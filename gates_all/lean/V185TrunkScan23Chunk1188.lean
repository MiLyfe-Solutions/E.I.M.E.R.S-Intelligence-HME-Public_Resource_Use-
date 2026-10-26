import V185TrunkScan23Chunk1187

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7038411 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 2, 3, 2]
def baseStart_7038411 : Nat := 118140960795 + 7038411 * 2 ^ 59
def prefixEnd_7038411 : Nat := 4983230072969 + 3 ^ 40 * 7038411 * 2
def baseEnd_7038411 : Nat := 3614087886892566918293443

theorem tailTrace_7038411 : CollatzResearch.WordTrace tailWord_7038411 prefixEnd_7038411 3614087886892566918293443 := by
  unfold tailWord_7038411
  simp only [CollatzResearch.WordTrace]
  refine ⟨256711938904046486742635087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171141292602697657828423391 256711938904046486742635087)
  ·
    refine ⟨385067908356069730113952631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256711938904046486742635087 385067908356069730113952631)
    ·
      refine ⟨577601862534104595170928947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385067908356069730113952631 577601862534104595170928947)
      ·
        refine ⟨866402793801156892756393421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577601862534104595170928947 866402793801156892756393421)
        ·
          refine ⟨324901047675433834783647533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 866402793801156892756393421 324901047675433834783647533)
          ·
            refine ⟨121837892878287688043867825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324901047675433834783647533 121837892878287688043867825)
            ·
              refine ⟨91378419658715766032900869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121837892878287688043867825 91378419658715766032900869)
              ·
                refine ⟨17133453686009206131168913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91378419658715766032900869 17133453686009206131168913)
                ·
                  refine ⟨12850090264506904598376685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17133453686009206131168913 12850090264506904598376685)
                  ·
                    refine ⟨4818783849190089224391257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12850090264506904598376685 4818783849190089224391257)
                    ·
                      refine ⟨3614087886892566918293443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818783849190089224391257 3614087886892566918293443)
                      ·
                        rfl

theorem cell23_7038411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 3, 2].length) (baseStart_7038411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038411 prefixEnd_7038411 := by exact prefixLift 7038411
  have htrace : WordTrace (prefixWord ++ tailWord_7038411) baseStart_7038411 baseEnd_7038411 := by
    simpa [prefixWord, tailWord_7038411, baseEnd_7038411] using wordTrace_append hprefix tailTrace_7038411
  have hstable : (prefixWord ++ tailWord_7038411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038411).length < 2 ^ (prefixWord ++ tailWord_7038411).sum := by decide
  have hdescent : baseEnd_7038411 < baseStart_7038411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038417 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 2, 10]
def baseStart_7038417 : Nat := 118140960795 + 7038417 * 2 ^ 59
def prefixEnd_7038417 : Nat := 4983230072969 + 3 ^ 40 * 7038417 * 2
def baseEnd_7038417 : Nat := 1204696989258831298272805

theorem tailTrace_7038417 : CollatzResearch.WordTrace tailWord_7038417 prefixEnd_7038417 1204696989258831298272805 := by
  unfold tailWord_7038417
  simp only [CollatzResearch.WordTrace]
  refine ⟨256712157742024749767353505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171141438494683166511569003 256712157742024749767353505)
  ·
    refine ⟨192534118306518562325515129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256712157742024749767353505 192534118306518562325515129)
    ·
      refine ⟨144400588729888921744136347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192534118306518562325515129 144400588729888921744136347)
      ·
        refine ⟨216600883094833382616204521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144400588729888921744136347 216600883094833382616204521)
        ·
          refine ⟨162450662321125036962153391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216600883094833382616204521 162450662321125036962153391)
          ·
            refine ⟨243675993481687555443230087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162450662321125036962153391 243675993481687555443230087)
            ·
              refine ⟨365513990222531333164845131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243675993481687555443230087 365513990222531333164845131)
              ·
                refine ⟨548270985333796999747267697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365513990222531333164845131 548270985333796999747267697)
                ·
                  refine ⟨411203239000347749810450773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548270985333796999747267697 411203239000347749810450773)
                  ·
                    refine ⟨1204696989258831298272805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 411203239000347749810450773 1204696989258831298272805)
                    ·
                      rfl

theorem cell23_7038417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_7038417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038417 prefixEnd_7038417 := by exact prefixLift 7038417
  have htrace : WordTrace (prefixWord ++ tailWord_7038417) baseStart_7038417 baseEnd_7038417 := by
    simpa [prefixWord, tailWord_7038417, baseEnd_7038417] using wordTrace_append hprefix tailTrace_7038417
  have hstable : (prefixWord ++ tailWord_7038417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038417).length < 2 ^ (prefixWord ++ tailWord_7038417).sum := by decide
  have hdescent : baseEnd_7038417 < baseStart_7038417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038424 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_7038424 : Nat := 118140960795 + 7038424 * 2 ^ 59
def prefixEnd_7038424 : Nat := 4983230072969 + 3 ^ 40 * 7038424 * 2
def baseEnd_7038424 : Nat := 3614094562141075367430883

theorem tailTrace_7038424 : CollatzResearch.WordTrace tailWord_7038424 prefixEnd_7038424 3614094562141075367430883 := by
  unfold tailWord_7038424
  simp only [CollatzResearch.WordTrace]
  refine ⟨128356206526499694981429163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171141608701999593308572217 128356206526499694981429163)
  ·
    refine ⟨192534309789749542472143745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128356206526499694981429163 192534309789749542472143745)
    ·
      refine ⟨144400732342312156854107809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192534309789749542472143745 144400732342312156854107809)
      ·
        refine ⟨108300549256734117640580857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144400732342312156854107809 108300549256734117640580857)
        ·
          refine ⟨81225411942550588230435643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108300549256734117640580857 81225411942550588230435643)
          ·
            refine ⟨121838117913825882345653465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81225411942550588230435643 121838117913825882345653465)
            ·
              refine ⟨91378588435369411759240099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121838117913825882345653465 91378588435369411759240099)
              ·
                refine ⟨137067882653054117638860149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91378588435369411759240099 137067882653054117638860149)
                ·
                  refine ⟨12850113998723823528643139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137067882653054117638860149 12850113998723823528643139)
                  ·
                    refine ⟨19275170998085735292964709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12850113998723823528643139 19275170998085735292964709)
                    ·
                      refine ⟨3614094562141075367430883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19275170998085735292964709 3614094562141075367430883)
                      ·
                        rfl

theorem cell23_7038424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_7038424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038424 prefixEnd_7038424 := by exact prefixLift 7038424
  have htrace : WordTrace (prefixWord ++ tailWord_7038424) baseStart_7038424 baseEnd_7038424 := by
    simpa [prefixWord, tailWord_7038424, baseEnd_7038424] using wordTrace_append hprefix tailTrace_7038424
  have hstable : (prefixWord ++ tailWord_7038424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038424).length < 2 ^ (prefixWord ++ tailWord_7038424).sum := by decide
  have hdescent : baseEnd_7038424 < baseStart_7038424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038461 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_7038461 : Nat := 118140960795 + 7038461 * 2 ^ 59
def prefixEnd_7038461 : Nat := 4983230072969 + 3 ^ 40 * 7038461 * 2
def baseEnd_7038461 : Nat := 3614113560925291722668213

theorem tailTrace_7038461 : CollatzResearch.WordTrace tailWord_7038461 prefixEnd_7038461 3614113560925291722668213 := by
  unfold tailWord_7038461
  simp only [CollatzResearch.WordTrace]
  refine ⟨256713762553865345281955237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171142508369243563521303491 256713762553865345281955237)
  ·
    refine ⟨48133830478849752240366607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256713762553865345281955237 48133830478849752240366607)
    ·
      refine ⟨72200745718274628360549911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48133830478849752240366607 72200745718274628360549911)
      ·
        refine ⟨108301118577411942540824867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72200745718274628360549911 108301118577411942540824867)
        ·
          refine ⟨162451677866117913811237301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108301118577411942540824867 162451677866117913811237301)
          ·
            refine ⟨15229844799948554419803497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162451677866117913811237301 15229844799948554419803497)
            ·
              refine ⟨11422383599961415814852623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15229844799948554419803497 11422383599961415814852623)
              ·
                refine ⟨17133575399942123722278935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11422383599961415814852623 17133575399942123722278935)
                ·
                  refine ⟨25700363099913185583418403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17133575399942123722278935 25700363099913185583418403)
                  ·
                    refine ⟨38550544649869778375127605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25700363099913185583418403 38550544649869778375127605)
                    ·
                      refine ⟨3614113560925291722668213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38550544649869778375127605 3614113560925291722668213)
                      ·
                        rfl

theorem cell23_7038461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_7038461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038461 prefixEnd_7038461 := by exact prefixLift 7038461
  have htrace : WordTrace (prefixWord ++ tailWord_7038461) baseStart_7038461 baseEnd_7038461 := by
    simpa [prefixWord, tailWord_7038461, baseEnd_7038461] using wordTrace_append hprefix tailTrace_7038461
  have hstable : (prefixWord ++ tailWord_7038461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038461).length < 2 ^ (prefixWord ++ tailWord_7038461).sum := by decide
  have hdescent : baseEnd_7038461 < baseStart_7038461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038462 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7038462 : Nat := 118140960795 + 7038462 * 2 ^ 59
def prefixEnd_7038462 : Nat := 4983230072969 + 3 ^ 40 * 7038462 * 2
def baseEnd_7038462 : Nat := 3614114074405946218755709

theorem tailTrace_7038462 : CollatzResearch.WordTrace tailWord_7038462 prefixEnd_7038462 3614114074405946218755709 := by
  unfold tailWord_7038462
  simp only [CollatzResearch.WordTrace]
  refine ⟨32089224878357715306592705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171142532684574481635161093 32089224878357715306592705)
  ·
    refine ⟨24066918658768286479944529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32089224878357715306592705 24066918658768286479944529)
    ·
      refine ⟨18050188994076214859958397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24066918658768286479944529 18050188994076214859958397)
      ·
        refine ⟨6768820872778580572484399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18050188994076214859958397 6768820872778580572484399)
        ·
          refine ⟨10153231309167870858726599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6768820872778580572484399 10153231309167870858726599)
          ·
            refine ⟨15229846963751806288089899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153231309167870858726599 15229846963751806288089899)
            ·
              refine ⟨22844770445627709432134849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15229846963751806288089899 22844770445627709432134849)
              ·
                refine ⟨17133577834220782074101137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22844770445627709432134849 17133577834220782074101137)
                ·
                  refine ⟨12850183375665586555575853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17133577834220782074101137 12850183375665586555575853)
                  ·
                    refine ⟨4818818765874594958340945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12850183375665586555575853 4818818765874594958340945)
                    ·
                      refine ⟨3614114074405946218755709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818818765874594958340945 3614114074405946218755709)
                      ·
                        rfl

theorem cell23_7038462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7038462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038462 prefixEnd_7038462 := by exact prefixLift 7038462
  have htrace : WordTrace (prefixWord ++ tailWord_7038462) baseStart_7038462 baseEnd_7038462 := by
    simpa [prefixWord, tailWord_7038462, baseEnd_7038462] using wordTrace_append hprefix tailTrace_7038462
  have hstable : (prefixWord ++ tailWord_7038462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038462).length < 2 ^ (prefixWord ++ tailWord_7038462).sum := by decide
  have hdescent : baseEnd_7038462 < baseStart_7038462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038485 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 2, 4]
def baseStart_7038485 : Nat := 118140960795 + 7038485 * 2 ^ 59
def prefixEnd_7038485 : Nat := 4983230072969 + 3 ^ 40 * 7038485 * 2
def baseEnd_7038485 : Nat := 1204708628153666542922701

theorem tailTrace_7038485 : CollatzResearch.WordTrace tailWord_7038485 prefixEnd_7038485 1204708628153666542922701 := by
  unfold tailWord_7038485
  simp only [CollatzResearch.WordTrace]
  refine ⟨256714637905778397380828909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171143091937185598253885939 256714637905778397380828909)
  ·
    refine ⟨96267989214666899017810841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256714637905778397380828909 96267989214666899017810841)
    ·
      refine ⟨72200991911000174263358131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96267989214666899017810841 72200991911000174263358131)
      ·
        refine ⟨108301487866500261395037197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72200991911000174263358131 108301487866500261395037197)
        ·
          refine ⟨40613057949937598023138949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108301487866500261395037197 40613057949937598023138949)
          ·
            refine ⟨7614948365613299629338553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40613057949937598023138949 7614948365613299629338553)
            ·
              refine ⟨5711211274209974722003915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7614948365613299629338553 5711211274209974722003915)
              ·
                refine ⟨8566816911314962083005873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5711211274209974722003915 8566816911314962083005873)
                ·
                  refine ⟨6425112683486221562254405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8566816911314962083005873 6425112683486221562254405)
                  ·
                    refine ⟨1204708628153666542922701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6425112683486221562254405 1204708628153666542922701)
                    ·
                      rfl

theorem cell23_7038485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_7038485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038485 prefixEnd_7038485 := by exact prefixLift 7038485
  have htrace : WordTrace (prefixWord ++ tailWord_7038485) baseStart_7038485 baseEnd_7038485 := by
    simpa [prefixWord, tailWord_7038485, baseEnd_7038485] using wordTrace_append hprefix tailTrace_7038485
  have hstable : (prefixWord ++ tailWord_7038485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038485).length < 2 ^ (prefixWord ++ tailWord_7038485).sum := by decide
  have hdescent : baseEnd_7038485 < baseStart_7038485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038582 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_7038582 : Nat := 118140960795 + 7038582 * 2 ^ 59
def prefixEnd_7038582 : Nat := 4983230072969 + 3 ^ 40 * 7038582 * 2
def baseEnd_7038582 : Nat := 3614175692084485749255157

theorem tailTrace_7038582 : CollatzResearch.WordTrace tailWord_7038582 prefixEnd_7038582 3614175692084485749255157 := by
  unfold tailWord_7038582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16044885986651686434194375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171145450524284655298073333 16044885986651686434194375)
  ·
    refine ⟨24067328979977529651291563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16044885986651686434194375 24067328979977529651291563)
    ·
      refine ⟨36100993469966294476937345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24067328979977529651291563 36100993469966294476937345)
      ·
        refine ⟨27075745102474720857703009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36100993469966294476937345 27075745102474720857703009)
        ·
          refine ⟨20306808826856040643277257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27075745102474720857703009 20306808826856040643277257)
          ·
            refine ⟨15230106620142030482457943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20306808826856040643277257 15230106620142030482457943)
            ·
              refine ⟨22845159930213045723686915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15230106620142030482457943 22845159930213045723686915)
              ·
                refine ⟨34267739895319568585530373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22845159930213045723686915 34267739895319568585530373)
                ·
                  refine ⟨6425201230372419109786945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34267739895319568585530373 6425201230372419109786945)
                  ·
                    refine ⟨4818900922779314332340209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6425201230372419109786945 4818900922779314332340209)
                    ·
                      refine ⟨3614175692084485749255157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818900922779314332340209 3614175692084485749255157)
                      ·
                        rfl

theorem cell23_7038582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_7038582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038582 prefixEnd_7038582 := by exact prefixLift 7038582
  have htrace : WordTrace (prefixWord ++ tailWord_7038582) baseStart_7038582 baseEnd_7038582 := by
    simpa [prefixWord, tailWord_7038582, baseEnd_7038582] using wordTrace_append hprefix tailTrace_7038582
  have hstable : (prefixWord ++ tailWord_7038582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038582).length < 2 ^ (prefixWord ++ tailWord_7038582).sum := by decide
  have hdescent : baseEnd_7038582 < baseStart_7038582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038584 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 5, 7]
def baseStart_7038584 : Nat := 118140960795 + 7038584 * 2 ^ 59
def prefixEnd_7038584 : Nat := 4983230072969 + 3 ^ 40 * 7038584 * 2
def baseEnd_7038584 : Nat := 1204725573015264913810049

theorem tailTrace_7038584 : CollatzResearch.WordTrace tailWord_7038584 prefixEnd_7038584 1204725573015264913810049 := by
  unfold tailWord_7038584
  simp only [CollatzResearch.WordTrace]
  refine ⟨128359124366209868644341403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171145499154946491525788537 128359124366209868644341403)
  ·
    refine ⟨192538686549314802966512105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128359124366209868644341403 192538686549314802966512105)
    ·
      refine ⟨144404014911986102224884079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192538686549314802966512105 144404014911986102224884079)
      ·
        refine ⟨216606022367979153337326119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144404014911986102224884079 216606022367979153337326119)
        ·
          refine ⟨324909033551968730005989179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216606022367979153337326119 324909033551968730005989179)
          ·
            refine ⟨487363550327953095008983769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324909033551968730005989179 487363550327953095008983769)
            ·
              refine ⟨365522662745964821256737827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487363550327953095008983769 365522662745964821256737827)
              ·
                refine ⟨548283994118947231885106741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365522662745964821256737827 548283994118947231885106741)
                ·
                  refine ⟨51401624448651302989228757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 548283994118947231885106741 51401624448651302989228757)
                  ·
                    refine ⟨1204725573015264913810049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51401624448651302989228757 1204725573015264913810049)
                    ·
                      rfl

theorem cell23_7038584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_7038584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038584 prefixEnd_7038584 := by exact prefixLift 7038584
  have htrace : WordTrace (prefixWord ++ tailWord_7038584) baseStart_7038584 baseEnd_7038584 := by
    simpa [prefixWord, tailWord_7038584, baseEnd_7038584] using wordTrace_append hprefix tailTrace_7038584
  have hstable : (prefixWord ++ tailWord_7038584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038584).length < 2 ^ (prefixWord ++ tailWord_7038584).sum := by decide
  have hdescent : baseEnd_7038584 < baseStart_7038584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038622 : List Nat := [4, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_7038622 : Nat := 118140960795 + 7038622 * 2 ^ 59
def prefixEnd_7038622 : Nat := 4983230072969 + 3 ^ 40 * 7038622 * 2
def baseEnd_7038622 : Nat := 401577359034518399194997

theorem tailTrace_7038622 : CollatzResearch.WordTrace tailWord_7038622 prefixEnd_7038622 401577359034518399194997 := by
  unfold tailWord_7038622
  simp only [CollatzResearch.WordTrace]
  refine ⟨32089954338285258722320765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171146423137521379852377413 32089954338285258722320765)
  ·
    refine ⟨12033732876856972020870287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32089954338285258722320765 12033732876856972020870287)
    ·
      refine ⟨18050599315285458031305431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12033732876856972020870287 18050599315285458031305431)
      ·
        refine ⟨27075898972928187046958147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18050599315285458031305431 27075898972928187046958147)
        ·
          refine ⟨40613848459392280570437221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27075898972928187046958147 40613848459392280570437221)
          ·
            refine ⟨7615096586136052606956979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40613848459392280570437221 7615096586136052606956979)
            ·
              refine ⟨11422644879204078910435469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7615096586136052606956979 11422644879204078910435469)
              ·
                refine ⟨4283491829701529591413301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11422644879204078910435469 4283491829701529591413301)
                ·
                  refine ⟨401577359034518399194997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4283491829701529591413301 401577359034518399194997)
                  ·
                    rfl

theorem cell23_7038622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_7038622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038622 prefixEnd_7038622 := by exact prefixLift 7038622
  have htrace : WordTrace (prefixWord ++ tailWord_7038622) baseStart_7038622 baseEnd_7038622 := by
    simpa [prefixWord, tailWord_7038622, baseEnd_7038622] using wordTrace_append hprefix tailTrace_7038622
  have hstable : (prefixWord ++ tailWord_7038622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038622).length < 2 ^ (prefixWord ++ tailWord_7038622).sum := by decide
  have hdescent : baseEnd_7038622 < baseStart_7038622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038661 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 6]
def baseStart_7038661 : Nat := 118140960795 + 7038661 * 2 ^ 59
def prefixEnd_7038661 : Nat := 4983230072969 + 3 ^ 40 * 7038661 * 2
def baseEnd_7038661 : Nat := 401579584117354548907477

theorem tailTrace_7038661 : CollatzResearch.WordTrace tailWord_7038661 prefixEnd_7038661 401579584117354548907477 := by
  unfold tailWord_7038661
  simp only [CollatzResearch.WordTrace]
  refine ⟨256721057153140779439235837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171147371435427186292823891 256721057153140779439235837)
  ·
    refine ⟨96270396432427792289713439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256721057153140779439235837 96270396432427792289713439)
    ·
      refine ⟨144405594648641688434570159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96270396432427792289713439 144405594648641688434570159)
      ·
        refine ⟨216608391972962532651855239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144405594648641688434570159 216608391972962532651855239)
        ·
          refine ⟨324912587959443798977782859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216608391972962532651855239 324912587959443798977782859)
          ·
            refine ⟨487368881939165698466674289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324912587959443798977782859 487368881939165698466674289)
            ·
              refine ⟨365526661454374273850005717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487368881939165698466674289 365526661454374273850005717)
              ·
                refine ⟨8567031127836897043359509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 365526661454374273850005717 8567031127836897043359509)
                ·
                  refine ⟨401579584117354548907477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8567031127836897043359509 401579584117354548907477)
                  ·
                    rfl

theorem cell23_7038661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_7038661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038661 prefixEnd_7038661 := by exact prefixLift 7038661
  have htrace : WordTrace (prefixWord ++ tailWord_7038661) baseStart_7038661 baseEnd_7038661 := by
    simpa [prefixWord, tailWord_7038661, baseEnd_7038661] using wordTrace_append hprefix tailTrace_7038661
  have hstable : (prefixWord ++ tailWord_7038661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038661).length < 2 ^ (prefixWord ++ tailWord_7038661).sum := by decide
  have hdescent : baseEnd_7038661 < baseStart_7038661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038671 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 3]
def baseStart_7038671 : Nat := 118140960795 + 7038671 * 2 ^ 59
def prefixEnd_7038671 : Nat := 4983230072969 + 3 ^ 40 * 7038671 * 2
def baseEnd_7038671 : Nat := 3614221391862735901042247

theorem tailTrace_7038671 : CollatzResearch.WordTrace tailWord_7038671 prefixEnd_7038671 3614221391862735901042247 := by
  unfold tailWord_7038671
  simp only [CollatzResearch.WordTrace]
  refine ⟨256721421883104551147099867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171147614588736367431399911 256721421883104551147099867)
  ·
    refine ⟨385082132824656826720649801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256721421883104551147099867 385082132824656826720649801)
    ·
      refine ⟨288811599618492620040487351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385082132824656826720649801 288811599618492620040487351)
      ·
        refine ⟨433217399427738930060731027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288811599618492620040487351 433217399427738930060731027)
        ·
          refine ⟨649826099141608395091096541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433217399427738930060731027 649826099141608395091096541)
          ·
            refine ⟨243684787178103148159161203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 649826099141608395091096541 243684787178103148159161203)
            ·
              refine ⟨365527180767154722238741805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243684787178103148159161203 365527180767154722238741805)
              ·
                refine ⟨137072692787683020839528177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365527180767154722238741805 137072692787683020839528177)
                ·
                  refine ⟨102804519590762265629646133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137072692787683020839528177 102804519590762265629646133)
                  ·
                    refine ⟨9637923711633962402779325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102804519590762265629646133 9637923711633962402779325)
                    ·
                      refine ⟨3614221391862735901042247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9637923711633962402779325 3614221391862735901042247)
                      ·
                        rfl

theorem cell23_7038671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 3].length) (baseStart_7038671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038671 prefixEnd_7038671 := by exact prefixLift 7038671
  have htrace : WordTrace (prefixWord ++ tailWord_7038671) baseStart_7038671 baseEnd_7038671 := by
    simpa [prefixWord, tailWord_7038671, baseEnd_7038671] using wordTrace_append hprefix tailTrace_7038671
  have hstable : (prefixWord ++ tailWord_7038671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038671).length < 2 ^ (prefixWord ++ tailWord_7038671).sum := by decide
  have hdescent : baseEnd_7038671 < baseStart_7038671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038722 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_7038722 : Nat := 118140960795 + 7038722 * 2 ^ 59
def prefixEnd_7038722 : Nat := 4983230072969 + 3 ^ 40 * 7038722 * 2
def baseEnd_7038722 : Nat := 3614247579376115201504513

theorem tailTrace_7038722 : CollatzResearch.WordTrace tailWord_7038722 prefixEnd_7038722 3614247579376115201504513 := by
  unfold tailWord_7038722
  simp only [CollatzResearch.WordTrace]
  refine ⟨64180820501479946714301605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171148854670613191238137613 64180820501479946714301605)
  ·
    refine ⟨12033903844027490008931551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64180820501479946714301605 12033903844027490008931551)
    ·
      refine ⟨18050855766041235013397327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12033903844027490008931551 18050855766041235013397327)
      ·
        refine ⟨27076283649061852520095991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18050855766041235013397327 27076283649061852520095991)
        ·
          refine ⟨40614425473592778780143987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27076283649061852520095991 40614425473592778780143987)
          ·
            refine ⟨60921638210389168170215981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40614425473592778780143987 60921638210389168170215981)
            ·
              refine ⟨22845614328895938063830993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60921638210389168170215981 22845614328895938063830993)
              ·
                refine ⟨17134210746671953547873245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22845614328895938063830993 17134210746671953547873245)
                ·
                  refine ⟨6425329030001982580452467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17134210746671953547873245 6425329030001982580452467)
                  ·
                    refine ⟨9637993545002973870678701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6425329030001982580452467 9637993545002973870678701)
                    ·
                      refine ⟨3614247579376115201504513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9637993545002973870678701 3614247579376115201504513)
                      ·
                        rfl

theorem cell23_7038722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_7038722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038722 prefixEnd_7038722 := by exact prefixLift 7038722
  have htrace : WordTrace (prefixWord ++ tailWord_7038722) baseStart_7038722 baseEnd_7038722 := by
    simpa [prefixWord, tailWord_7038722, baseEnd_7038722] using wordTrace_append hprefix tailTrace_7038722
  have hstable : (prefixWord ++ tailWord_7038722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038722).length < 2 ^ (prefixWord ++ tailWord_7038722).sum := by decide
  have hdescent : baseEnd_7038722 < baseStart_7038722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038728 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_7038728 : Nat := 118140960795 + 7038728 * 2 ^ 59
def prefixEnd_7038728 : Nat := 4983230072969 + 3 ^ 40 * 7038728 * 2
def baseEnd_7038728 : Nat := 3614250660260042178029485

theorem tailTrace_7038728 : CollatzResearch.WordTrace tailWord_7038728 prefixEnd_7038728 3614250660260042178029485 := by
  unfold tailWord_7038728
  simp only [CollatzResearch.WordTrace]
  refine ⟨128361750421949024940962419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171149000562598699921283225 128361750421949024940962419)
  ·
    refine ⟨192542625632923537411443629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128361750421949024940962419 192542625632923537411443629)
    ·
      refine ⟨72203484612346326529291361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192542625632923537411443629 72203484612346326529291361)
      ·
        refine ⟨54152613459259744896968521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72203484612346326529291361 54152613459259744896968521)
        ·
          refine ⟨40614460094444808672726391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54152613459259744896968521 40614460094444808672726391)
          ·
            refine ⟨60921690141667213009089587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40614460094444808672726391 60921690141667213009089587)
            ·
              refine ⟨91382535212500819513634381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60921690141667213009089587 91382535212500819513634381)
              ·
                refine ⟨34268450704687807317612893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91382535212500819513634381 34268450704687807317612893)
                ·
                  refine ⟨12850669014257927744104835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34268450704687807317612893 12850669014257927744104835)
                  ·
                    refine ⟨19276003521386891616157253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12850669014257927744104835 19276003521386891616157253)
                    ·
                      refine ⟨3614250660260042178029485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19276003521386891616157253 3614250660260042178029485)
                      ·
                        rfl

theorem cell23_7038728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_7038728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038728 prefixEnd_7038728 := by exact prefixLift 7038728
  have htrace : WordTrace (prefixWord ++ tailWord_7038728) baseStart_7038728 baseEnd_7038728 := by
    simpa [prefixWord, tailWord_7038728, baseEnd_7038728] using wordTrace_append hprefix tailTrace_7038728
  have hstable : (prefixWord ++ tailWord_7038728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038728).length < 2 ^ (prefixWord ++ tailWord_7038728).sum := by decide
  have hdescent : baseEnd_7038728 < baseStart_7038728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038748 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_7038748 : Nat := 118140960795 + 7038748 * 2 ^ 59
def prefixEnd_7038748 : Nat := 4983230072969 + 3 ^ 40 * 7038748 * 2
def baseEnd_7038748 : Nat := 3614260929873132099779393

theorem tailTrace_7038748 : CollatzResearch.WordTrace tailWord_7038748 prefixEnd_7038748 3614260929873132099779393 := by
  unfold tailWord_7038748
  simp only [CollatzResearch.WordTrace]
  refine ⟨128362115151912796648826449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171149486869217062198435265 128362115151912796648826449)
  ·
    refine ⟨96271586363934597486619837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128362115151912796648826449 96271586363934597486619837)
    ·
      refine ⟨36101844886475474057482439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96271586363934597486619837 36101844886475474057482439)
      ·
        refine ⟨54152767329713211086223659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36101844886475474057482439 54152767329713211086223659)
        ·
          refine ⟨81229150994569816629335489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54152767329713211086223659 81229150994569816629335489)
          ·
            refine ⟨60921863245927362472001617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81229150994569816629335489 60921863245927362472001617)
            ·
              refine ⟨45691397434445521854001213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60921863245927362472001617 45691397434445521854001213)
              ·
                refine ⟨17134274037917070695250455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45691397434445521854001213 17134274037917070695250455)
                ·
                  refine ⟨25701411056875606042875683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17134274037917070695250455 25701411056875606042875683)
                  ·
                    refine ⟨38552116585313409064313525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25701411056875606042875683 38552116585313409064313525)
                    ·
                      refine ⟨3614260929873132099779393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38552116585313409064313525 3614260929873132099779393)
                      ·
                        rfl

theorem cell23_7038748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_7038748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038748 prefixEnd_7038748 := by exact prefixLift 7038748
  have htrace : WordTrace (prefixWord ++ tailWord_7038748) baseStart_7038748 baseEnd_7038748 := by
    simpa [prefixWord, tailWord_7038748, baseEnd_7038748] using wordTrace_append hprefix tailTrace_7038748
  have hstable : (prefixWord ++ tailWord_7038748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038748).length < 2 ^ (prefixWord ++ tailWord_7038748).sum := by decide
  have hdescent : baseEnd_7038748 < baseStart_7038748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038751 : List Nat := [1, 1, 2, 4, 2, 1, 12]
def baseStart_7038751 : Nat := 118140960795 + 7038751 * 2 ^ 59
def prefixEnd_7038751 : Nat := 4983230072969 + 3 ^ 40 * 7038751 * 2
def baseEnd_7038751 : Nat := 44620524324877723309159

theorem tailTrace_7038751 : CollatzResearch.WordTrace tailWord_7038751 prefixEnd_7038751 44620524324877723309159 := by
  unfold tailWord_7038751
  simp only [CollatzResearch.WordTrace]
  refine ⟨256724339722814724810012107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171149559815209816540008071 256724339722814724810012107)
  ·
    refine ⟨385086509584222087215018161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256724339722814724810012107 385086509584222087215018161)
    ·
      refine ⟨288814882188166565411263621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385086509584222087215018161 288814882188166565411263621)
      ·
        refine ⟨54152790410281231014611929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288814882188166565411263621 54152790410281231014611929)
        ·
          refine ⟨40614592807710923260958947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54152790410281231014611929 40614592807710923260958947)
          ·
            refine ⟨60921889211566384891438421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40614592807710923260958947 60921889211566384891438421)
            ·
              refine ⟨44620524324877723309159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 60921889211566384891438421 44620524324877723309159)
              ·
                rfl

theorem cell23_7038751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 12].length) (baseStart_7038751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038751 prefixEnd_7038751 := by exact prefixLift 7038751
  have htrace : WordTrace (prefixWord ++ tailWord_7038751) baseStart_7038751 baseEnd_7038751 := by
    simpa [prefixWord, tailWord_7038751, baseEnd_7038751] using wordTrace_append hprefix tailTrace_7038751
  have hstable : (prefixWord ++ tailWord_7038751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038751).length < 2 ^ (prefixWord ++ tailWord_7038751).sum := by decide
  have hdescent : baseEnd_7038751 < baseStart_7038751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038755 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 2, 4]
def baseStart_7038755 : Nat := 118140960795 + 7038755 * 2 ^ 59
def prefixEnd_7038755 : Nat := 4983230072969 + 3 ^ 40 * 7038755 * 2
def baseEnd_7038755 : Nat := 1204754841412571190797287

theorem tailTrace_7038755 : CollatzResearch.WordTrace tailWord_7038755 prefixEnd_7038755 1204754841412571190797287 := by
  unfold tailWord_7038755
  simp only [CollatzResearch.WordTrace]
  refine ⟨256724485614800233493157719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171149657076533488995438479 256724485614800233493157719)
  ·
    refine ⟨385086728422200350239736579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256724485614800233493157719 385086728422200350239736579)
    ·
      refine ⟨577630092633300525359604869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385086728422200350239736579 577630092633300525359604869)
      ·
        refine ⟨108305642368743848504925913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 577630092633300525359604869 108305642368743848504925913)
        ·
          refine ⟨81229231776557886378694435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108305642368743848504925913 81229231776557886378694435)
          ·
            refine ⟨121843847664836829568041653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81229231776557886378694435 121843847664836829568041653)
            ·
              refine ⟨11422860718578452772003905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121843847664836829568041653 11422860718578452772003905)
              ·
                refine ⟨8567145538933839579002929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11422860718578452772003905 8567145538933839579002929)
                ·
                  refine ⟨6425359154200379684252197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8567145538933839579002929 6425359154200379684252197)
                  ·
                    refine ⟨1204754841412571190797287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6425359154200379684252197 1204754841412571190797287)
                    ·
                      rfl

theorem cell23_7038755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 4].length) (baseStart_7038755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038755 prefixEnd_7038755 := by exact prefixLift 7038755
  have htrace : WordTrace (prefixWord ++ tailWord_7038755) baseStart_7038755 baseEnd_7038755 := by
    simpa [prefixWord, tailWord_7038755, baseEnd_7038755] using wordTrace_append hprefix tailTrace_7038755
  have hstable : (prefixWord ++ tailWord_7038755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038755).length < 2 ^ (prefixWord ++ tailWord_7038755).sum := by decide
  have hdescent : baseEnd_7038755 < baseStart_7038755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038772 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_7038772 : Nat := 118140960795 + 7038772 * 2 ^ 59
def prefixEnd_7038772 : Nat := 4983230072969 + 3 ^ 40 * 7038772 * 2
def baseEnd_7038772 : Nat := 1204757751136280001959761

theorem tailTrace_7038772 : CollatzResearch.WordTrace tailWord_7038772 prefixEnd_7038772 1204757751136280001959761 := by
  unfold tailWord_7038772
  simp only [CollatzResearch.WordTrace]
  refine ⟨128362552827869322698263285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171150070437159096931017713 128362552827869322698263285)
  ·
    refine ⟨12033989327612749002962183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128362552827869322698263285 12033989327612749002962183)
    ·
      refine ⟨18050983991419123504443275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12033989327612749002962183 18050983991419123504443275)
      ·
        refine ⟨27076475987128685256664913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18050983991419123504443275 27076475987128685256664913)
        ·
          refine ⟨20307356990346513942498685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27076475987128685256664913 20307356990346513942498685)
          ·
            refine ⟨7615258871379942728437007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20307356990346513942498685 7615258871379942728437007)
            ·
              refine ⟨11422888307069914092655511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7615258871379942728437007 11422888307069914092655511)
              ·
                refine ⟨17134332460604871138983267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11422888307069914092655511 17134332460604871138983267)
                ·
                  refine ⟨25701498690907306708474901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17134332460604871138983267 25701498690907306708474901)
                  ·
                    refine ⟨1204757751136280001959761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25701498690907306708474901 1204757751136280001959761)
                    ·
                      rfl

theorem cell23_7038772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_7038772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038772 prefixEnd_7038772 := by exact prefixLift 7038772
  have htrace : WordTrace (prefixWord ++ tailWord_7038772) baseStart_7038772 baseEnd_7038772 := by
    simpa [prefixWord, tailWord_7038772, baseEnd_7038772] using wordTrace_append hprefix tailTrace_7038772
  have hstable : (prefixWord ++ tailWord_7038772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038772).length < 2 ^ (prefixWord ++ tailWord_7038772).sum := by decide
  have hdescent : baseEnd_7038772 < baseStart_7038772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038782 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_7038782 : Nat := 118140960795 + 7038782 * 2 ^ 59
def prefixEnd_7038782 : Nat := 4983230072969 + 3 ^ 40 * 7038782 * 2
def baseEnd_7038782 : Nat := 3614278388215384966754237

theorem tailTrace_7038782 : CollatzResearch.WordTrace tailWord_7038782 prefixEnd_7038782 3614278388215384966754237 := by
  unfold tailWord_7038782
  simp only [CollatzResearch.WordTrace]
  refine ⟨32090683798212802138048825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171150313590468278069593733 32090683798212802138048825)
  ·
    refine ⟨24068012848659601603536619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32090683798212802138048825 24068012848659601603536619)
    ·
      refine ⟨36102019272989402405304929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24068012848659601603536619 36102019272989402405304929)
      ·
        refine ⟨27076514454742051803978697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36102019272989402405304929 27076514454742051803978697)
        ·
          refine ⟨20307385841056538852984023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27076514454742051803978697 20307385841056538852984023)
          ·
            refine ⟨30461078761584808279476035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20307385841056538852984023 30461078761584808279476035)
            ·
              refine ⟨45691618142377212419214053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30461078761584808279476035 45691618142377212419214053)
              ·
                refine ⟨8567178401695727328602635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45691618142377212419214053 8567178401695727328602635)
                ·
                  refine ⟨12850767602543590992903953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8567178401695727328602635 12850767602543590992903953)
                  ·
                    refine ⟨9638075701907693244677965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12850767602543590992903953 9638075701907693244677965)
                    ·
                      refine ⟨3614278388215384966754237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9638075701907693244677965 3614278388215384966754237)
                      ·
                        rfl

theorem cell23_7038782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_7038782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038782 prefixEnd_7038782 := by exact prefixLift 7038782
  have htrace : WordTrace (prefixWord ++ tailWord_7038782) baseStart_7038782 baseEnd_7038782 := by
    simpa [prefixWord, tailWord_7038782, baseEnd_7038782] using wordTrace_append hprefix tailTrace_7038782
  have hstable : (prefixWord ++ tailWord_7038782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038782).length < 2 ^ (prefixWord ++ tailWord_7038782).sum := by decide
  have hdescent : baseEnd_7038782 < baseStart_7038782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038829 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_7038829 : Nat := 118140960795 + 7038829 * 2 ^ 59
def prefixEnd_7038829 : Nat := 4983230072969 + 3 ^ 40 * 7038829 * 2
def baseEnd_7038829 : Nat := 3614302521806146282866521

theorem tailTrace_7038829 : CollatzResearch.WordTrace tailWord_7038829 prefixEnd_7038829 3614302521806146282866521 := by
  unfold tailWord_7038829
  simp only [CollatzResearch.WordTrace]
  refine ⟨256727184616532144131351541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171151456411021429420901027 256727184616532144131351541)
  ·
    refine ⟨24068173557799888512314207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256727184616532144131351541 24068173557799888512314207)
    ·
      refine ⟨36102260336699832768471311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24068173557799888512314207 36102260336699832768471311)
      ·
        refine ⟨54153390505049749152706967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36102260336699832768471311 54153390505049749152706967)
        ·
          refine ⟨81230085757574623729060451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54153390505049749152706967 81230085757574623729060451)
          ·
            refine ⟨121845128636361935593590677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81230085757574623729060451 121845128636361935593590677)
            ·
              refine ⟨5711490404829465730949563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121845128636361935593590677 5711490404829465730949563)
              ·
                refine ⟨8567235607244198596424345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5711490404829465730949563 8567235607244198596424345)
                ·
                  refine ⟨6425426705433148947318259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8567235607244198596424345 6425426705433148947318259)
                  ·
                    refine ⟨9638140058149723420977389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6425426705433148947318259 9638140058149723420977389)
                    ·
                      refine ⟨3614302521806146282866521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9638140058149723420977389 3614302521806146282866521)
                      ·
                        rfl

theorem cell23_7038829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_7038829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038829 prefixEnd_7038829 := by exact prefixLift 7038829
  have htrace : WordTrace (prefixWord ++ tailWord_7038829) baseStart_7038829 baseEnd_7038829 := by
    simpa [prefixWord, tailWord_7038829, baseEnd_7038829] using wordTrace_append hprefix tailTrace_7038829
  have hstable : (prefixWord ++ tailWord_7038829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038829).length < 2 ^ (prefixWord ++ tailWord_7038829).sum := by decide
  have hdescent : baseEnd_7038829 < baseStart_7038829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038835 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 1, 4, 2]
def baseStart_7038835 : Nat := 118140960795 + 7038835 * 2 ^ 59
def prefixEnd_7038835 : Nat := 4983230072969 + 3 ^ 40 * 7038835 * 2
def baseEnd_7038835 : Nat := 3614305602690073259391493

theorem tailTrace_7038835 : CollatzResearch.WordTrace tailWord_7038835 prefixEnd_7038835 3614305602690073259391493 := by
  unfold tailWord_7038835
  simp only [CollatzResearch.WordTrace]
  refine ⟨256727403454510407156069959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171151602303006938104046639 256727403454510407156069959)
  ·
    refine ⟨385091105181765610734104939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256727403454510407156069959 385091105181765610734104939)
    ·
      refine ⟨577636657772648416101157409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385091105181765610734104939 577636657772648416101157409)
      ·
        refine ⟨433227493329486312075868057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577636657772648416101157409 433227493329486312075868057)
        ·
          refine ⟨324920619997114734056901043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433227493329486312075868057 324920619997114734056901043)
          ·
            refine ⟨487380929995672101085351565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324920619997114734056901043 487380929995672101085351565)
            ·
              refine ⟨182767848748377037907006837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 487380929995672101085351565 182767848748377037907006837)
              ·
                refine ⟨17134485820160347303781891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182767848748377037907006837 17134485820160347303781891)
                ·
                  refine ⟨25701728730240520955672837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17134485820160347303781891 25701728730240520955672837)
                  ·
                    refine ⟨4819074136920097679188657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25701728730240520955672837 4819074136920097679188657)
                    ·
                      refine ⟨3614305602690073259391493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819074136920097679188657 3614305602690073259391493)
                      ·
                        rfl

theorem cell23_7038835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 4, 2].length) (baseStart_7038835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038835 prefixEnd_7038835 := by exact prefixLift 7038835
  have htrace : WordTrace (prefixWord ++ tailWord_7038835) baseStart_7038835 baseEnd_7038835 := by
    simpa [prefixWord, tailWord_7038835, baseEnd_7038835] using wordTrace_append hprefix tailTrace_7038835
  have hstable : (prefixWord ++ tailWord_7038835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038835).length < 2 ^ (prefixWord ++ tailWord_7038835).sum := by decide
  have hdescent : baseEnd_7038835 < baseStart_7038835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038852 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_7038852 : Nat := 118140960795 + 7038852 * 2 ^ 59
def prefixEnd_7038852 : Nat := 4983230072969 + 3 ^ 40 * 7038852 * 2
def baseEnd_7038852 : Nat := 3614314331861199692878915

theorem tailTrace_7038852 : CollatzResearch.WordTrace tailWord_7038852 prefixEnd_7038852 3614314331861199692878915 := by
  unfold tailWord_7038852
  simp only [CollatzResearch.WordTrace]
  refine ⟨128364011747724409529719405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171152015663632546039625873 128364011747724409529719405)
  ·
    refine ⟨48136504405396653573644777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128364011747724409529719405 48136504405396653573644777)
    ·
      refine ⟨36102378304047490180233583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48136504405396653573644777 36102378304047490180233583)
      ·
        refine ⟨54153567456071235270350375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36102378304047490180233583 54153567456071235270350375)
        ·
          refine ⟨81230351184106852905525563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54153567456071235270350375 81230351184106852905525563)
          ·
            refine ⟨121845526776160279358288345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81230351184106852905525563 121845526776160279358288345)
            ·
              refine ⟨91384145082120209518716259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121845526776160279358288345 91384145082120209518716259)
              ·
                refine ⟨137076217623180314278074389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91384145082120209518716259 137076217623180314278074389)
                ·
                  refine ⟨6425447701086577231784737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137076217623180314278074389 6425447701086577231784737)
                  ·
                    refine ⟨4819085775814932923838553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6425447701086577231784737 4819085775814932923838553)
                    ·
                      refine ⟨3614314331861199692878915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819085775814932923838553 3614314331861199692878915)
                      ·
                        rfl

theorem cell23_7038852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_7038852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038852 prefixEnd_7038852 := by exact prefixLift 7038852
  have htrace : WordTrace (prefixWord ++ tailWord_7038852) baseStart_7038852 baseEnd_7038852 := by
    simpa [prefixWord, tailWord_7038852, baseEnd_7038852] using wordTrace_append hprefix tailTrace_7038852
  have hstable : (prefixWord ++ tailWord_7038852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038852).length < 2 ^ (prefixWord ++ tailWord_7038852).sum := by decide
  have hdescent : baseEnd_7038852 < baseStart_7038852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038856 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 1, 3, 2]
def baseStart_7038856 : Nat := 118140960795 + 7038856 * 2 ^ 59
def prefixEnd_7038856 : Nat := 4983230072969 + 3 ^ 40 * 7038856 * 2
def baseEnd_7038856 : Nat := 3614316385783817677228897

theorem tailTrace_7038856 : CollatzResearch.WordTrace tailWord_7038856 prefixEnd_7038856 3614316385783817677228897 := by
  unfold tailWord_7038856
  simp only [CollatzResearch.WordTrace]
  refine ⟨128364084693717163871292211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171152112924956218495056281 128364084693717163871292211)
  ·
    refine ⟨192546127040575745806938317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128364084693717163871292211 192546127040575745806938317)
    ·
      refine ⟨72204797640215904677601869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192546127040575745806938317 72204797640215904677601869)
      ·
        refine ⟨27076799115080964254100701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72204797640215904677601869 27076799115080964254100701)
        ·
          refine ⟨10153799668155361595287763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27076799115080964254100701 10153799668155361595287763)
          ·
            refine ⟨15230699502233042392931645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153799668155361595287763 15230699502233042392931645)
            ·
              refine ⟨5711512313337390897349367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15230699502233042392931645 5711512313337390897349367)
              ·
                refine ⟨8567268470006086346024051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5711512313337390897349367 8567268470006086346024051)
                ·
                  refine ⟨12850902705009129519036077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8567268470006086346024051 12850902705009129519036077)
                  ·
                    refine ⟨4819088514378423569638529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12850902705009129519036077 4819088514378423569638529)
                    ·
                      refine ⟨3614316385783817677228897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819088514378423569638529 3614316385783817677228897)
                      ·
                        rfl

theorem cell23_7038856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_7038856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038856 prefixEnd_7038856 := by exact prefixLift 7038856
  have htrace : WordTrace (prefixWord ++ tailWord_7038856) baseStart_7038856 baseEnd_7038856 := by
    simpa [prefixWord, tailWord_7038856, baseEnd_7038856] using wordTrace_append hprefix tailTrace_7038856
  have hstable : (prefixWord ++ tailWord_7038856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038856).length < 2 ^ (prefixWord ++ tailWord_7038856).sum := by decide
  have hdescent : baseEnd_7038856 < baseStart_7038856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038869 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 2, 2, 2]
def baseStart_7038869 : Nat := 118140960795 + 7038869 * 2 ^ 59
def prefixEnd_7038869 : Nat := 4983230072969 + 3 ^ 40 * 7038869 * 2
def baseEnd_7038869 : Nat := 3614323061032326126366337

theorem tailTrace_7038869 : CollatzResearch.WordTrace tailWord_7038869 prefixEnd_7038869 3614323061032326126366337 := by
  unfold tailWord_7038869
  simp only [CollatzResearch.WordTrace]
  refine ⟨256728643536387230962807661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171152429024258153975205107 256728643536387230962807661)
  ·
    refine ⟨96273241326145211611052873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256728643536387230962807661 96273241326145211611052873)
    ·
      refine ⟨72204930994608908708289655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96273241326145211611052873 72204930994608908708289655)
      ·
        refine ⟨108307396491913363062434483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72204930994608908708289655 108307396491913363062434483)
        ·
          refine ⟨162461094737870044593651725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108307396491913363062434483 162461094737870044593651725)
          ·
            refine ⟨60922910526701266722619397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162461094737870044593651725 60922910526701266722619397)
            ·
              refine ⟨11423045723756487510491137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60922910526701266722619397 11423045723756487510491137)
              ·
                refine ⟨8567284292817365632868353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11423045723756487510491137 8567284292817365632868353)
                ·
                  refine ⟨6425463219613024224651265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8567284292817365632868353 6425463219613024224651265)
                  ·
                    refine ⟨4819097414709768168488449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6425463219613024224651265 4819097414709768168488449)
                    ·
                      refine ⟨3614323061032326126366337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819097414709768168488449 3614323061032326126366337)
                      ·
                        rfl

theorem cell23_7038869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_7038869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038869 prefixEnd_7038869 := by exact prefixLift 7038869
  have htrace : WordTrace (prefixWord ++ tailWord_7038869) baseStart_7038869 baseEnd_7038869 := by
    simpa [prefixWord, tailWord_7038869, baseEnd_7038869] using wordTrace_append hprefix tailTrace_7038869
  have hstable : (prefixWord ++ tailWord_7038869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038869).length < 2 ^ (prefixWord ++ tailWord_7038869).sum := by decide
  have hdescent : baseEnd_7038869 < baseStart_7038869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038882 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_7038882 : Nat := 118140960795 + 7038882 * 2 ^ 59
def prefixEnd_7038882 : Nat := 4983230072969 + 3 ^ 40 * 7038882 * 2
def baseEnd_7038882 : Nat := 3614329736280834575503777

theorem tailTrace_7038882 : CollatzResearch.WordTrace tailWord_7038882 prefixEnd_7038882 3614329736280834575503777 := by
  unfold tailWord_7038882
  simp only [CollatzResearch.WordTrace]
  refine ⟨64182279421335033545757725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171152745123560089455353933 64182279421335033545757725)
  ·
    refine ⟨24068354783000637579659147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64182279421335033545757725 24068354783000637579659147)
    ·
      refine ⟨36102532174500956369488721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24068354783000637579659147 36102532174500956369488721)
      ·
        refine ⟨27076899130875717277116541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36102532174500956369488721 27076899130875717277116541)
        ·
          refine ⟨10153837174078393978918703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27076899130875717277116541 10153837174078393978918703)
          ·
            refine ⟨15230755761117590968378055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153837174078393978918703 15230755761117590968378055)
            ·
              refine ⟨22846133641676386452567083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15230755761117590968378055 22846133641676386452567083)
              ·
                refine ⟨34269200462514579678850625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22846133641676386452567083 34269200462514579678850625)
                ·
                  refine ⟨25701900346885934759137969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34269200462514579678850625 25701900346885934759137969)
                  ·
                    refine ⟨19276425260164451069353477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25701900346885934759137969 19276425260164451069353477)
                    ·
                      refine ⟨3614329736280834575503777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19276425260164451069353477 3614329736280834575503777)
                      ·
                        rfl

theorem cell23_7038882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_7038882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038882 prefixEnd_7038882 := by exact prefixLift 7038882
  have htrace : WordTrace (prefixWord ++ tailWord_7038882) baseStart_7038882 baseEnd_7038882 := by
    simpa [prefixWord, tailWord_7038882, baseEnd_7038882] using wordTrace_append hprefix tailTrace_7038882
  have hstable : (prefixWord ++ tailWord_7038882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038882).length < 2 ^ (prefixWord ++ tailWord_7038882).sum := by decide
  have hdescent : baseEnd_7038882 < baseStart_7038882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038895 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 2, 5, 2]
def baseStart_7038895 : Nat := 118140960795 + 7038895 * 2 ^ 59
def prefixEnd_7038895 : Nat := 4983230072969 + 3 ^ 40 * 7038895 * 2
def baseEnd_7038895 : Nat := 3614336411529343024641217

theorem tailTrace_7038895 : CollatzResearch.WordTrace tailWord_7038895 prefixEnd_7038895 3614336411529343024641217 := by
  unfold tailWord_7038895
  simp only [CollatzResearch.WordTrace]
  refine ⟨256729591834293037403254139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171153061222862024935502759 256729591834293037403254139)
  ·
    refine ⟨385094387751439556104881209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256729591834293037403254139 385094387751439556104881209)
    ·
      refine ⟨288820790813579667078660907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385094387751439556104881209 288820790813579667078660907)
      ·
        refine ⟨433231186220369500617991361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288820790813579667078660907 433231186220369500617991361)
        ·
          refine ⟨324923389665277125463493521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433231186220369500617991361 324923389665277125463493521)
          ·
            refine ⟨243692542248957844097620141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324923389665277125463493521 243692542248957844097620141)
            ·
              refine ⟨91384703343359191536607553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243692542248957844097620141 91384703343359191536607553)
              ·
                refine ⟨68538527507519393652455665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91384703343359191536607553 68538527507519393652455665)
                ·
                  refine ⟨51403895630639545239341749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68538527507519393652455665 51403895630639545239341749)
                  ·
                    refine ⟨4819115215372457366188289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51403895630639545239341749 4819115215372457366188289)
                    ·
                      refine ⟨3614336411529343024641217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819115215372457366188289 3614336411529343024641217)
                      ·
                        rfl

theorem cell23_7038895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 5, 2].length) (baseStart_7038895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038895 prefixEnd_7038895 := by exact prefixLift 7038895
  have htrace : WordTrace (prefixWord ++ tailWord_7038895) baseStart_7038895 baseEnd_7038895 := by
    simpa [prefixWord, tailWord_7038895, baseEnd_7038895] using wordTrace_append hprefix tailTrace_7038895
  have hstable : (prefixWord ++ tailWord_7038895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038895).length < 2 ^ (prefixWord ++ tailWord_7038895).sum := by decide
  have hdescent : baseEnd_7038895 < baseStart_7038895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038898 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_7038898 : Nat := 118140960795 + 7038898 * 2 ^ 59
def prefixEnd_7038898 : Nat := 4983230072969 + 3 ^ 40 * 7038898 * 2
def baseEnd_7038898 : Nat := 3614337951971306512903703

theorem tailTrace_7038898 : CollatzResearch.WordTrace tailWord_7038898 prefixEnd_7038898 3614337951971306512903703 := by
  unfold tailWord_7038898
  simp only [CollatzResearch.WordTrace]
  refine ⟨64182425313320542228903337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171153134168854779277075565 64182425313320542228903337)
  ·
    refine ⟨48136818984990406671677503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64182425313320542228903337 48136818984990406671677503)
    ·
      refine ⟨72205228477485610007516255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48136818984990406671677503 72205228477485610007516255)
      ·
        refine ⟨108307842716228415011274383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72205228477485610007516255 108307842716228415011274383)
        ·
          refine ⟨162461764074342622516911575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108307842716228415011274383 162461764074342622516911575)
          ·
            refine ⟨243692646111513933775367363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162461764074342622516911575 243692646111513933775367363)
            ·
              refine ⟨365538969167270900663051045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243692646111513933775367363 365538969167270900663051045)
              ·
                refine ⟨68538556718863293874322071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365538969167270900663051045 68538556718863293874322071)
                ·
                  refine ⟨102807835078294940811483107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68538556718863293874322071 102807835078294940811483107)
                  ·
                    refine ⟨154211752617442411217224661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102807835078294940811483107 154211752617442411217224661)
                    ·
                      refine ⟨3614337951971306512903703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154211752617442411217224661 3614337951971306512903703)
                      ·
                        rfl

theorem cell23_7038898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_7038898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038898 prefixEnd_7038898 := by exact prefixLift 7038898
  have htrace : WordTrace (prefixWord ++ tailWord_7038898) baseStart_7038898 baseEnd_7038898 := by
    simpa [prefixWord, tailWord_7038898, baseEnd_7038898] using wordTrace_append hprefix tailTrace_7038898
  have hstable : (prefixWord ++ tailWord_7038898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038898).length < 2 ^ (prefixWord ++ tailWord_7038898).sum := by decide
  have hdescent : baseEnd_7038898 < baseStart_7038898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038928 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_7038928 : Nat := 118140960795 + 7038928 * 2 ^ 59
def prefixEnd_7038928 : Nat := 4983230072969 + 3 ^ 40 * 7038928 * 2
def baseEnd_7038928 : Nat := 3614353356390941395528565

theorem tailTrace_7038928 : CollatzResearch.WordTrace tailWord_7038928 prefixEnd_7038928 3614353356390941395528565 := by
  unfold tailWord_7038928
  simp only [CollatzResearch.WordTrace]
  refine ⟨128365397721586742019602719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171153863628782322692803625 128365397721586742019602719)
  ·
    refine ⟨192548096582380113029404079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128365397721586742019602719 192548096582380113029404079)
    ·
      refine ⟨288822144873570169544106119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192548096582380113029404079 288822144873570169544106119)
      ·
        refine ⟨433233217310355254316159179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288822144873570169544106119 433233217310355254316159179)
        ·
          refine ⟨649849825965532881474238769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433233217310355254316159179 649849825965532881474238769)
          ·
            refine ⟨487387369474149661105679077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649849825965532881474238769 487387369474149661105679077)
            ·
              refine ⟨91385131776403061457314827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 487387369474149661105679077 91385131776403061457314827)
              ·
                refine ⟨137077697664604592185972241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91385131776403061457314827 137077697664604592185972241)
                ·
                  refine ⟨102808273248453444139479181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137077697664604592185972241 102808273248453444139479181)
                  ·
                    refine ⟨38553102468170041552304693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102808273248453444139479181 38553102468170041552304693)
                    ·
                      refine ⟨3614353356390941395528565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38553102468170041552304693 3614353356390941395528565)
                      ·
                        rfl

theorem cell23_7038928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_7038928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038928 prefixEnd_7038928 := by exact prefixLift 7038928
  have htrace : WordTrace (prefixWord ++ tailWord_7038928) baseStart_7038928 baseEnd_7038928 := by
    simpa [prefixWord, tailWord_7038928, baseEnd_7038928] using wordTrace_append hprefix tailTrace_7038928
  have hstable : (prefixWord ++ tailWord_7038928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038928).length < 2 ^ (prefixWord ++ tailWord_7038928).sum := by decide
  have hdescent : baseEnd_7038928 < baseStart_7038928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038945 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_7038945 : Nat := 118140960795 + 7038945 * 2 ^ 59
def prefixEnd_7038945 : Nat := 4983230072969 + 3 ^ 40 * 7038945 * 2
def baseEnd_7038945 : Nat := 3614362085562067829015987

theorem tailTrace_7038945 : CollatzResearch.WordTrace tailWord_7038945 prefixEnd_7038945 3614362085562067829015987 := by
  unfold tailWord_7038945
  simp only [CollatzResearch.WordTrace]
  refine ⟨256731415484111895942574289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171154276989407930628382859 256731415484111895942574289)
  ·
    refine ⟨192548561613083921956930717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256731415484111895942574289 192548561613083921956930717)
    ·
      refine ⟨72205710604906470733849019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192548561613083921956930717 72205710604906470733849019)
      ·
        refine ⟨108308565907359706100773529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72205710604906470733849019 108308565907359706100773529)
        ·
          refine ⟨81231424430519779575580147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108308565907359706100773529 81231424430519779575580147)
          ·
            refine ⟨121847136645779669363370221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81231424430519779575580147 121847136645779669363370221)
            ·
              refine ⟨45692676242167376011263833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121847136645779669363370221 45692676242167376011263833)
              ·
                refine ⟨34269507181625532008447875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45692676242167376011263833 34269507181625532008447875)
                ·
                  refine ⟨51404260772438298012671813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34269507181625532008447875 51404260772438298012671813)
                  ·
                    refine ⟨9638298894832180877375965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51404260772438298012671813 9638298894832180877375965)
                    ·
                      refine ⟨3614362085562067829015987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9638298894832180877375965 3614362085562067829015987)
                      ·
                        rfl

theorem cell23_7038945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_7038945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038945 prefixEnd_7038945 := by exact prefixLift 7038945
  have htrace : WordTrace (prefixWord ++ tailWord_7038945) baseStart_7038945 baseEnd_7038945 := by
    simpa [prefixWord, tailWord_7038945, baseEnd_7038945] using wordTrace_append hprefix tailTrace_7038945
  have hstable : (prefixWord ++ tailWord_7038945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038945).length < 2 ^ (prefixWord ++ tailWord_7038945).sum := by decide
  have hdescent : baseEnd_7038945 < baseStart_7038945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038969 : List Nat := [1, 2, 1, 3, 1, 4, 3, 3, 1, 4]
def baseStart_7038969 : Nat := 118140960795 + 7038969 * 2 ^ 59
def prefixEnd_7038969 : Nat := 4983230072969 + 3 ^ 40 * 7038969 * 2
def baseEnd_7038969 : Nat := 1204791469699258578371959

theorem tailTrace_7038969 : CollatzResearch.WordTrace tailWord_7038969 prefixEnd_7038969 1204791469699258578371959 := by
  unfold tailWord_7038969
  simp only [CollatzResearch.WordTrace]
  refine ⟨256732290836024948041447961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171154860557349965360965307 256732290836024948041447961)
  ·
    refine ⟨192549218127018711031085971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256732290836024948041447961 192549218127018711031085971)
    ·
      refine ⟨288823827190528066546628957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192549218127018711031085971 288823827190528066546628957)
      ·
        refine ⟨108308935196448024954985859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288823827190528066546628957 108308935196448024954985859)
        ·
          refine ⟨162463402794672037432478789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108308935196448024954985859 162463402794672037432478789)
          ·
            refine ⟨30461888024001007018589773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162463402794672037432478789 30461888024001007018589773)
            ·
              refine ⟨11423208009000377631971165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30461888024001007018589773 11423208009000377631971165)
              ·
                refine ⟨4283703003375141611989187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11423208009000377631971165 4283703003375141611989187)
                ·
                  refine ⟨6425554505062712417983781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283703003375141611989187 6425554505062712417983781)
                  ·
                    refine ⟨1204791469699258578371959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6425554505062712417983781 1204791469699258578371959)
                    ·
                      rfl

theorem cell23_7038969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 1, 4].length) (baseStart_7038969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038969 prefixEnd_7038969 := by exact prefixLift 7038969
  have htrace : WordTrace (prefixWord ++ tailWord_7038969) baseStart_7038969 baseEnd_7038969 := by
    simpa [prefixWord, tailWord_7038969, baseEnd_7038969] using wordTrace_append hprefix tailTrace_7038969
  have hstable : (prefixWord ++ tailWord_7038969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038969).length < 2 ^ (prefixWord ++ tailWord_7038969).sum := by decide
  have hdescent : baseEnd_7038969 < baseStart_7038969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038986 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 3, 4]
def baseStart_7038986 : Nat := 118140960795 + 7038986 * 2 ^ 59
def prefixEnd_7038986 : Nat := 4983230072969 + 3 ^ 40 * 7038986 * 2
def baseEnd_7038986 : Nat := 1204794379422967389534433

theorem tailTrace_7038986 : CollatzResearch.WordTrace tailWord_7038986 prefixEnd_7038986 1204794379422967389534433 := by
  unfold tailWord_7038986
  simp only [CollatzResearch.WordTrace]
  refine ⟨64183227719240839986204203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171155273917975573296544541 64183227719240839986204203)
  ·
    refine ⟨96274841578861259979306305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64183227719240839986204203 96274841578861259979306305)
    ·
      refine ⟨72206131184145944984479729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96274841578861259979306305 72206131184145944984479729)
      ·
        refine ⟨54154598388109458738359797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72206131184145944984479729 54154598388109458738359797)
        ·
          refine ⟨5076993598885261756721231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54154598388109458738359797 5076993598885261756721231)
          ·
            refine ⟨7615490398327892635081847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076993598885261756721231 7615490398327892635081847)
            ·
              refine ⟨11423235597491838952622771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7615490398327892635081847 11423235597491838952622771)
              ·
                refine ⟨17134853396237758428934157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11423235597491838952622771 17134853396237758428934157)
                ·
                  refine ⟨6425570023589159410850309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17134853396237758428934157 6425570023589159410850309)
                  ·
                    refine ⟨1204794379422967389534433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6425570023589159410850309 1204794379422967389534433)
                    ·
                      rfl

theorem cell23_7038986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_7038986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038986 prefixEnd_7038986 := by exact prefixLift 7038986
  have htrace : WordTrace (prefixWord ++ tailWord_7038986) baseStart_7038986 baseEnd_7038986 := by
    simpa [prefixWord, tailWord_7038986, baseEnd_7038986] using wordTrace_append hprefix tailTrace_7038986
  have hstable : (prefixWord ++ tailWord_7038986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038986).length < 2 ^ (prefixWord ++ tailWord_7038986).sum := by decide
  have hdescent : baseEnd_7038986 < baseStart_7038986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039025 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 3, 6]
def baseStart_7039025 : Nat := 118140960795 + 7039025 * 2 ^ 59
def prefixEnd_7039025 : Nat := 4983230072969 + 3 ^ 40 * 7039025 * 2
def baseEnd_7039025 : Nat := 1204801054671475838671873

theorem tailTrace_7039025 : CollatzResearch.WordTrace tailWord_7039025 prefixEnd_7039025 1204801054671475838671873 := by
  unfold tailWord_7039025
  simp only [CollatzResearch.WordTrace]
  refine ⟨256734333323822069605486529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171156222215881379736991019 256734333323822069605486529)
  ·
    refine ⟨192550749992866552204114897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256734333323822069605486529 192550749992866552204114897)
    ·
      refine ⟨144413062494649914153086173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192550749992866552204114897 144413062494649914153086173)
      ·
        refine ⟨54154898435493717807407315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144413062494649914153086173 54154898435493717807407315)
        ·
          refine ⟨81232347653240576711110973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54154898435493717807407315 81232347653240576711110973)
          ·
            refine ⟨30462130369965216266666615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81232347653240576711110973 30462130369965216266666615)
            ·
              refine ⟨45693195554947824399999923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30462130369965216266666615 45693195554947824399999923)
              ·
                refine ⟨68539793332421736599999885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45693195554947824399999923 68539793332421736599999885)
                ·
                  refine ⟨25702422499658151224999957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68539793332421736599999885 25702422499658151224999957)
                  ·
                    refine ⟨1204801054671475838671873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25702422499658151224999957 1204801054671475838671873)
                    ·
                      rfl

theorem cell23_7039025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_7039025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039025 prefixEnd_7039025 := by exact prefixLift 7039025
  have htrace : WordTrace (prefixWord ++ tailWord_7039025) baseStart_7039025 baseEnd_7039025 := by
    simpa [prefixWord, tailWord_7039025, baseEnd_7039025] using wordTrace_append hprefix tailTrace_7039025
  have hstable : (prefixWord ++ tailWord_7039025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039025).length < 2 ^ (prefixWord ++ tailWord_7039025).sum := by decide
  have hdescent : baseEnd_7039025 < baseStart_7039025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039045 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_7039045 : Nat := 118140960795 + 7039045 * 2 ^ 59
def prefixEnd_7039045 : Nat := 4983230072969 + 3 ^ 40 * 7039045 * 2
def baseEnd_7039045 : Nat := 3614413433627517437765527

theorem tailTrace_7039045 : CollatzResearch.WordTrace tailWord_7039045 prefixEnd_7039045 3614413433627517437765527 := by
  unfold tailWord_7039045
  simp only [CollatzResearch.WordTrace]
  refine ⟨256735062783749613021214589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171156708522499742014143059 256735062783749613021214589)
  ·
    refine ⟨96275648543906104882955471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256735062783749613021214589 96275648543906104882955471)
    ·
      refine ⟨144413472815859157324433207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96275648543906104882955471 144413472815859157324433207)
      ·
        refine ⟨216620209223788735986649811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144413472815859157324433207 216620209223788735986649811)
        ·
          refine ⟨324930313835683103979974717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216620209223788735986649811 324930313835683103979974717)
          ·
            refine ⟨121848867688381163992490519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324930313835683103979974717 121848867688381163992490519)
            ·
              refine ⟨182773301532571745988735779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121848867688381163992490519 182773301532571745988735779)
              ·
                refine ⟨274159952298857618983103669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182773301532571745988735779 274159952298857618983103669)
                ·
                  refine ⟨25702495528017901779665969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274159952298857618983103669 25702495528017901779665969)
                  ·
                    refine ⟨19276871646013426334749477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25702495528017901779665969 19276871646013426334749477)
                    ·
                      refine ⟨3614413433627517437765527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19276871646013426334749477 3614413433627517437765527)
                      ·
                        rfl

theorem cell23_7039045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_7039045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039045 prefixEnd_7039045 := by exact prefixLift 7039045
  have htrace : WordTrace (prefixWord ++ tailWord_7039045) baseStart_7039045 baseEnd_7039045 := by
    simpa [prefixWord, tailWord_7039045, baseEnd_7039045] using wordTrace_append hprefix tailTrace_7039045
  have hstable : (prefixWord ++ tailWord_7039045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039045).length < 2 ^ (prefixWord ++ tailWord_7039045).sum := by decide
  have hdescent : baseEnd_7039045 < baseStart_7039045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039049 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 3, 2, 2]
def baseStart_7039049 : Nat := 118140960795 + 7039049 * 2 ^ 59
def prefixEnd_7039049 : Nat := 4983230072969 + 3 ^ 40 * 7039049 * 2
def baseEnd_7039049 : Nat := 3614415487550135422115509

theorem tailTrace_7039049 : CollatzResearch.WordTrace tailWord_7039049 prefixEnd_7039049 3614415487550135422115509 := by
  unfold tailWord_7039049
  simp only [CollatzResearch.WordTrace]
  refine ⟨256735208675735121704360201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171156805783823414469573467 256735208675735121704360201)
  ·
    refine ⟨192551406506801341278270151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256735208675735121704360201 192551406506801341278270151)
    ·
      refine ⟨288827109760202011917405227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192551406506801341278270151 288827109760202011917405227)
      ·
        refine ⟨433240664640303017876107841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288827109760202011917405227 433240664640303017876107841)
        ·
          refine ⟨324930498480227263407080881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433240664640303017876107841 324930498480227263407080881)
          ·
            refine ⟨243697873860170447555310661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324930498480227263407080881 243697873860170447555310661)
            ·
              refine ⟨45693351348781958916620749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243697873860170447555310661 45693351348781958916620749)
              ·
                refine ⟨17135006755793234593732781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45693351348781958916620749 17135006755793234593732781)
                ·
                  refine ⟨6425627533422462972649793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17135006755793234593732781 6425627533422462972649793)
                  ·
                    refine ⟨4819220650066847229487345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6425627533422462972649793 4819220650066847229487345)
                    ·
                      refine ⟨3614415487550135422115509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819220650066847229487345 3614415487550135422115509)
                      ·
                        rfl

theorem cell23_7039049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 2, 2].length) (baseStart_7039049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039049 prefixEnd_7039049 := by exact prefixLift 7039049
  have htrace : WordTrace (prefixWord ++ tailWord_7039049) baseStart_7039049 baseEnd_7039049 := by
    simpa [prefixWord, tailWord_7039049, baseEnd_7039049] using wordTrace_append hprefix tailTrace_7039049
  have hstable : (prefixWord ++ tailWord_7039049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039049).length < 2 ^ (prefixWord ++ tailWord_7039049).sum := by decide
  have hdescent : baseEnd_7039049 < baseStart_7039049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039052 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 3, 2, 3]
def baseStart_7039052 : Nat := 118140960795 + 7039052 * 2 ^ 59
def prefixEnd_7039052 : Nat := 4983230072969 + 3 ^ 40 * 7039052 * 2
def baseEnd_7039052 : Nat := 3614417027992098910377995

theorem tailTrace_7039052 : CollatzResearch.WordTrace tailWord_7039052 prefixEnd_7039052 3614417027992098910377995 := by
  unfold tailWord_7039052
  simp only [CollatzResearch.WordTrace]
  refine ⟨128367659047362126608359705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171156878729816168811146273 128367659047362126608359705)
  ·
    refine ⟨96275744285521594956269779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128367659047362126608359705 96275744285521594956269779)
    ·
      refine ⟨144413616428282392434404669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96275744285521594956269779 144413616428282392434404669)
      ·
        refine ⟨54155106160605897162901751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144413616428282392434404669 54155106160605897162901751)
        ·
          refine ⟨81232659240908845744352627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54155106160605897162901751 81232659240908845744352627)
          ·
            refine ⟨121848988861363268616528941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81232659240908845744352627 121848988861363268616528941)
            ·
              refine ⟨45693370823011225731198353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121848988861363268616528941 45693370823011225731198353)
              ·
                refine ⟨34270028117258419298398765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45693370823011225731198353 34270028117258419298398765)
                ·
                  refine ⟨12851260543971907236899537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34270028117258419298398765 12851260543971907236899537)
                  ·
                    refine ⟨9638445407978930427674653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12851260543971907236899537 9638445407978930427674653)
                    ·
                      refine ⟨3614417027992098910377995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9638445407978930427674653 3614417027992098910377995)
                      ·
                        rfl

theorem cell23_7039052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_7039052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039052 prefixEnd_7039052 := by exact prefixLift 7039052
  have htrace : WordTrace (prefixWord ++ tailWord_7039052) baseStart_7039052 baseEnd_7039052 := by
    simpa [prefixWord, tailWord_7039052, baseEnd_7039052] using wordTrace_append hprefix tailTrace_7039052
  have hstable : (prefixWord ++ tailWord_7039052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039052).length < 2 ^ (prefixWord ++ tailWord_7039052).sum := by decide
  have hdescent : baseEnd_7039052 < baseStart_7039052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039072 : List Nat := [2, 1, 1, 3, 2, 4, 3, 7]
def baseStart_7039072 : Nat := 118140960795 + 7039072 * 2 ^ 59
def prefixEnd_7039072 : Nat := 4983230072969 + 3 ^ 40 * 7039072 * 2
def baseEnd_7039072 : Nat := 133867677689081067856589

theorem tailTrace_7039072 : CollatzResearch.WordTrace tailWord_7039072 prefixEnd_7039072 133867677689081067856589 := by
  unfold tailWord_7039072
  simp only [CollatzResearch.WordTrace]
  refine ⟨128368023777325898316223735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171157365036434531088298313 128368023777325898316223735)
  ·
    refine ⟨192552035665988847474335603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128368023777325898316223735 192552035665988847474335603)
    ·
      refine ⟨288828053498983271211503405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192552035665988847474335603 288828053498983271211503405)
      ·
        refine ⟨108310520062118726704313777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288828053498983271211503405 108310520062118726704313777)
        ·
          refine ⟨81232890046589045028235333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108310520062118726704313777 81232890046589045028235333)
          ·
            refine ⟨15231166883735445942794125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81232890046589045028235333 15231166883735445942794125)
            ·
              refine ⟨5711687581400792228547797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15231166883735445942794125 5711687581400792228547797)
              ·
                refine ⟨133867677689081067856589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5711687581400792228547797 133867677689081067856589)
                ·
                  rfl

theorem cell23_7039072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 7].length) (baseStart_7039072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039072 prefixEnd_7039072 := by exact prefixLift 7039072
  have htrace : WordTrace (prefixWord ++ tailWord_7039072) baseStart_7039072 baseEnd_7039072 := by
    simpa [prefixWord, tailWord_7039072, baseEnd_7039072] using wordTrace_append hprefix tailTrace_7039072
  have hstable : (prefixWord ++ tailWord_7039072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039072).length < 2 ^ (prefixWord ++ tailWord_7039072).sum := by decide
  have hdescent : baseEnd_7039072 < baseStart_7039072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039134 : List Nat := [4, 3, 1, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_7039134 : Nat := 118140960795 + 7039134 * 2 ^ 59
def prefixEnd_7039134 : Nat := 4983230072969 + 3 ^ 40 * 7039134 * 2
def baseEnd_7039134 : Nat := 3614459133405767589552619

theorem tailTrace_7039134 : CollatzResearch.WordTrace tailWord_7039134 prefixEnd_7039134 3614459133405767589552619 := by
  unfold tailWord_7039134
  simp only [CollatzResearch.WordTrace]
  refine ⟨32092288610053397652650557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171158872586951454147469637 32092288610053397652650557)
  ·
    refine ⟨12034608228770024119743959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32092288610053397652650557 12034608228770024119743959)
    ·
      refine ⟨18051912343155036179615939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12034608228770024119743959 18051912343155036179615939)
      ·
        refine ⟨27077868514732554269423909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18051912343155036179615939 27077868514732554269423909)
        ·
          refine ⟨5077100346512353925516983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27077868514732554269423909 5077100346512353925516983)
          ·
            refine ⟨7615650519768530888275475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077100346512353925516983 7615650519768530888275475)
            ·
              refine ⟨11423475779652796332413213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7615650519768530888275475 11423475779652796332413213)
              ·
                refine ⟨4283803417369798624654955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11423475779652796332413213 4283803417369798624654955)
                ·
                  refine ⟨6425705126054697936982433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283803417369798624654955 6425705126054697936982433)
                  ·
                    refine ⟨4819278844541023452736825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6425705126054697936982433 4819278844541023452736825)
                    ·
                      refine ⟨3614459133405767589552619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819278844541023452736825 3614459133405767589552619)
                      ·
                        rfl

theorem cell23_7039134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_7039134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039134 prefixEnd_7039134 := by exact prefixLift 7039134
  have htrace : WordTrace (prefixWord ++ tailWord_7039134) baseStart_7039134 baseEnd_7039134 := by
    simpa [prefixWord, tailWord_7039134, baseEnd_7039134] using wordTrace_append hprefix tailTrace_7039134
  have hstable : (prefixWord ++ tailWord_7039134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039134).length < 2 ^ (prefixWord ++ tailWord_7039134).sum := by decide
  have hdescent : baseEnd_7039134 < baseStart_7039134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039155 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 9]
def baseStart_7039155 : Nat := 118140960795 + 7039155 * 2 ^ 59
def prefixEnd_7039155 : Nat := 4983230072969 + 3 ^ 40 * 7039155 * 2
def baseEnd_7039155 : Nat := 3614469916499512007390021

theorem tailTrace_7039155 : CollatzResearch.WordTrace tailWord_7039155 prefixEnd_7039155 3614469916499512007390021 := by
  unfold tailWord_7039155
  simp only [CollatzResearch.WordTrace]
  refine ⟨256739074813351101807718919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171159383208900734538479279 256739074813351101807718919)
  ·
    refine ⟨385108612220026652711578379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256739074813351101807718919 385108612220026652711578379)
    ·
      refine ⟨577662918330039979067367569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385108612220026652711578379 577662918330039979067367569)
      ·
        refine ⟨433247188747529984300525677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577662918330039979067367569 433247188747529984300525677)
        ·
          refine ⟨162467695780323744112697129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433247188747529984300525677 162467695780323744112697129)
          ·
            refine ⟨121850771835242808084522847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162467695780323744112697129 121850771835242808084522847)
            ·
              refine ⟨182776157752864212126784271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121850771835242808084522847 182776157752864212126784271)
              ·
                refine ⟨274164236629296318190176407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182776157752864212126784271 274164236629296318190176407)
                ·
                  refine ⟨411246354943944477285264611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274164236629296318190176407 411246354943944477285264611)
                  ·
                    refine ⟨616869532415916715927896917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 411246354943944477285264611 616869532415916715927896917)
                    ·
                      refine ⟨3614469916499512007390021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 616869532415916715927896917 3614469916499512007390021)
                      ·
                        rfl

theorem cell23_7039155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_7039155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039155 prefixEnd_7039155 := by exact prefixLift 7039155
  have htrace : WordTrace (prefixWord ++ tailWord_7039155) baseStart_7039155 baseEnd_7039155 := by
    simpa [prefixWord, tailWord_7039155, baseEnd_7039155] using wordTrace_append hprefix tailTrace_7039155
  have hstable : (prefixWord ++ tailWord_7039155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039155).length < 2 ^ (prefixWord ++ tailWord_7039155).sum := by decide
  have hdescent : baseEnd_7039155 < baseStart_7039155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039162 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 7]
def baseStart_7039162 : Nat := 118140960795 + 7039162 * 2 ^ 59
def prefixEnd_7039162 : Nat := 4983230072969 + 3 ^ 40 * 7039162 * 2
def baseEnd_7039162 : Nat := 401608167873788164444721

theorem tailTrace_7039162 : CollatzResearch.WordTrace tailWord_7039162 prefixEnd_7039162 401608167873788164444721 := by
  unfold tailWord_7039162
  simp only [CollatzResearch.WordTrace]
  refine ⟨64184832531081435500805935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171159553416217161335482493 64184832531081435500805935)
  ·
    refine ⟨96277248796622153251208903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64184832531081435500805935 96277248796622153251208903)
    ·
      refine ⟨144415873194933229876813355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96277248796622153251208903 144415873194933229876813355)
      ·
        refine ⟨216623809792399844815220033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144415873194933229876813355 216623809792399844815220033)
        ·
          refine ⟨162467857344299883611415025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216623809792399844815220033 162467857344299883611415025)
          ·
            refine ⟨121850893008224912708561269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162467857344299883611415025 121850893008224912708561269)
            ·
              refine ⟨11423521219521085566427619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121850893008224912708561269 11423521219521085566427619)
              ·
                refine ⟨17135281829281628349641429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11423521219521085566427619 17135281829281628349641429)
                ·
                  refine ⟨401608167873788164444721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17135281829281628349641429 401608167873788164444721)
                  ·
                    rfl

theorem cell23_7039162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_7039162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039162 prefixEnd_7039162 := by exact prefixLift 7039162
  have htrace : WordTrace (prefixWord ++ tailWord_7039162) baseStart_7039162 baseEnd_7039162 := by
    simpa [prefixWord, tailWord_7039162, baseEnd_7039162] using wordTrace_append hprefix tailTrace_7039162
  have hstable : (prefixWord ++ tailWord_7039162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039162).length < 2 ^ (prefixWord ++ tailWord_7039162).sum := by decide
  have hdescent : baseEnd_7039162 < baseStart_7039162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039173 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 2, 2, 2]
def baseStart_7039173 : Nat := 118140960795 + 7039173 * 2 ^ 59
def prefixEnd_7039173 : Nat := 4983230072969 + 3 ^ 40 * 7039173 * 2
def baseEnd_7039173 : Nat := 3614479159151292936964939

theorem tailTrace_7039173 : CollatzResearch.WordTrace tailWord_7039173 prefixEnd_7039173 3614479159151292936964939 := by
  unfold tailWord_7039173
  simp only [CollatzResearch.WordTrace]
  refine ⟨256739731327285890881874173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171159820884857260587916115 256739731327285890881874173)
  ·
    refine ⟨96277399247732209080702815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256739731327285890881874173 96277399247732209080702815)
    ·
      refine ⟨144416098871598313621054223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96277399247732209080702815 144416098871598313621054223)
      ·
        refine ⟨216624148307397470431581335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144416098871598313621054223 216624148307397470431581335)
        ·
          refine ⟨324936222461096205647372003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216624148307397470431581335 324936222461096205647372003)
          ·
            refine ⟨487404333691644308471058005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324936222461096205647372003 487404333691644308471058005)
            ·
              refine ⟨5711769535448956739895211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 487404333691644308471058005 5711769535448956739895211)
              ·
                refine ⟨8567654303173435109842817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5711769535448956739895211 8567654303173435109842817)
                ·
                  refine ⟨6425740727380076332382113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8567654303173435109842817 6425740727380076332382113)
                  ·
                    refine ⟨4819305545535057249286585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6425740727380076332382113 4819305545535057249286585)
                    ·
                      refine ⟨3614479159151292936964939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819305545535057249286585 3614479159151292936964939)
                      ·
                        rfl

theorem cell23_7039173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_7039173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039173 prefixEnd_7039173 := by exact prefixLift 7039173
  have htrace : WordTrace (prefixWord ++ tailWord_7039173) baseStart_7039173 baseEnd_7039173 := by
    simpa [prefixWord, tailWord_7039173, baseEnd_7039173] using wordTrace_append hprefix tailTrace_7039173
  have hstable : (prefixWord ++ tailWord_7039173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039173).length < 2 ^ (prefixWord ++ tailWord_7039173).sum := by decide
  have hdescent : baseEnd_7039173 < baseStart_7039173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039249 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 3]
def baseStart_7039249 : Nat := 118140960795 + 7039249 * 2 ^ 59
def prefixEnd_7039249 : Nat := 4983230072969 + 3 ^ 40 * 7039249 * 2
def baseEnd_7039249 : Nat := 3614518183681034639614589

theorem tailTrace_7039249 : CollatzResearch.WordTrace tailWord_7039249 prefixEnd_7039249 3614518183681034639614589 := by
  unfold tailWord_7039249
  simp only [CollatzResearch.WordTrace]
  refine ⟨256742503275010555861640801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171161668850007037241093867 256742503275010555861640801)
  ·
    refine ⟨192556877456257916896230601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256742503275010555861640801 192556877456257916896230601)
    ·
      refine ⟨144417658092193437672172951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192556877456257916896230601 144417658092193437672172951)
      ·
        refine ⟨216626487138290156508259427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144417658092193437672172951 216626487138290156508259427)
        ·
          refine ⟨324939730707435234762389141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216626487138290156508259427 324939730707435234762389141)
          ·
            refine ⟨15231549876911026629486991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 324939730707435234762389141 15231549876911026629486991)
            ·
              refine ⟨22847324815366539944230487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15231549876911026629486991 22847324815366539944230487)
              ·
                refine ⟨34270987223049809916345731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22847324815366539944230487 34270987223049809916345731)
                ·
                  refine ⟨51406480834574714874518597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34270987223049809916345731 51406480834574714874518597)
                  ·
                    refine ⟨9638715156482759038972237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51406480834574714874518597 9638715156482759038972237)
                    ·
                      refine ⟨3614518183681034639614589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9638715156482759038972237 3614518183681034639614589)
                      ·
                        rfl

theorem cell23_7039249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_7039249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039249 prefixEnd_7039249 := by exact prefixLift 7039249
  have htrace : WordTrace (prefixWord ++ tailWord_7039249) baseStart_7039249 baseEnd_7039249 := by
    simpa [prefixWord, tailWord_7039249, baseEnd_7039249] using wordTrace_append hprefix tailTrace_7039249
  have hstable : (prefixWord ++ tailWord_7039249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039249).length < 2 ^ (prefixWord ++ tailWord_7039249).sum := by decide
  have hdescent : baseEnd_7039249 < baseStart_7039249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039269 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 8]
def baseStart_7039269 : Nat := 118140960795 + 7039269 * 2 ^ 59
def prefixEnd_7039269 : Nat := 4983230072969 + 3 ^ 40 * 7039269 * 2
def baseEnd_7039269 : Nat := 401614272588236062373833

theorem tailTrace_7039269 : CollatzResearch.WordTrace tailWord_7039269 prefixEnd_7039269 401614272588236062373833 := by
  unfold tailWord_7039269
  simp only [CollatzResearch.WordTrace]
  refine ⟨256743232734938099277368861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171162155156625399518245907 256743232734938099277368861)
  ·
    refine ⟨96278712275601787229013323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256743232734938099277368861 96278712275601787229013323)
    ·
      refine ⟨144418068413402680843519985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96278712275601787229013323 144418068413402680843519985)
      ·
        refine ⟨108313551310052010632639989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144418068413402680843519985 108313551310052010632639989)
        ·
          refine ⟨10154395435317375996809999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108313551310052010632639989 10154395435317375996809999)
          ·
            refine ⟨15231593152976063995214999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10154395435317375996809999 15231593152976063995214999)
            ·
              refine ⟨22847389729464095992822499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15231593152976063995214999 22847389729464095992822499)
              ·
                refine ⟨34271084594196143989233749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22847389729464095992822499 34271084594196143989233749)
                ·
                  refine ⟨401614272588236062373833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34271084594196143989233749 401614272588236062373833)
                  ·
                    rfl

theorem cell23_7039269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_7039269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039269 prefixEnd_7039269 := by exact prefixLift 7039269
  have htrace : WordTrace (prefixWord ++ tailWord_7039269) baseStart_7039269 baseEnd_7039269 := by
    simpa [prefixWord, tailWord_7039269, baseEnd_7039269] using wordTrace_append hprefix tailTrace_7039269
  have hstable : (prefixWord ++ tailWord_7039269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039269).length < 2 ^ (prefixWord ++ tailWord_7039269).sum := by decide
  have hdescent : baseEnd_7039269 < baseStart_7039269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039299 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 1, 5]
def baseStart_7039299 : Nat := 118140960795 + 7039299 * 2 ^ 59
def prefixEnd_7039299 : Nat := 4983230072969 + 3 ^ 40 * 7039299 * 2
def baseEnd_7039299 : Nat := 1204847952571253147996453

theorem tailTrace_7039299 : CollatzResearch.WordTrace tailWord_7039299 prefixEnd_7039299 1204847952571253147996453 := by
  unfold tailWord_7039299
  simp only [CollatzResearch.WordTrace]
  refine ⟨256744326924829414400960951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171162884616552942933973967 256744326924829414400960951)
  ·
    refine ⟨385116490387244121601441427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256744326924829414400960951 385116490387244121601441427)
    ·
      refine ⟨577674735580866182402162141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385116490387244121601441427 577674735580866182402162141)
      ·
        refine ⟨216628025842824818400810803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577674735580866182402162141 216628025842824818400810803)
        ·
          refine ⟨324942038764237227601216205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216628025842824818400810803 324942038764237227601216205)
          ·
            refine ⟨121853264536588960350456077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324942038764237227601216205 121853264536588960350456077)
            ·
              refine ⟨45694974201220860131421029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121853264536588960350456077 45694974201220860131421029)
              ·
                refine ⟨8567807662728911274641443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45694974201220860131421029 8567807662728911274641443)
                ·
                  refine ⟨12851711494093366911962165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8567807662728911274641443 12851711494093366911962165)
                  ·
                    refine ⟨1204847952571253147996453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12851711494093366911962165 1204847952571253147996453)
                    ·
                      rfl

theorem cell23_7039299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 5].length) (baseStart_7039299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039299 prefixEnd_7039299 := by exact prefixLift 7039299
  have htrace : WordTrace (prefixWord ++ tailWord_7039299) baseStart_7039299 baseEnd_7039299 := by
    simpa [prefixWord, tailWord_7039299, baseEnd_7039299] using wordTrace_append hprefix tailTrace_7039299
  have hstable : (prefixWord ++ tailWord_7039299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039299).length < 2 ^ (prefixWord ++ tailWord_7039299).sum := by decide
  have hdescent : baseEnd_7039299 < baseStart_7039299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039316 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_7039316 : Nat := 118140960795 + 7039316 * 2 ^ 59
def prefixEnd_7039316 : Nat := 4983230072969 + 3 ^ 40 * 7039316 * 2
def baseEnd_7039316 : Nat := 1204850862294961959158927

theorem tailTrace_7039316 : CollatzResearch.WordTrace tailWord_7039316 prefixEnd_7039316 1204850862294961959158927 := by
  unfold tailWord_7039316
  simp only [CollatzResearch.WordTrace]
  refine ⟨128372473482883913152164901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171163297977178550869553201 128372473482883913152164901)
  ·
    refine ⟨24069838778040733716030919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128372473482883913152164901 24069838778040733716030919)
    ·
      refine ⟨36104758167061100574046379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24069838778040733716030919 36104758167061100574046379)
      ·
        refine ⟨54157137250591650861069569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36104758167061100574046379 54157137250591650861069569)
        ·
          refine ⟨40617852937943738145802177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54157137250591650861069569 40617852937943738145802177)
          ·
            refine ⟨30463389703457803609351633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40617852937943738145802177 30463389703457803609351633)
            ·
              refine ⟨22847542277593352707013725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30463389703457803609351633 22847542277593352707013725)
              ·
                refine ⟨8567828354097507265130147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22847542277593352707013725 8567828354097507265130147)
                ·
                  refine ⟨12851742531146260897695221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8567828354097507265130147 12851742531146260897695221)
                  ·
                    refine ⟨1204850862294961959158927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12851742531146260897695221 1204850862294961959158927)
                    ·
                      rfl

theorem cell23_7039316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_7039316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039316 prefixEnd_7039316 := by exact prefixLift 7039316
  have htrace : WordTrace (prefixWord ++ tailWord_7039316) baseStart_7039316 baseEnd_7039316 := by
    simpa [prefixWord, tailWord_7039316, baseEnd_7039316] using wordTrace_append hprefix tailTrace_7039316
  have hstable : (prefixWord ++ tailWord_7039316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039316).length < 2 ^ (prefixWord ++ tailWord_7039316).sum := by decide
  have hdescent : baseEnd_7039316 < baseStart_7039316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039330 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_7039330 : Nat := 118140960795 + 7039330 * 2 ^ 59
def prefixEnd_7039330 : Nat := 4983230072969 + 3 ^ 40 * 7039330 * 2
def baseEnd_7039330 : Nat := 3614559775614048822701717

theorem tailTrace_7039330 : CollatzResearch.WordTrace tailWord_7039330 prefixEnd_7039330 3614559775614048822701717 := by
  unfold tailWord_7039330
  simp only [CollatzResearch.WordTrace]
  refine ⟨64186364396929276673834861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171163638391811404463559629 64186364396929276673834861)
  ·
    refine ⟨24069886648848478752688073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64186364396929276673834861 24069886648848478752688073)
    ·
      refine ⟨18052414986636359064516055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24069886648848478752688073 18052414986636359064516055)
      ·
        refine ⟨27078622479954538596774083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18052414986636359064516055 27078622479954538596774083)
        ·
          refine ⟨40617933719931807895161125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27078622479954538596774083 40617933719931807895161125)
          ·
            refine ⟨7615862572487213980342711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40617933719931807895161125 7615862572487213980342711)
            ·
              refine ⟨11423793858730820970514067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7615862572487213980342711 11423793858730820970514067)
              ·
                refine ⟨17135690788096231455771101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11423793858730820970514067 17135690788096231455771101)
                ·
                  refine ⟨6425884045536086795914163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17135690788096231455771101 6425884045536086795914163)
                  ·
                    refine ⟨9638826068304130193871245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6425884045536086795914163 9638826068304130193871245)
                    ·
                      refine ⟨3614559775614048822701717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9638826068304130193871245 3614559775614048822701717)
                      ·
                        rfl

theorem cell23_7039330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_7039330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039330 prefixEnd_7039330 := by exact prefixLift 7039330
  have htrace : WordTrace (prefixWord ++ tailWord_7039330) baseStart_7039330 baseEnd_7039330 := by
    simpa [prefixWord, tailWord_7039330, baseEnd_7039330] using wordTrace_append hprefix tailTrace_7039330
  have hstable : (prefixWord ++ tailWord_7039330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039330).length < 2 ^ (prefixWord ++ tailWord_7039330).sum := by decide
  have hdescent : baseEnd_7039330 < baseStart_7039330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039339 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 3]
def baseStart_7039339 : Nat := 118140960795 + 7039339 * 2 ^ 59
def prefixEnd_7039339 : Nat := 4983230072969 + 3 ^ 40 * 7039339 * 2
def baseEnd_7039339 : Nat := 3614564396939939287489175

theorem tailTrace_7039339 : CollatzResearch.WordTrace tailWord_7039339 prefixEnd_7039339 3614564396939939287489175 := by
  unfold tailWord_7039339
  simp only [CollatzResearch.WordTrace]
  refine ⟨256745785844684501232417071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171163857229789667488278047 256745785844684501232417071)
  ·
    refine ⟨385118678767026751848625607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256745785844684501232417071 385118678767026751848625607)
    ·
      refine ⟨577678018150540127772938411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385118678767026751848625607 577678018150540127772938411)
      ·
        refine ⟨866517027225810191659407617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577678018150540127772938411 866517027225810191659407617)
        ·
          refine ⟨649887770419357643744555713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866517027225810191659407617 649887770419357643744555713)
          ·
            refine ⟨487415827814518232808416785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649887770419357643744555713 487415827814518232808416785)
            ·
              refine ⟨365561870860888674606312589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487415827814518232808416785 365561870860888674606312589)
              ·
                refine ⟨137085701572833252977367221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365561870860888674606312589 137085701572833252977367221)
                ·
                  refine ⟨12851784522453117466628177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137085701572833252977367221 12851784522453117466628177)
                  ·
                    refine ⟨9638838391839838099971133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12851784522453117466628177 9638838391839838099971133)
                    ·
                      refine ⟨3614564396939939287489175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9638838391839838099971133 3614564396939939287489175)
                      ·
                        rfl

theorem cell23_7039339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 3].length) (baseStart_7039339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039339 prefixEnd_7039339 := by exact prefixLift 7039339
  have htrace : WordTrace (prefixWord ++ tailWord_7039339) baseStart_7039339 baseEnd_7039339 := by
    simpa [prefixWord, tailWord_7039339, baseEnd_7039339] using wordTrace_append hprefix tailTrace_7039339
  have hstable : (prefixWord ++ tailWord_7039339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039339).length < 2 ^ (prefixWord ++ tailWord_7039339).sum := by decide
  have hdescent : baseEnd_7039339 < baseStart_7039339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039356 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_7039356 : Nat := 118140960795 + 7039356 * 2 ^ 59
def prefixEnd_7039356 : Nat := 4983230072969 + 3 ^ 40 * 7039356 * 2
def baseEnd_7039356 : Nat := 3614573126111065720976597

theorem tailTrace_7039356 : CollatzResearch.WordTrace tailWord_7039356 prefixEnd_7039356 3614573126111065720976597 := by
  unfold tailWord_7039356
  simp only [CollatzResearch.WordTrace]
  refine ⟨128373202942811456567892961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171164270590415275423857281 128373202942811456567892961)
  ·
    refine ⟨96279902207108592425919721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128373202942811456567892961 96279902207108592425919721)
    ·
      refine ⟨72209926655331444319439791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96279902207108592425919721 72209926655331444319439791)
      ·
        refine ⟨108314889982997166479159687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72209926655331444319439791 108314889982997166479159687)
        ·
          refine ⟨162472334974495749718739531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108314889982997166479159687 162472334974495749718739531)
          ·
            refine ⟨243708502461743624578109297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162472334974495749718739531 243708502461743624578109297)
            ·
              refine ⟨182781376846307718433581973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243708502461743624578109297 182781376846307718433581973)
              ·
                refine ⟨8567877039670674301574155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182781376846307718433581973 8567877039670674301574155)
                ·
                  refine ⟨12851815559506011452361233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8567877039670674301574155 12851815559506011452361233)
                  ·
                    refine ⟨9638861669629508589270925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12851815559506011452361233 9638861669629508589270925)
                    ·
                      refine ⟨3614573126111065720976597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9638861669629508589270925 3614573126111065720976597)
                      ·
                        rfl

theorem cell23_7039356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_7039356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039356 prefixEnd_7039356 := by exact prefixLift 7039356
  have htrace : WordTrace (prefixWord ++ tailWord_7039356) baseStart_7039356 baseEnd_7039356 := by
    simpa [prefixWord, tailWord_7039356, baseEnd_7039356] using wordTrace_append hprefix tailTrace_7039356
  have hstable : (prefixWord ++ tailWord_7039356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039356).length < 2 ^ (prefixWord ++ tailWord_7039356).sum := by decide
  have hdescent : baseEnd_7039356 < baseStart_7039356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039380 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_7039380 : Nat := 118140960795 + 7039380 * 2 ^ 59
def prefixEnd_7039380 : Nat := 4983230072969 + 3 ^ 40 * 7039380 * 2
def baseEnd_7039380 : Nat := 1204861816548924542358829

theorem tailTrace_7039380 : CollatzResearch.WordTrace tailWord_7039380 prefixEnd_7039380 1204861816548924542358829 := by
  unfold tailWord_7039380
  simp only [CollatzResearch.WordTrace]
  refine ⟨128373640618767982617329797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171164854158357310156439729 128373640618767982617329797)
  ·
    refine ⟨24070057616018996740749337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128373640618767982617329797 24070057616018996740749337)
    ·
      refine ⟨18052543212014247555562003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24070057616018996740749337 18052543212014247555562003)
      ·
        refine ⟨27078814818021371333343005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18052543212014247555562003 27078814818021371333343005)
        ·
          refine ⟨10154555556758014250003627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27078814818021371333343005 10154555556758014250003627)
          ·
            refine ⟨15231833335137021375005441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10154555556758014250003627 15231833335137021375005441)
            ·
              refine ⟨11423875001352766031254081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15231833335137021375005441 11423875001352766031254081)
              ·
                refine ⟨8567906251014574523440561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11423875001352766031254081 8567906251014574523440561)
                ·
                  refine ⟨6425929688260930892580421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8567906251014574523440561 6425929688260930892580421)
                  ·
                    refine ⟨1204861816548924542358829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6425929688260930892580421 1204861816548924542358829)
                    ·
                      rfl

theorem cell23_7039380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_7039380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039380 prefixEnd_7039380 := by exact prefixLift 7039380
  have htrace : WordTrace (prefixWord ++ tailWord_7039380) baseStart_7039380 baseEnd_7039380 := by
    simpa [prefixWord, tailWord_7039380, baseEnd_7039380] using wordTrace_append hprefix tailTrace_7039380
  have hstable : (prefixWord ++ tailWord_7039380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039380).length < 2 ^ (prefixWord ++ tailWord_7039380).sum := by decide
  have hdescent : baseEnd_7039380 < baseStart_7039380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039393 : List Nat := [1, 2, 3, 5, 1, 2, 1, 8]
def baseStart_7039393 : Nat := 118140960795 + 7039393 * 2 ^ 59
def prefixEnd_7039393 : Nat := 4983230072969 + 3 ^ 40 * 7039393 * 2
def baseEnd_7039393 : Nat := 133873782403528965785701

theorem tailTrace_7039393 : CollatzResearch.WordTrace tailWord_7039393 prefixEnd_7039393 133873782403528965785701 := by
  unfold tailWord_7039393
  simp only [CollatzResearch.WordTrace]
  refine ⟨256747755386488868454882833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171165170257659245636588555 256747755386488868454882833)
  ·
    refine ⟨192560816539866651341162125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256747755386488868454882833 192560816539866651341162125)
    ·
      refine ⟨72210306202449994252935797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192560816539866651341162125 72210306202449994252935797)
      ·
        refine ⟨6769716206479686961212731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72210306202449994252935797 6769716206479686961212731)
        ·
          refine ⟨10154574309719530441819097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6769716206479686961212731 10154574309719530441819097)
          ·
            refine ⟨7615930732289647831364323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10154574309719530441819097 7615930732289647831364323)
            ·
              refine ⟨11423896098434471747046485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7615930732289647831364323 11423896098434471747046485)
              ·
                refine ⟨133873782403528965785701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11423896098434471747046485 133873782403528965785701)
                ·
                  rfl

theorem cell23_7039393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 8].length) (baseStart_7039393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039393 prefixEnd_7039393 := by exact prefixLift 7039393
  have htrace : WordTrace (prefixWord ++ tailWord_7039393) baseStart_7039393 baseEnd_7039393 := by
    simpa [prefixWord, tailWord_7039393, baseEnd_7039393] using wordTrace_append hprefix tailTrace_7039393
  have hstable : (prefixWord ++ tailWord_7039393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039393).length < 2 ^ (prefixWord ++ tailWord_7039393).sum := by decide
  have hdescent : baseEnd_7039393 < baseStart_7039393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039466 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 7]
def baseStart_7039466 : Nat := 118140960795 + 7039466 * 2 ^ 59
def prefixEnd_7039466 : Nat := 4983230072969 + 3 ^ 40 * 7039466 * 2
def baseEnd_7039466 : Nat := 401625512109228921177899

theorem tailTrace_7039466 : CollatzResearch.WordTrace tailWord_7039466 prefixEnd_7039466 401625512109228921177899 := by
  unfold tailWord_7039466
  simp only [CollatzResearch.WordTrace]
  refine ⟨64187604478806100480572563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171166945276816267948193501 64187604478806100480572563)
  ·
    refine ⟨96281406718209150720858845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64187604478806100480572563 96281406718209150720858845)
    ·
      refine ⟨36105527519328431520322067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96281406718209150720858845 36105527519328431520322067)
      ·
        refine ⟨54158291278992647280483101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36105527519328431520322067 54158291278992647280483101)
        ·
          refine ⟨20309359229622242730181163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54158291278992647280483101 20309359229622242730181163)
          ·
            refine ⟨30464038844433364095271745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20309359229622242730181163 30464038844433364095271745)
            ·
              refine ⟨22848029133325023071453809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30464038844433364095271745 22848029133325023071453809)
              ·
                refine ⟨17136021849993767303590357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22848029133325023071453809 17136021849993767303590357)
                ·
                  refine ⟨401625512109228921177899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17136021849993767303590357 401625512109228921177899)
                  ·
                    rfl

theorem cell23_7039466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_7039466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039466 prefixEnd_7039466 := by exact prefixLift 7039466
  have htrace : WordTrace (prefixWord ++ tailWord_7039466) baseStart_7039466 baseEnd_7039466 := by
    simpa [prefixWord, tailWord_7039466, baseEnd_7039466] using wordTrace_append hprefix tailTrace_7039466
  have hstable : (prefixWord ++ tailWord_7039466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039466).length < 2 ^ (prefixWord ++ tailWord_7039466).sum := by decide
  have hdescent : baseEnd_7039466 < baseStart_7039466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039500 : List Nat := [2, 2, 1, 2, 4, 2, 3, 2, 5]
def baseStart_7039500 : Nat := 118140960795 + 7039500 * 2 ^ 59
def prefixEnd_7039500 : Nat := 4983230072969 + 3 ^ 40 * 7039500 * 2
def baseEnd_7039500 : Nat := 401627451925034795286215

theorem tailTrace_7039500 : CollatzResearch.WordTrace tailWord_7039500 prefixEnd_7039500 401627451925034795286215 := by
  unfold tailWord_7039500
  simp only [CollatzResearch.WordTrace]
  refine ⟨128375828998550612864513977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171167771998067483819351969 128375828998550612864513977)
  ·
    refine ⟨96281871748912959648385483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128375828998550612864513977 96281871748912959648385483)
    ·
      refine ⟨144422807623369439472578225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96281871748912959648385483 144422807623369439472578225)
      ·
        refine ⟨108317105717527079604433669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144422807623369439472578225 108317105717527079604433669)
        ·
          refine ⟨20309457322036327425831313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108317105717527079604433669 20309457322036327425831313)
          ·
            refine ⟨15232092991527245569373485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20309457322036327425831313 15232092991527245569373485)
            ·
              refine ⟨5712034871822717088515057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15232092991527245569373485 5712034871822717088515057)
              ·
                refine ⟨4284026153867037816386293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5712034871822717088515057 4284026153867037816386293)
                ·
                  refine ⟨401627451925034795286215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4284026153867037816386293 401627451925034795286215)
                  ·
                    rfl

theorem cell23_7039500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_7039500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039500 prefixEnd_7039500 := by exact prefixLift 7039500
  have htrace : WordTrace (prefixWord ++ tailWord_7039500) baseStart_7039500 baseEnd_7039500 := by
    simpa [prefixWord, tailWord_7039500, baseEnd_7039500] using wordTrace_append hprefix tailTrace_7039500
  have hstable : (prefixWord ++ tailWord_7039500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039500).length < 2 ^ (prefixWord ++ tailWord_7039500).sum := by decide
  have hdescent : baseEnd_7039500 < baseStart_7039500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039511 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7039511 : Nat := 118140960795 + 7039511 * 2 ^ 59
def prefixEnd_7039511 : Nat := 4983230072969 + 3 ^ 40 * 7039511 * 2
def baseEnd_7039511 : Nat := 3614652715612512614538385

theorem tailTrace_7039511 : CollatzResearch.WordTrace tailWord_7039511 prefixEnd_7039511 3614652715612512614538385 := by
  unfold tailWord_7039511
  simp only [CollatzResearch.WordTrace]
  refine ⟨256752059200061374607678387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171168039466707583071785591 256752059200061374607678387)
  ·
    refine ⟨385128088800092061911517581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256752059200061374607678387 385128088800092061911517581)
    ·
      refine ⟨144423033300034523216819093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385128088800092061911517581 144423033300034523216819093)
      ·
        refine ⟨6769829685939118275788395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144423033300034523216819093 6769829685939118275788395)
        ·
          refine ⟨10154744528908677413682593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6769829685939118275788395 10154744528908677413682593)
          ·
            refine ⟨7616058396681508060261945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10154744528908677413682593 7616058396681508060261945)
            ·
              refine ⟨5712043797511131045196459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7616058396681508060261945 5712043797511131045196459)
              ·
                refine ⟨8568065696266696567794689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712043797511131045196459 8568065696266696567794689)
                ·
                  refine ⟨6426049272200022425846017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8568065696266696567794689 6426049272200022425846017)
                  ·
                    refine ⟨4819536954150016819384513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6426049272200022425846017 4819536954150016819384513)
                    ·
                      refine ⟨3614652715612512614538385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819536954150016819384513 3614652715612512614538385)
                      ·
                        rfl

theorem cell23_7039511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7039511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039511 prefixEnd_7039511 := by exact prefixLift 7039511
  have htrace : WordTrace (prefixWord ++ tailWord_7039511) baseStart_7039511 baseEnd_7039511 := by
    simpa [prefixWord, tailWord_7039511, baseEnd_7039511] using wordTrace_append hprefix tailTrace_7039511
  have hstable : (prefixWord ++ tailWord_7039511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039511).length < 2 ^ (prefixWord ++ tailWord_7039511).sum := by decide
  have hdescent : baseEnd_7039511 < baseStart_7039511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039536 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 3]
def baseStart_7039536 : Nat := 118140960795 + 7039536 * 2 ^ 59
def prefixEnd_7039536 : Nat := 4983230072969 + 3 ^ 40 * 7039536 * 2
def baseEnd_7039536 : Nat := 3614665552628875016725769

theorem tailTrace_7039536 : CollatzResearch.WordTrace tailWord_7039536 prefixEnd_7039536 3614665552628875016725769 := by
  unfold tailWord_7039536
  simp only [CollatzResearch.WordTrace]
  refine ⟨128376485512485401938669231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171168647349980535918225641 128376485512485401938669231)
  ·
    refine ⟨192564728268728102908003847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128376485512485401938669231 192564728268728102908003847)
    ·
      refine ⟨288847092403092154362005771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192564728268728102908003847 288847092403092154362005771)
      ·
        refine ⟨433270638604638231543008657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288847092403092154362005771 433270638604638231543008657)
        ·
          refine ⟨324952978953478673657256493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433270638604638231543008657 324952978953478673657256493)
          ·
            refine ⟨121857367107554502621471185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324952978953478673657256493 121857367107554502621471185)
            ·
              refine ⟨91393025330665876966103389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121857367107554502621471185 91393025330665876966103389)
              ·
                refine ⟨34272384498999703862288771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91393025330665876966103389 34272384498999703862288771)
                ·
                  refine ⟨51408576748499555793433157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34272384498999703862288771 51408576748499555793433157)
                  ·
                    refine ⟨9639108140343666711268717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51408576748499555793433157 9639108140343666711268717)
                    ·
                      refine ⟨3614665552628875016725769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9639108140343666711268717 3614665552628875016725769)
                      ·
                        rfl

theorem cell23_7039536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 3].length) (baseStart_7039536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039536 prefixEnd_7039536 := by exact prefixLift 7039536
  have htrace : WordTrace (prefixWord ++ tailWord_7039536) baseStart_7039536 baseEnd_7039536 := by
    simpa [prefixWord, tailWord_7039536, baseEnd_7039536] using wordTrace_append hprefix tailTrace_7039536
  have hstable : (prefixWord ++ tailWord_7039536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039536).length < 2 ^ (prefixWord ++ tailWord_7039536).sum := by decide
  have hdescent : baseEnd_7039536 < baseStart_7039536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039617 : List Nat := [1, 2, 4, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_7039617 : Nat := 118140960795 + 7039617 * 2 ^ 59
def prefixEnd_7039617 : Nat := 4983230072969 + 3 ^ 40 * 7039617 * 2
def baseEnd_7039617 : Nat := 3614707144561889199812897

theorem tailTrace_7039617 : CollatzResearch.WordTrace tailWord_7039617 prefixEnd_7039617 3614707144561889199812897 := by
  unfold tailWord_7039617
  simp only [CollatzResearch.WordTrace]
  refine ⟨256755925337677354711037105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171170616891784903140691403 256755925337677354711037105)
  ·
    refine ⟨192566944003258016033277829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256755925337677354711037105 192566944003258016033277829)
    ·
      refine ⟨36106302000610878006239593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192566944003258016033277829 36106302000610878006239593)
      ·
        refine ⟨27079726500458158504679695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36106302000610878006239593 27079726500458158504679695)
        ·
          refine ⟨40619589750687237757019543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27079726500458158504679695 40619589750687237757019543)
          ·
            refine ⟨60929384626030856635529315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40619589750687237757019543 60929384626030856635529315)
            ·
              refine ⟨91394076939046284953293973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60929384626030856635529315 91394076939046284953293973)
              ·
                refine ⟨4284097356517794607185655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91394076939046284953293973 4284097356517794607185655)
                ·
                  refine ⟨6426146034776691910778483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4284097356517794607185655 6426146034776691910778483)
                  ·
                    refine ⟨9639219052165037866167725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6426146034776691910778483 9639219052165037866167725)
                    ·
                      refine ⟨3614707144561889199812897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9639219052165037866167725 3614707144561889199812897)
                      ·
                        rfl

theorem cell23_7039617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_7039617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039617 prefixEnd_7039617 := by exact prefixLift 7039617
  have htrace : WordTrace (prefixWord ++ tailWord_7039617) baseStart_7039617 baseEnd_7039617 := by
    simpa [prefixWord, tailWord_7039617, baseEnd_7039617] using wordTrace_append hprefix tailTrace_7039617
  have hstable : (prefixWord ++ tailWord_7039617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039617).length < 2 ^ (prefixWord ++ tailWord_7039617).sum := by decide
  have hdescent : baseEnd_7039617 < baseStart_7039617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039640 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 1, 1, 4]
def baseStart_7039640 : Nat := 118140960795 + 7039640 * 2 ^ 59
def prefixEnd_7039640 : Nat := 4983230072969 + 3 ^ 40 * 7039640 * 2
def baseEnd_7039640 : Nat := 3614718954616942609825291

theorem tailTrace_7039640 : CollatzResearch.WordTrace tailWord_7039640 prefixEnd_7039640 3614718954616942609825291 := by
  unfold tailWord_7039640
  simp only [CollatzResearch.WordTrace]
  refine ⟨128378382108297014819562187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171171176144396019759416249 128378382108297014819562187)
  ·
    refine ⟨192567573162445522229343281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128378382108297014819562187 192567573162445522229343281)
    ·
      refine ⟨144425679871834141672007461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192567573162445522229343281 144425679871834141672007461)
      ·
        refine ⟨27079814975968901563501399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144425679871834141672007461 27079814975968901563501399)
        ·
          refine ⟨40619722463953352345252099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27079814975968901563501399 40619722463953352345252099)
          ·
            refine ⟨60929583695930028517878149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40619722463953352345252099 60929583695930028517878149)
            ·
              refine ⟨11424296942986880347102153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60929583695930028517878149 11424296942986880347102153)
              ·
                refine ⟨8568222707240160260326615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11424296942986880347102153 8568222707240160260326615)
                ·
                  refine ⟨12852334060860240390489923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8568222707240160260326615 12852334060860240390489923)
                  ·
                    refine ⟨19278501091290360585734885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12852334060860240390489923 19278501091290360585734885)
                    ·
                      refine ⟨3614718954616942609825291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19278501091290360585734885 3614718954616942609825291)
                      ·
                        rfl

theorem cell23_7039640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_7039640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039640 prefixEnd_7039640 := by exact prefixLift 7039640
  have htrace : WordTrace (prefixWord ++ tailWord_7039640) baseStart_7039640 baseEnd_7039640 := by
    simpa [prefixWord, tailWord_7039640, baseEnd_7039640] using wordTrace_append hprefix tailTrace_7039640
  have hstable : (prefixWord ++ tailWord_7039640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039640).length < 2 ^ (prefixWord ++ tailWord_7039640).sum := by decide
  have hdescent : baseEnd_7039640 < baseStart_7039640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039684 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_7039684 : Nat := 118140960795 + 7039684 * 2 ^ 59
def prefixEnd_7039684 : Nat := 4983230072969 + 3 ^ 40 * 7039684 * 2
def baseEnd_7039684 : Nat := 1204913849255246812558363

theorem tailTrace_7039684 : CollatzResearch.WordTrace tailWord_7039684 prefixEnd_7039684 1204913849255246812558363 := by
  unfold tailWord_7039684
  simp only [CollatzResearch.WordTrace]
  refine ⟨128379184514217312576863053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171172246018956416769150737 128379184514217312576863053)
  ·
    refine ⟨48142194192831492216323645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128379184514217312576863053 48142194192831492216323645)
    ·
      refine ⟨18053322822311809581121367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48142194192831492216323645 18053322822311809581121367)
      ·
        refine ⟨27079984233467714371682051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18053322822311809581121367 27079984233467714371682051)
        ·
          refine ⟨40619976350201571557523077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27079984233467714371682051 40619976350201571557523077)
          ·
            refine ⟨7616245565662794667035577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40619976350201571557523077 7616245565662794667035577)
            ·
              refine ⟨5712184174247096000276683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7616245565662794667035577 5712184174247096000276683)
              ·
                refine ⟨8568276261370644000415025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712184174247096000276683 8568276261370644000415025)
                ·
                  refine ⟨6426207196027983000311269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8568276261370644000415025 6426207196027983000311269)
                  ·
                    refine ⟨1204913849255246812558363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6426207196027983000311269 1204913849255246812558363)
                    ·
                      rfl

theorem cell23_7039684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_7039684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039684 prefixEnd_7039684 := by exact prefixLift 7039684
  have htrace : WordTrace (prefixWord ++ tailWord_7039684) baseStart_7039684 baseEnd_7039684 := by
    simpa [prefixWord, tailWord_7039684, baseEnd_7039684] using wordTrace_append hprefix tailTrace_7039684
  have hstable : (prefixWord ++ tailWord_7039684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039684).length < 2 ^ (prefixWord ++ tailWord_7039684).sum := by decide
  have hdescent : baseEnd_7039684 < baseStart_7039684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039763 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 3]
def baseStart_7039763 : Nat := 118140960795 + 7039763 * 2 ^ 59
def prefixEnd_7039763 : Nat := 4983230072969 + 3 ^ 40 * 7039763 * 2
def baseEnd_7039763 : Nat := 3614782112737445628587225

theorem tailTrace_7039763 : CollatzResearch.WordTrace tailWord_7039763 prefixEnd_7039763 3614782112737445628587225 := by
  unfold tailWord_7039763
  simp only [CollatzResearch.WordTrace]
  refine ⟨256761250395148421645851943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171174166930098947763901295 256761250395148421645851943)
  ·
    refine ⟨385141875592722632468777915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256761250395148421645851943 385141875592722632468777915)
    ·
      refine ⟨577712813389083948703166873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385141875592722632468777915 577712813389083948703166873)
      ·
        refine ⟨433284610041812961527375155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577712813389083948703166873 433284610041812961527375155)
        ·
          refine ⟨649926915062719442291062733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433284610041812961527375155 649926915062719442291062733)
          ·
            refine ⟨243722593148519790859148525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 649926915062719442291062733 243722593148519790859148525)
            ·
              refine ⟨91395972430694921572180697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243722593148519790859148525 91395972430694921572180697)
              ·
                refine ⟨68546979323021191179135523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91395972430694921572180697 68546979323021191179135523)
                ·
                  refine ⟨102820468984531786768703285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68546979323021191179135523 102820468984531786768703285)
                  ·
                    refine ⟨9639418967299855009565933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102820468984531786768703285 9639418967299855009565933)
                    ·
                      refine ⟨3614782112737445628587225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9639418967299855009565933 3614782112737445628587225)
                      ·
                        rfl

theorem cell23_7039763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 3].length) (baseStart_7039763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039763 prefixEnd_7039763 := by exact prefixLift 7039763
  have htrace : WordTrace (prefixWord ++ tailWord_7039763) baseStart_7039763 baseEnd_7039763 := by
    simpa [prefixWord, tailWord_7039763, baseEnd_7039763] using wordTrace_append hprefix tailTrace_7039763
  have hstable : (prefixWord ++ tailWord_7039763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039763).length < 2 ^ (prefixWord ++ tailWord_7039763).sum := by decide
  have hdescent : baseEnd_7039763 < baseStart_7039763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039793 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_7039793 : Nat := 118140960795 + 7039793 * 2 ^ 59
def prefixEnd_7039793 : Nat := 4983230072969 + 3 ^ 40 * 7039793 * 2
def baseEnd_7039793 : Nat := 3614797517157080511212087

theorem tailTrace_7039793 : CollatzResearch.WordTrace tailWord_7039793 prefixEnd_7039793 3614797517157080511212087 := by
  unfold tailWord_7039793
  simp only [CollatzResearch.WordTrace]
  refine ⟨256762344585039736769444033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171174896390026491179629355 256762344585039736769444033)
  ·
    refine ⟨192571758438779802577083025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256762344585039736769444033 192571758438779802577083025)
    ·
      refine ⟨144428818829084851932812269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192571758438779802577083025 144428818829084851932812269)
      ·
        refine ⟨54160807060906819474804601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144428818829084851932812269 54160807060906819474804601)
        ·
          refine ⟨40620605295680114606103451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54160807060906819474804601 40620605295680114606103451)
          ·
            refine ⟨60930907943520171909155177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40620605295680114606103451 60930907943520171909155177)
            ·
              refine ⟨45698180957640128931866383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60930907943520171909155177 45698180957640128931866383)
              ·
                refine ⟨68547271436460193397799575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45698180957640128931866383 68547271436460193397799575)
                ·
                  refine ⟨102820907154690290096699363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68547271436460193397799575 102820907154690290096699363)
                  ·
                    refine ⟨154231360732035435145049045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102820907154690290096699363 154231360732035435145049045)
                    ·
                      refine ⟨3614797517157080511212087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154231360732035435145049045 3614797517157080511212087)
                      ·
                        rfl

theorem cell23_7039793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_7039793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039793 prefixEnd_7039793 := by exact prefixLift 7039793
  have htrace : WordTrace (prefixWord ++ tailWord_7039793) baseStart_7039793 baseEnd_7039793 := by
    simpa [prefixWord, tailWord_7039793, baseEnd_7039793] using wordTrace_append hprefix tailTrace_7039793
  have hstable : (prefixWord ++ tailWord_7039793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039793).length < 2 ^ (prefixWord ++ tailWord_7039793).sum := by decide
  have hdescent : baseEnd_7039793 < baseStart_7039793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039798 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_7039798 : Nat := 118140960795 + 7039798 * 2 ^ 59
def prefixEnd_7039798 : Nat := 4983230072969 + 3 ^ 40 * 7039798 * 2
def baseEnd_7039798 : Nat := 3614800084560352991649565

theorem tailTrace_7039798 : CollatzResearch.WordTrace tailWord_7039798 prefixEnd_7039798 3614800084560352991649565 := by
  unfold tailWord_7039798
  simp only [CollatzResearch.WordTrace]
  refine ⟨16047657934376351413961003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171175017966681081748917365 16047657934376351413961003)
  ·
    refine ⟨24071486901564527120941505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16047657934376351413961003 24071486901564527120941505)
    ·
      refine ⟨18053615176173395340706129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24071486901564527120941505 18053615176173395340706129)
      ·
        refine ⟨13540211382130046505529597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18053615176173395340706129 13540211382130046505529597)
        ·
          refine ⟨5077579268298767439573599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13540211382130046505529597 5077579268298767439573599)
          ·
            refine ⟨7616368902448151159360399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077579268298767439573599 7616368902448151159360399)
            ·
              refine ⟨11424553353672226739040599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616368902448151159360399 11424553353672226739040599)
              ·
                refine ⟨17136830030508340108560899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11424553353672226739040599 17136830030508340108560899)
                ·
                  refine ⟨25705245045762510162841349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17136830030508340108560899 25705245045762510162841349)
                  ·
                    refine ⟨4819733446080470655532753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25705245045762510162841349 4819733446080470655532753)
                    ·
                      refine ⟨3614800084560352991649565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819733446080470655532753 3614800084560352991649565)
                      ·
                        rfl

theorem cell23_7039798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_7039798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039798 prefixEnd_7039798 := by exact prefixLift 7039798
  have htrace : WordTrace (prefixWord ++ tailWord_7039798) baseStart_7039798 baseEnd_7039798 := by
    simpa [prefixWord, tailWord_7039798, baseEnd_7039798] using wordTrace_append hprefix tailTrace_7039798
  have hstable : (prefixWord ++ tailWord_7039798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039798).length < 2 ^ (prefixWord ++ tailWord_7039798).sum := by decide
  have hdescent : baseEnd_7039798 < baseStart_7039798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039820 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7039820 : Nat := 118140960795 + 7039820 * 2 ^ 59
def prefixEnd_7039820 : Nat := 4983230072969 + 3 ^ 40 * 7039820 * 2
def baseEnd_7039820 : Nat := 3614811381134751905574463

theorem tailTrace_7039820 : CollatzResearch.WordTrace tailWord_7039820 prefixEnd_7039820 3614811381134751905574463 := by
  unfold tailWord_7039820
  simp only [CollatzResearch.WordTrace]
  refine ⟨128381664677970960190338457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171175552903961280253784609 128381664677970960190338457)
  ·
    refine ⟨96286248508478220142753843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128381664677970960190338457 96286248508478220142753843)
    ·
      refine ⟨144429372762717330214130765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96286248508478220142753843 144429372762717330214130765)
      ·
        refine ⟨54161014786018998830299037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144429372762717330214130765 54161014786018998830299037)
        ·
          refine ⟨20310380544757124561362139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54161014786018998830299037 20310380544757124561362139)
          ·
            refine ⟨30465570817135686842043209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20310380544757124561362139 30465570817135686842043209)
            ·
              refine ⟨22849178112851765131532407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30465570817135686842043209 22849178112851765131532407)
              ·
                refine ⟨34273767169277647697298611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22849178112851765131532407 34273767169277647697298611)
                ·
                  refine ⟨51410650753916471545947917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34273767169277647697298611 51410650753916471545947917)
                  ·
                    refine ⟨19278994032718676829730469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51410650753916471545947917 19278994032718676829730469)
                    ·
                      refine ⟨3614811381134751905574463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19278994032718676829730469 3614811381134751905574463)
                      ·
                        rfl

theorem cell23_7039820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7039820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039820 prefixEnd_7039820 := by exact prefixLift 7039820
  have htrace : WordTrace (prefixWord ++ tailWord_7039820) baseStart_7039820 baseEnd_7039820 := by
    simpa [prefixWord, tailWord_7039820, baseEnd_7039820] using wordTrace_append hprefix tailTrace_7039820
  have hstable : (prefixWord ++ tailWord_7039820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039820).length < 2 ^ (prefixWord ++ tailWord_7039820).sum := by decide
  have hdescent : baseEnd_7039820 < baseStart_7039820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039821 : List Nat := [1, 6, 1, 2, 2, 2, 1, 3, 5]
def baseStart_7039821 : Nat := 118140960795 + 7039821 * 2 ^ 59
def prefixEnd_7039821 : Nat := 4983230072969 + 3 ^ 40 * 7039821 * 2
def baseEnd_7039821 : Nat := 401645766068378489073551

theorem tailTrace_7039821 : CollatzResearch.WordTrace tailWord_7039821 prefixEnd_7039821 401645766068378489073551 := by
  unfold tailWord_7039821
  simp only [CollatzResearch.WordTrace]
  refine ⟨256763365828938297551463317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171175577219292198367642211 256763365828938297551463317)
  ·
    refine ⟨12035782773231482697724843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 256763365828938297551463317 12035782773231482697724843)
    ·
      refine ⟨18053674159847224046587265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12035782773231482697724843 18053674159847224046587265)
      ·
        refine ⟨13540255619885418034940449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18053674159847224046587265 13540255619885418034940449)
        ·
          refine ⟨10155191714914063526205337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13540255619885418034940449 10155191714914063526205337)
          ·
            refine ⟨7616393786185547644654003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10155191714914063526205337 7616393786185547644654003)
            ·
              refine ⟨11424590679278321466981005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616393786185547644654003 11424590679278321466981005)
              ·
                refine ⟨4284221504729370550117877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11424590679278321466981005 4284221504729370550117877)
                ·
                  refine ⟨401645766068378489073551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4284221504729370550117877 401645766068378489073551)
                  ·
                    rfl

theorem cell23_7039821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_7039821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039821 prefixEnd_7039821 := by exact prefixLift 7039821
  have htrace : WordTrace (prefixWord ++ tailWord_7039821) baseStart_7039821 baseEnd_7039821 := by
    simpa [prefixWord, tailWord_7039821, baseEnd_7039821] using wordTrace_append hprefix tailTrace_7039821
  have hstable : (prefixWord ++ tailWord_7039821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039821).length < 2 ^ (prefixWord ++ tailWord_7039821).sum := by decide
  have hdescent : baseEnd_7039821 < baseStart_7039821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039847 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 3, 4]
def baseStart_7039847 : Nat := 118140960795 + 7039847 * 2 ^ 59
def prefixEnd_7039847 : Nat := 4983230072969 + 3 ^ 40 * 7039847 * 2
def baseEnd_7039847 : Nat := 1204941748370807766645613

theorem tailTrace_7039847 : CollatzResearch.WordTrace tailWord_7039847 prefixEnd_7039847 1204941748370807766645613 := by
  unfold tailWord_7039847
  simp only [CollatzResearch.WordTrace]
  refine ⟨256764314126844103991909795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171176209417896069327939863 256764314126844103991909795)
  ·
    refine ⟨385146471190266155987864693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256764314126844103991909795 385146471190266155987864693)
    ·
      refine ⟨36107481674087452123862315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 385146471190266155987864693 36107481674087452123862315)
      ·
        refine ⟨54161222511131178185793473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36107481674087452123862315 54161222511131178185793473)
        ·
          refine ⟨40620916883348383639345105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54161222511131178185793473 40620916883348383639345105)
          ·
            refine ⟨30465687662511287729508829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40620916883348383639345105 30465687662511287729508829)
            ·
              refine ⟨11424632873441732898565811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30465687662511287729508829 11424632873441732898565811)
              ·
                refine ⟨17136949310162599347848717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11424632873441732898565811 17136949310162599347848717)
                ·
                  refine ⟨6426355991310974755443269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17136949310162599347848717 6426355991310974755443269)
                  ·
                    refine ⟨1204941748370807766645613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6426355991310974755443269 1204941748370807766645613)
                    ·
                      rfl

theorem cell23_7039847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_7039847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039847 prefixEnd_7039847 := by exact prefixLift 7039847
  have htrace : WordTrace (prefixWord ++ tailWord_7039847) baseStart_7039847 baseEnd_7039847 := by
    simpa [prefixWord, tailWord_7039847, baseEnd_7039847] using wordTrace_append hprefix tailTrace_7039847
  have hstable : (prefixWord ++ tailWord_7039847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039847).length < 2 ^ (prefixWord ++ tailWord_7039847).sum := by decide
  have hdescent : baseEnd_7039847 < baseStart_7039847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039863 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_7039863 : Nat := 118140960795 + 7039863 * 2 ^ 59
def prefixEnd_7039863 : Nat := 4983230072969 + 3 ^ 40 * 7039863 * 2
def baseEnd_7039863 : Nat := 3614833460802895237336765

theorem tailTrace_7039863 : CollatzResearch.WordTrace tailWord_7039863 prefixEnd_7039863 3614833460802895237336765 := by
  unfold tailWord_7039863
  simp only [CollatzResearch.WordTrace]
  refine ⟨256764897694786138724492243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171176598463190759149661495 256764897694786138724492243)
  ·
    refine ⟨385147346542179208086738365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256764897694786138724492243 385147346542179208086738365)
    ·
      refine ⟨144430254953317203032526887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385147346542179208086738365 144430254953317203032526887)
      ·
        refine ⟨216645382429975804548790331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144430254953317203032526887 216645382429975804548790331)
        ·
          refine ⟨324968073644963706823185497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216645382429975804548790331 324968073644963706823185497)
          ·
            refine ⟨243726055233722780117389123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324968073644963706823185497 243726055233722780117389123)
            ·
              refine ⟨365589082850584170176083685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243726055233722780117389123 365589082850584170176083685)
              ·
                refine ⟨68547953034484531908015691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365589082850584170176083685 68547953034484531908015691)
                ·
                  refine ⟨102821929551726797862023537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68547953034484531908015691 102821929551726797862023537)
                  ·
                    refine ⟨77116447163795098396517653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102821929551726797862023537 77116447163795098396517653)
                    ·
                      refine ⟨3614833460802895237336765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77116447163795098396517653 3614833460802895237336765)
                      ·
                        rfl

theorem cell23_7039863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_7039863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039863 prefixEnd_7039863 := by exact prefixLift 7039863
  have htrace : WordTrace (prefixWord ++ tailWord_7039863) baseStart_7039863 baseEnd_7039863 := by
    simpa [prefixWord, tailWord_7039863, baseEnd_7039863] using wordTrace_append hprefix tailTrace_7039863
  have hstable : (prefixWord ++ tailWord_7039863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039863).length < 2 ^ (prefixWord ++ tailWord_7039863).sum := by decide
  have hdescent : baseEnd_7039863 < baseStart_7039863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039898 : List Nat := [3, 1, 1, 4, 3, 2, 2, 2, 1, 4]
def baseStart_7039898 : Nat := 118140960795 + 7039898 * 2 ^ 59
def prefixEnd_7039898 : Nat := 4983230072969 + 3 ^ 40 * 7039898 * 2
def baseEnd_7039898 : Nat := 1204950477541934200133035

theorem tailTrace_7039898 : CollatzResearch.WordTrace tailWord_7039898 prefixEnd_7039898 1204950477541934200133035 := by
  unfold tailWord_7039898
  simp only [CollatzResearch.WordTrace]
  refine ⟨64191543562414834925504087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171177449499772893134677565 64191543562414834925504087)
  ·
    refine ⟨96287315343622252388256131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64191543562414834925504087 96287315343622252388256131)
    ·
      refine ⟨144430973015433378582384197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96287315343622252388256131 144430973015433378582384197)
      ·
        refine ⟨27080807440393758484197037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144430973015433378582384197 27080807440393758484197037)
        ·
          refine ⟨10155302790147659431573889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27080807440393758484197037 10155302790147659431573889)
          ·
            refine ⟨7616477092610744573680417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10155302790147659431573889 7616477092610744573680417)
            ·
              refine ⟨5712357819458058430260313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7616477092610744573680417 5712357819458058430260313)
              ·
                refine ⟨4284268364593543822695235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5712357819458058430260313 4284268364593543822695235)
                ·
                  refine ⟨6426402546890315734042853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4284268364593543822695235 6426402546890315734042853)
                  ·
                    refine ⟨1204950477541934200133035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6426402546890315734042853 1204950477541934200133035)
                    ·
                      rfl

theorem cell23_7039898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_7039898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039898 prefixEnd_7039898 := by exact prefixLift 7039898
  have htrace : WordTrace (prefixWord ++ tailWord_7039898) baseStart_7039898 baseEnd_7039898 := by
    simpa [prefixWord, tailWord_7039898, baseEnd_7039898] using wordTrace_append hprefix tailTrace_7039898
  have hstable : (prefixWord ++ tailWord_7039898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039898).length < 2 ^ (prefixWord ++ tailWord_7039898).sum := by decide
  have hdescent : baseEnd_7039898 < baseStart_7039898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039924 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_7039924 : Nat := 118140960795 + 7039924 * 2 ^ 59
def prefixEnd_7039924 : Nat := 4983230072969 + 3 ^ 40 * 7039924 * 2
def baseEnd_7039924 : Nat := 1204954927707606499557995

theorem tailTrace_7039924 : CollatzResearch.WordTrace tailWord_7039924 prefixEnd_7039924 1204954927707606499557995 := by
  unfold tailWord_7039924
  simp only [CollatzResearch.WordTrace]
  refine ⟨128383561273782573071231413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171178081698376764094975217 128383561273782573071231413)
  ·
    refine ⟨12035958869417116225427945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128383561273782573071231413 12035958869417116225427945)
    ·
      refine ⟨9026969152062837169070959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12035958869417116225427945 9026969152062837169070959)
      ·
        refine ⟨13540453728094255753606439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9026969152062837169070959 13540453728094255753606439)
        ·
          refine ⟨20310680592141383630409659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13540453728094255753606439 20310680592141383630409659)
          ·
            refine ⟨30466020888212075445614489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20310680592141383630409659 30466020888212075445614489)
            ·
              refine ⟨22849515666159056584210867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30466020888212075445614489 22849515666159056584210867)
              ·
                refine ⟨34274273499238584876316301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22849515666159056584210867 34274273499238584876316301)
                ·
                  refine ⟨12852852562214469328618613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34274273499238584876316301 12852852562214469328618613)
                  ·
                    refine ⟨1204954927707606499557995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12852852562214469328618613 1204954927707606499557995)
                    ·
                      rfl

theorem cell23_7039924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_7039924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039924 prefixEnd_7039924 := by exact prefixLift 7039924
  have htrace : WordTrace (prefixWord ++ tailWord_7039924) baseStart_7039924 baseEnd_7039924 := by
    simpa [prefixWord, tailWord_7039924, baseEnd_7039924] using wordTrace_append hprefix tailTrace_7039924
  have hstable : (prefixWord ++ tailWord_7039924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039924).length < 2 ^ (prefixWord ++ tailWord_7039924).sum := by decide
  have hdescent : baseEnd_7039924 < baseStart_7039924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039944 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_7039944 : Nat := 118140960795 + 7039944 * 2 ^ 59
def prefixEnd_7039944 : Nat := 4983230072969 + 3 ^ 40 * 7039944 * 2
def baseEnd_7039944 : Nat := 3614875052735909420423893

theorem tailTrace_7039944 : CollatzResearch.WordTrace tailWord_7039944 prefixEnd_7039944 3614875052735909420423893 := by
  unfold tailWord_7039944
  simp only [CollatzResearch.WordTrace]
  refine ⟨128383926003746344779095443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171178568004995126372127257 128383926003746344779095443)
  ·
    refine ⟨192575889005619517168643165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128383926003746344779095443 192575889005619517168643165)
    ·
      refine ⟨72215958377107318938241187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192575889005619517168643165 72215958377107318938241187)
      ·
        refine ⟨108323937565660978407361781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72215958377107318938241187 108323937565660978407361781)
        ·
          refine ⟨10155369146780716725690167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108323937565660978407361781 10155369146780716725690167)
          ·
            refine ⟨15233053720171075088535251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10155369146780716725690167 15233053720171075088535251)
            ·
              refine ⟨22849580580256612632802877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15233053720171075088535251 22849580580256612632802877)
              ·
                refine ⟨8568592717596229737301079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22849580580256612632802877 8568592717596229737301079)
                ·
                  refine ⟨12852889076394344605951619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8568592717596229737301079 12852889076394344605951619)
                  ·
                    refine ⟨19279333614591516908927429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12852889076394344605951619 19279333614591516908927429)
                    ·
                      refine ⟨3614875052735909420423893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19279333614591516908927429 3614875052735909420423893)
                      ·
                        rfl

theorem cell23_7039944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_7039944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039944 prefixEnd_7039944 := by exact prefixLift 7039944
  have htrace : WordTrace (prefixWord ++ tailWord_7039944) baseStart_7039944 baseEnd_7039944 := by
    simpa [prefixWord, tailWord_7039944, baseEnd_7039944] using wordTrace_append hprefix tailTrace_7039944
  have hstable : (prefixWord ++ tailWord_7039944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039944).length < 2 ^ (prefixWord ++ tailWord_7039944).sum := by decide
  have hdescent : baseEnd_7039944 < baseStart_7039944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039950 : List Nat := [4, 1, 1, 1, 2, 4, 10]
def baseStart_7039950 : Nat := 118140960795 + 7039950 * 2 ^ 59
def prefixEnd_7039950 : Nat := 4983230072969 + 3 ^ 40 * 7039950 * 2
def baseEnd_7039950 : Nat := 44628125106417733295665

theorem tailTrace_7039950 : CollatzResearch.WordTrace tailWord_7039950 prefixEnd_7039950 44628125106417733295665 := by
  unfold tailWord_7039950
  simp only [CollatzResearch.WordTrace]
  refine ⟨32096008855683869072863663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171178713896980635055272869 32096008855683869072863663)
  ·
    refine ⟨48144013283525803609295495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32096008855683869072863663 48144013283525803609295495)
    ·
      refine ⟨72216019925288705413943243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48144013283525803609295495 72216019925288705413943243)
      ·
        refine ⟨108324029887933058120914865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72216019925288705413943243 108324029887933058120914865)
        ·
          refine ⟨81243022415949793590686149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108324029887933058120914865 81243022415949793590686149)
          ·
            refine ⟨15233066702990586298253653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81243022415949793590686149 15233066702990586298253653)
            ·
              refine ⟨44628125106417733295665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15233066702990586298253653 44628125106417733295665)
              ·
                rfl

theorem cell23_7039950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 10].length) (baseStart_7039950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039950 prefixEnd_7039950 := by exact prefixLift 7039950
  have htrace : WordTrace (prefixWord ++ tailWord_7039950) baseStart_7039950 baseEnd_7039950 := by
    simpa [prefixWord, tailWord_7039950, baseEnd_7039950] using wordTrace_append hprefix tailTrace_7039950
  have hstable : (prefixWord ++ tailWord_7039950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039950).length < 2 ^ (prefixWord ++ tailWord_7039950).sum := by decide
  have hdescent : baseEnd_7039950 < baseStart_7039950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039954 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_7039954 : Nat := 118140960795 + 7039954 * 2 ^ 59
def prefixEnd_7039954 : Nat := 4983230072969 + 3 ^ 40 * 7039954 * 2
def baseEnd_7039954 : Nat := 1204960062514151460432949

theorem tailTrace_7039954 : CollatzResearch.WordTrace tailWord_7039954 prefixEnd_7039954 1204960062514151460432949 := by
  unfold tailWord_7039954
  simp only [CollatzResearch.WordTrace]
  refine ⟨64192054184364115316513729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171178811158304307510703277 64192054184364115316513729)
  ·
    refine ⟨48144040638273086487385297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64192054184364115316513729 48144040638273086487385297)
    ·
      refine ⟨36108030478704814865538973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48144040638273086487385297 36108030478704814865538973)
      ·
        refine ⟨13540511429514305574577115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36108030478704814865538973 13540511429514305574577115)
        ·
          refine ⟨20310767144271458361865673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13540511429514305574577115 20310767144271458361865673)
          ·
            refine ⟨15233075358203593771399255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20310767144271458361865673 15233075358203593771399255)
            ·
              refine ⟨22849613037305390657098883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15233075358203593771399255 22849613037305390657098883)
              ·
                refine ⟨34274419555958085985648325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22849613037305390657098883 34274419555958085985648325)
                ·
                  refine ⟨6426453666742141122309061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34274419555958085985648325 6426453666742141122309061)
                  ·
                    refine ⟨1204960062514151460432949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6426453666742141122309061 1204960062514151460432949)
                    ·
                      rfl

theorem cell23_7039954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_7039954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039954 prefixEnd_7039954 := by exact prefixLift 7039954
  have htrace : WordTrace (prefixWord ++ tailWord_7039954) baseStart_7039954 baseEnd_7039954 := by
    simpa [prefixWord, tailWord_7039954, baseEnd_7039954] using wordTrace_append hprefix tailTrace_7039954
  have hstable : (prefixWord ++ tailWord_7039954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039954).length < 2 ^ (prefixWord ++ tailWord_7039954).sum := by decide
  have hdescent : baseEnd_7039954 < baseStart_7039954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7039961 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 3, 2, 2]
def baseStart_7039961 : Nat := 118140960795 + 7039961 * 2 ^ 59
def prefixEnd_7039961 : Nat := 4983230072969 + 3 ^ 40 * 7039961 * 2
def baseEnd_7039961 : Nat := 3614883781907035853911315

theorem tailTrace_7039961 : CollatzResearch.WordTrace tailWord_7039961 prefixEnd_7039961 3614883781907035853911315 := by
  unfold tailWord_7039961
  simp only [CollatzResearch.WordTrace]
  refine ⟨256768472048431101461559737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171178981365620734307706491 256768472048431101461559737)
  ·
    refine ⟨192576354036323326096169803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256768472048431101461559737 192576354036323326096169803)
    ·
      refine ⟨288864531054484989144254705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192576354036323326096169803 288864531054484989144254705)
      ·
        refine ⟨216648398290863741858191029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288864531054484989144254705 216648398290863741858191029)
        ·
          refine ⟨20310787339768475799205409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216648398290863741858191029 20310787339768475799205409)
          ·
            refine ⟨15233090504826356849404057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20310787339768475799205409 15233090504826356849404057)
            ·
              refine ⟨11424817878619767637053043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15233090504826356849404057 11424817878619767637053043)
              ·
                refine ⟨17137226817929651455579565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11424817878619767637053043 17137226817929651455579565)
                ·
                  refine ⟨6426460056723619295842337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17137226817929651455579565 6426460056723619295842337)
                  ·
                    refine ⟨4819845042542714471881753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6426460056723619295842337 4819845042542714471881753)
                    ·
                      refine ⟨3614883781907035853911315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819845042542714471881753 3614883781907035853911315)
                      ·
                        rfl

theorem cell23_7039961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_7039961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7039961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7039961 prefixEnd_7039961 := by exact prefixLift 7039961
  have htrace : WordTrace (prefixWord ++ tailWord_7039961) baseStart_7039961 baseEnd_7039961 := by
    simpa [prefixWord, tailWord_7039961, baseEnd_7039961] using wordTrace_append hprefix tailTrace_7039961
  have hstable : (prefixWord ++ tailWord_7039961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7039961).length < 2 ^ (prefixWord ++ tailWord_7039961).sum := by decide
  have hdescent : baseEnd_7039961 < baseStart_7039961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7039961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040054 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_7040054 : Nat := 118140960795 + 7040054 * 2 ^ 59
def prefixEnd_7040054 : Nat := 4983230072969 + 3 ^ 40 * 7040054 * 2
def baseEnd_7040054 : Nat := 3614931535607903990048387

theorem tailTrace_7040054 : CollatzResearch.WordTrace tailWord_7040054 prefixEnd_7040054 3614931535607903990048387 := by
  unfold tailWord_7040054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16048241502318386146543451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171181242691396118896463477 16048241502318386146543451)
  ·
    refine ⟨24072362253477579219815177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16048241502318386146543451 24072362253477579219815177)
    ·
      refine ⟨18054271690108184414861383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24072362253477579219815177 18054271690108184414861383)
      ·
        refine ⟨27081407535162276622292075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18054271690108184414861383 27081407535162276622292075)
        ·
          refine ⟨40622111302743414933438113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27081407535162276622292075 40622111302743414933438113)
          ·
            refine ⟨30466583477057561200078585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40622111302743414933438113 30466583477057561200078585)
            ·
              refine ⟨22849937607793170900058939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30466583477057561200078585 22849937607793170900058939)
              ·
                refine ⟨34274906411689756350088409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22849937607793170900058939 34274906411689756350088409)
                ·
                  refine ⟨25706179808767317262566307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34274906411689756350088409 25706179808767317262566307)
                  ·
                    refine ⟨38559269713150975893849461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25706179808767317262566307 38559269713150975893849461)
                    ·
                      refine ⟨3614931535607903990048387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38559269713150975893849461 3614931535607903990048387)
                      ·
                        rfl

theorem cell23_7040054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_7040054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040054 prefixEnd_7040054 := by exact prefixLift 7040054
  have htrace : WordTrace (prefixWord ++ tailWord_7040054) baseStart_7040054 baseEnd_7040054 := by
    simpa [prefixWord, tailWord_7040054, baseEnd_7040054] using wordTrace_append hprefix tailTrace_7040054
  have hstable : (prefixWord ++ tailWord_7040054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040054).length < 2 ^ (prefixWord ++ tailWord_7040054).sum := by decide
  have hdescent : baseEnd_7040054 < baseStart_7040054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040067 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 3]
def baseStart_7040067 : Nat := 118140960795 + 7040067 * 2 ^ 59
def prefixEnd_7040067 : Nat := 4983230072969 + 3 ^ 40 * 7040067 * 2
def baseEnd_7040067 : Nat := 3614938210856412439185827

theorem tailTrace_7040067 : CollatzResearch.WordTrace tailWord_7040067 prefixEnd_7040067 3614938210856412439185827 := by
  unfold tailWord_7040067
  simp only [CollatzResearch.WordTrace]
  refine ⟨256772338186047081564918455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171181558790698054376612303 256772338186047081564918455)
  ·
    refine ⟨385158507279070622347377683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256772338186047081564918455 385158507279070622347377683)
    ·
      refine ⟨577737760918605933521066525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385158507279070622347377683 577737760918605933521066525)
      ·
        refine ⟨216651660344477225070399947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577737760918605933521066525 216651660344477225070399947)
        ·
          refine ⟨324977490516715837605599921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216651660344477225070399947 324977490516715837605599921)
          ·
            refine ⟨243733117887536878204199941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324977490516715837605599921 243733117887536878204199941)
            ·
              refine ⟨45699959603913164663287489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243733117887536878204199941 45699959603913164663287489)
              ·
                refine ⟨34274969702934873497465617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45699959603913164663287489 34274969702934873497465617)
                ·
                  refine ⟨25706227277201155123099213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34274969702934873497465617 25706227277201155123099213)
                  ·
                    refine ⟨9639835228950433171162205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25706227277201155123099213 9639835228950433171162205)
                    ·
                      refine ⟨3614938210856412439185827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9639835228950433171162205 3614938210856412439185827)
                      ·
                        rfl

theorem cell23_7040067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_7040067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040067 prefixEnd_7040067 := by exact prefixLift 7040067
  have htrace : WordTrace (prefixWord ++ tailWord_7040067) baseStart_7040067 baseEnd_7040067 := by
    simpa [prefixWord, tailWord_7040067, baseEnd_7040067] using wordTrace_append hprefix tailTrace_7040067
  have hstable : (prefixWord ++ tailWord_7040067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040067).length < 2 ^ (prefixWord ++ tailWord_7040067).sum := by decide
  have hdescent : baseEnd_7040067 < baseStart_7040067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040124 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 4, 4, 2]
def baseStart_7040124 : Nat := 118140960795 + 7040124 * 2 ^ 59
def prefixEnd_7040124 : Nat := 4983230072969 + 3 ^ 40 * 7040124 * 2
def baseEnd_7040124 : Nat := 3614967479253718716173065

theorem tailTrace_7040124 : CollatzResearch.WordTrace tailWord_7040124 prefixEnd_7040124 3614967479253718716173065 := by
  unfold tailWord_7040124
  simp only [CollatzResearch.WordTrace]
  refine ⟨128387208573420290149871713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171182944764560386866495617 128387208573420290149871713)
  ·
    refine ⟨96290406430065217612403785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128387208573420290149871713 96290406430065217612403785)
    ·
      refine ⟨72217804822548913209302839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96290406430065217612403785 72217804822548913209302839)
      ·
        refine ⟨108326707233823369813954259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72217804822548913209302839 108326707233823369813954259)
        ·
          refine ⟨162490060850735054720931389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108326707233823369813954259 162490060850735054720931389)
          ·
            refine ⟨60933772819025645520349271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162490060850735054720931389 60933772819025645520349271)
            ·
              refine ⟨91400659228538468280523907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60933772819025645520349271 91400659228538468280523907)
              ·
                refine ⟨137100988842807702420785861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91400659228538468280523907 137100988842807702420785861)
                ·
                  refine ⟨25706435408026444203897349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137100988842807702420785861 25706435408026444203897349)
                  ·
                    refine ⟨4819956639004958288230753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25706435408026444203897349 4819956639004958288230753)
                    ·
                      refine ⟨3614967479253718716173065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819956639004958288230753 3614967479253718716173065)
                      ·
                        rfl

theorem cell23_7040124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_7040124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040124 prefixEnd_7040124 := by exact prefixLift 7040124
  have htrace : WordTrace (prefixWord ++ tailWord_7040124) baseStart_7040124 baseEnd_7040124 := by
    simpa [prefixWord, tailWord_7040124, baseEnd_7040124] using wordTrace_append hprefix tailTrace_7040124
  have hstable : (prefixWord ++ tailWord_7040124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040124).length < 2 ^ (prefixWord ++ tailWord_7040124).sum := by decide
  have hdescent : baseEnd_7040124 < baseStart_7040124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040147 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 6]
def baseStart_7040147 : Nat := 118140960795 + 7040147 * 2 ^ 59
def prefixEnd_7040147 : Nat := 4983230072969 + 3 ^ 40 * 7040147 * 2
def baseEnd_7040147 : Nat := 401664365478752458465051

theorem tailTrace_7040147 : CollatzResearch.WordTrace tailWord_7040147 prefixEnd_7040147 401664365478752458465051 := by
  unfold tailWord_7040147
  simp only [CollatzResearch.WordTrace]
  refine ⟨256775256025757255227830695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171183504017171503485220463 256775256025757255227830695)
  ·
    refine ⟨385162884038635882841746043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256775256025757255227830695 385162884038635882841746043)
    ·
      refine ⟨577744326057953824262619065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385162884038635882841746043 577744326057953824262619065)
      ·
        refine ⟨433308244543465368196964299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577744326057953824262619065 433308244543465368196964299)
        ·
          refine ⟨649962366815198052295446449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433308244543465368196964299 649962366815198052295446449)
          ·
            refine ⟨487471775111398539221584837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649962366815198052295446449 487471775111398539221584837)
            ·
              refine ⟨91400957833387226104047157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 487471775111398539221584837 91400957833387226104047157)
              ·
                refine ⟨8568839796880052447254421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91400957833387226104047157 8568839796880052447254421)
                ·
                  refine ⟨401664365478752458465051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8568839796880052447254421 401664365478752458465051)
                  ·
                    rfl

theorem cell23_7040147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 6].length) (baseStart_7040147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040147 prefixEnd_7040147 := by exact prefixLift 7040147
  have htrace : WordTrace (prefixWord ++ tailWord_7040147) baseStart_7040147 baseEnd_7040147 := by
    simpa [prefixWord, tailWord_7040147, baseEnd_7040147] using wordTrace_append hprefix tailTrace_7040147
  have hstable : (prefixWord ++ tailWord_7040147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040147).length < 2 ^ (prefixWord ++ tailWord_7040147).sum := by decide
  have hdescent : baseEnd_7040147 < baseStart_7040147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040184 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 3, 5, 2]
def baseStart_7040184 : Nat := 118140960795 + 7040184 * 2 ^ 59
def prefixEnd_7040184 : Nat := 4983230072969 + 3 ^ 40 * 7040184 * 2
def baseEnd_7040184 : Nat := 3614998288092988481422789

theorem tailTrace_7040184 : CollatzResearch.WordTrace tailWord_7040184 prefixEnd_7040184 3614998288092988481422789 := by
  unfold tailWord_7040184
  simp only [CollatzResearch.WordTrace]
  refine ⟨128388302763311605273463803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171184403684415473697951737 128388302763311605273463803)
  ·
    refine ⟨192582454144967407910195705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128388302763311605273463803 192582454144967407910195705)
    ·
      refine ⟨144436840608725555932646779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192582454144967407910195705 144436840608725555932646779)
      ·
        refine ⟨216655260913088333898970169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144436840608725555932646779 216655260913088333898970169)
        ·
          refine ⟨162491445684816250424227627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216655260913088333898970169 162491445684816250424227627)
          ·
            refine ⟨243737168527224375636341441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162491445684816250424227627 243737168527224375636341441)
            ·
              refine ⟨182802876395418281727256081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243737168527224375636341441 182802876395418281727256081)
              ·
                refine ⟨137102157296563711295442061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182802876395418281727256081 137102157296563711295442061)
                ·
                  refine ⟨51413308986211391735790773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137102157296563711295442061 51413308986211391735790773)
                  ·
                    refine ⟨4819997717457317975230385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51413308986211391735790773 4819997717457317975230385)
                    ·
                      refine ⟨3614998288092988481422789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4819997717457317975230385 3614998288092988481422789)
                      ·
                        rfl

theorem cell23_7040184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_7040184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040184 prefixEnd_7040184 := by exact prefixLift 7040184
  have htrace : WordTrace (prefixWord ++ tailWord_7040184) baseStart_7040184 baseEnd_7040184 := by
    simpa [prefixWord, tailWord_7040184, baseEnd_7040184] using wordTrace_append hprefix tailTrace_7040184
  have hstable : (prefixWord ++ tailWord_7040184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040184).length < 2 ^ (prefixWord ++ tailWord_7040184).sum := by decide
  have hdescent : baseEnd_7040184 < baseStart_7040184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040191 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 3, 1, 3]
def baseStart_7040191 : Nat := 118140960795 + 7040191 * 2 ^ 59
def prefixEnd_7040191 : Nat := 4983230072969 + 3 ^ 40 * 7040191 * 2
def baseEnd_7040191 : Nat := 3615001882457569954035257

theorem tailTrace_7040191 : CollatzResearch.WordTrace tailWord_7040191 prefixEnd_7040191 3615001882457569954035257 := by
  unfold tailWord_7040191
  simp only [CollatzResearch.WordTrace]
  refine ⟨256776860837597850742432427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171184573891731900494954951 256776860837597850742432427)
  ·
    refine ⟨385165291256396776113648641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256776860837597850742432427 385165291256396776113648641)
    ·
      refine ⟨288873968442297582085236481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385165291256396776113648641 288873968442297582085236481)
      ·
        refine ⟨216655476331723186563927361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288873968442297582085236481 216655476331723186563927361)
        ·
          refine ⟨162491607248792389922945521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216655476331723186563927361 162491607248792389922945521)
          ·
            refine ⟨121868705436594292442209141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162491607248792389922945521 121868705436594292442209141)
            ·
              refine ⟨11425191134680714916457107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121868705436594292442209141 11425191134680714916457107)
              ·
                refine ⟨17137786702021072374685661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11425191134680714916457107 17137786702021072374685661)
                ·
                  refine ⟨6426670013257902140507123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17137786702021072374685661 6426670013257902140507123)
                  ·
                    refine ⟨9640005019886853210760685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6426670013257902140507123 9640005019886853210760685)
                    ·
                      refine ⟨3615001882457569954035257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9640005019886853210760685 3615001882457569954035257)
                      ·
                        rfl

theorem cell23_7040191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_7040191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040191 prefixEnd_7040191 := by exact prefixLift 7040191
  have htrace : WordTrace (prefixWord ++ tailWord_7040191) baseStart_7040191 baseEnd_7040191 := by
    simpa [prefixWord, tailWord_7040191, baseEnd_7040191] using wordTrace_append hprefix tailTrace_7040191
  have hstable : (prefixWord ++ tailWord_7040191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040191).length < 2 ^ (prefixWord ++ tailWord_7040191).sum := by decide
  have hdescent : baseEnd_7040191 < baseStart_7040191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040197 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_7040197 : Nat := 118140960795 + 7040197 * 2 ^ 59
def prefixEnd_7040197 : Nat := 4983230072969 + 3 ^ 40 * 7040197 * 2
def baseEnd_7040197 : Nat := 3615004963341496930560229

theorem tailTrace_7040197 : CollatzResearch.WordTrace tailWord_7040197 prefixEnd_7040197 3615004963341496930560229 := by
  unfold tailWord_7040197
  simp only [CollatzResearch.WordTrace]
  refine ⟨256777079675576113767150845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171184719783717409178100563 256777079675576113767150845)
  ·
    refine ⟨96291404878341042662681567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256777079675576113767150845 96291404878341042662681567)
    ·
      refine ⟨144437107317511563994022351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96291404878341042662681567 144437107317511563994022351)
      ·
        refine ⟨216655660976267345991033527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144437107317511563994022351 216655660976267345991033527)
        ·
          refine ⟨324983491464401018986550291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216655660976267345991033527 324983491464401018986550291)
          ·
            refine ⟨487475237196601528479825437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324983491464401018986550291 487475237196601528479825437)
            ·
              refine ⟨182803213948725573179934539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 487475237196601528479825437 182803213948725573179934539)
              ·
                refine ⟨274204820923088359769901809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182803213948725573179934539 274204820923088359769901809)
                ·
                  refine ⟨205653615692316269827426357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274204820923088359769901809 205653615692316269827426357)
                  ·
                    refine ⟨19280026471154650296321221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 205653615692316269827426357 19280026471154650296321221)
                    ·
                      refine ⟨3615004963341496930560229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19280026471154650296321221 3615004963341496930560229)
                      ·
                        rfl

theorem cell23_7040197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_7040197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040197 prefixEnd_7040197 := by exact prefixLift 7040197
  have htrace : WordTrace (prefixWord ++ tailWord_7040197) baseStart_7040197 baseEnd_7040197 := by
    simpa [prefixWord, tailWord_7040197, baseEnd_7040197] using wordTrace_append hprefix tailTrace_7040197
  have hstable : (prefixWord ++ tailWord_7040197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040197).length < 2 ^ (prefixWord ++ tailWord_7040197).sum := by decide
  have hdescent : baseEnd_7040197 < baseStart_7040197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040224 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 1, 6]
def baseStart_7040224 : Nat := 118140960795 + 7040224 * 2 ^ 59
def prefixEnd_7040224 : Nat := 4983230072969 + 3 ^ 40 * 7040224 * 2
def baseEnd_7040224 : Nat := 1205006275773056108307535

theorem tailTrace_7040224 : CollatzResearch.WordTrace tailWord_7040224 prefixEnd_7040224 1205006275773056108307535 := by
  unfold tailWord_7040224
  simp only [CollatzResearch.WordTrace]
  refine ⟨128389032223239148689191863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171185376297652198252255817 128389032223239148689191863)
  ·
    refine ⟨192583548334858723033787795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128389032223239148689191863 192583548334858723033787795)
    ·
      refine ⟨288875322502288084550681693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192583548334858723033787795 288875322502288084550681693)
      ·
        refine ⟨108328245938358031706505635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288875322502288084550681693 108328245938358031706505635)
        ·
          refine ⟨162492368907537047559758453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108328245938358031706505635 162492368907537047559758453)
          ·
            refine ⟨15233659585081598208727355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162492368907537047559758453 15233659585081598208727355)
            ·
              refine ⟨22850489377622397313091033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15233659585081598208727355 22850489377622397313091033)
              ·
                refine ⟨17137867033216797984818275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22850489377622397313091033 17137867033216797984818275)
                ·
                  refine ⟨25706800549825196977227413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17137867033216797984818275 25706800549825196977227413)
                  ·
                    refine ⟨1205006275773056108307535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25706800549825196977227413 1205006275773056108307535)
                    ·
                      rfl

theorem cell23_7040224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_7040224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040224 prefixEnd_7040224 := by exact prefixLift 7040224
  have htrace : WordTrace (prefixWord ++ tailWord_7040224) baseStart_7040224 baseEnd_7040224 := by
    simpa [prefixWord, tailWord_7040224, baseEnd_7040224] using wordTrace_append hprefix tailTrace_7040224
  have hstable : (prefixWord ++ tailWord_7040224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040224).length < 2 ^ (prefixWord ++ tailWord_7040224).sum := by decide
  have hdescent : baseEnd_7040224 < baseStart_7040224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040258 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_7040258 : Nat := 118140960795 + 7040258 * 2 ^ 59
def prefixEnd_7040258 : Nat := 4983230072969 + 3 ^ 40 * 7040258 * 2
def baseEnd_7040258 : Nat := 1205012095220473730632483

theorem tailTrace_7040258 : CollatzResearch.WordTrace tailWord_7040258 prefixEnd_7040258 1205012095220473730632483 := by
  unfold tailWord_7040258
  simp only [CollatzResearch.WordTrace]
  refine ⟨64194826132088780296280357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171186203018903414123414285 64194826132088780296280357)
  ·
    refine ⟨12036529899766646305552567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64194826132088780296280357 12036529899766646305552567)
    ·
      refine ⟨18054794849649969458328851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12036529899766646305552567 18054794849649969458328851)
      ·
        refine ⟨27082192274474954187493277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18054794849649969458328851 27082192274474954187493277)
        ·
          refine ⟨10155822102928107820309979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27082192274474954187493277 10155822102928107820309979)
          ·
            refine ⟨15233733154392161730464969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10155822102928107820309979 15233733154392161730464969)
            ·
              refine ⟨11425299865794121297848727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15233733154392161730464969 11425299865794121297848727)
              ·
                refine ⟨17137949798691181946773091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11425299865794121297848727 17137949798691181946773091)
                ·
                  refine ⟨25706924698036772920159637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17137949798691181946773091 25706924698036772920159637)
                  ·
                    refine ⟨1205012095220473730632483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25706924698036772920159637 1205012095220473730632483)
                    ·
                      rfl

theorem cell23_7040258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_7040258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040258 prefixEnd_7040258 := by exact prefixLift 7040258
  have htrace : WordTrace (prefixWord ++ tailWord_7040258) baseStart_7040258 baseEnd_7040258 := by
    simpa [prefixWord, tailWord_7040258, baseEnd_7040258] using wordTrace_append hprefix tailTrace_7040258
  have hstable : (prefixWord ++ tailWord_7040258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040258).length < 2 ^ (prefixWord ++ tailWord_7040258).sum := by decide
  have hdescent : baseEnd_7040258 < baseStart_7040258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040282 : List Nat := [3, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2]
def baseStart_7040282 : Nat := 118140960795 + 7040282 * 2 ^ 59
def prefixEnd_7040282 : Nat := 4983230072969 + 3 ^ 40 * 7040282 * 2
def baseEnd_7040282 : Nat := 3615048609197129097997339

theorem tailTrace_7040282 : CollatzResearch.WordTrace tailWord_7040282 prefixEnd_7040282 3615048609197129097997339 := by
  unfold tailWord_7040282
  simp only [CollatzResearch.WordTrace]
  refine ⟨64195044970067043320998775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171186786586845448855996733 64195044970067043320998775)
  ·
    refine ⟨96292567455100564981498163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64195044970067043320998775 96292567455100564981498163)
    ·
      refine ⟨144438851182650847472247245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96292567455100564981498163 144438851182650847472247245)
      ·
        refine ⟨54164569193494067802092717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144438851182650847472247245 54164569193494067802092717)
        ·
          refine ⟨20311713447560275425784769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54164569193494067802092717 20311713447560275425784769)
          ·
            refine ⟨15233785085670206569338577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20311713447560275425784769 15233785085670206569338577)
            ·
              refine ⟨11425338814252654927003933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15233785085670206569338577 11425338814252654927003933)
              ·
                refine ⟨4284502055344745597626475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11425338814252654927003933 4284502055344745597626475)
                ·
                  refine ⟨6426753083017118396439713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4284502055344745597626475 6426753083017118396439713)
                  ·
                    refine ⟨4820064812262838797329785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6426753083017118396439713 4820064812262838797329785)
                    ·
                      refine ⟨3615048609197129097997339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820064812262838797329785 3615048609197129097997339)
                      ·
                        rfl

theorem cell23_7040282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_7040282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040282 prefixEnd_7040282 := by exact prefixLift 7040282
  have htrace : WordTrace (prefixWord ++ tailWord_7040282) baseStart_7040282 baseEnd_7040282 := by
    simpa [prefixWord, tailWord_7040282, baseEnd_7040282] using wordTrace_append hprefix tailTrace_7040282
  have hstable : (prefixWord ++ tailWord_7040282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040282).length < 2 ^ (prefixWord ++ tailWord_7040282).sum := by decide
  have hdescent : baseEnd_7040282 < baseStart_7040282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040285 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_7040285 : Nat := 118140960795 + 7040285 * 2 ^ 59
def prefixEnd_7040285 : Nat := 4983230072969 + 3 ^ 40 * 7040285 * 2
def baseEnd_7040285 : Nat := 3615050149639092586259825

theorem tailTrace_7040285 : CollatzResearch.WordTrace tailWord_7040285 prefixEnd_7040285 3615050149639092586259825 := by
  unfold tailWord_7040285
  simp only [CollatzResearch.WordTrace]
  refine ⟨256780289299257304796354309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171186859532838203197569539 256780289299257304796354309)
  ·
    refine ⟨48146304243610744649316433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256780289299257304796354309 48146304243610744649316433)
    ·
      refine ⟨36109728182708058486987325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48146304243610744649316433 36109728182708058486987325)
      ·
        refine ⟨13541148068515521932620247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36109728182708058486987325 13541148068515521932620247)
        ·
          refine ⟨20311722102773282898930371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13541148068515521932620247 20311722102773282898930371)
          ·
            refine ⟨30467583154159924348395557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20311722102773282898930371 30467583154159924348395557)
            ·
              refine ⟨5712671841404985815324167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30467583154159924348395557 5712671841404985815324167)
              ·
                refine ⟨8569007762107478722986251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712671841404985815324167 8569007762107478722986251)
                ·
                  refine ⟨12853511643161218084479377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8569007762107478722986251 12853511643161218084479377)
                  ·
                    refine ⟨9640133732370913563359533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12853511643161218084479377 9640133732370913563359533)
                    ·
                      refine ⟨3615050149639092586259825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9640133732370913563359533 3615050149639092586259825)
                      ·
                        rfl

theorem cell23_7040285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_7040285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040285 prefixEnd_7040285 := by exact prefixLift 7040285
  have htrace : WordTrace (prefixWord ++ tailWord_7040285) baseStart_7040285 baseEnd_7040285 := by
    simpa [prefixWord, tailWord_7040285, baseEnd_7040285] using wordTrace_append hprefix tailTrace_7040285
  have hstable : (prefixWord ++ tailWord_7040285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040285).length < 2 ^ (prefixWord ++ tailWord_7040285).sum := by decide
  have hdescent : baseEnd_7040285 < baseStart_7040285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040314 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_7040314 : Nat := 118140960795 + 7040314 * 2 ^ 59
def prefixEnd_7040314 : Nat := 4983230072969 + 3 ^ 40 * 7040314 * 2
def baseEnd_7040314 : Nat := 1205021680192690990932397

theorem tailTrace_7040314 : CollatzResearch.WordTrace tailWord_7040314 prefixEnd_7040314 1205021680192690990932397 := by
  unfold tailWord_7040314
  simp only [CollatzResearch.WordTrace]
  refine ⟨64195336754038060687289999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171187564677434828499439997 64195336754038060687289999)
  ·
    refine ⟨96293005131057091030934999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64195336754038060687289999 96293005131057091030934999)
    ·
      refine ⟨144439507696585636546402499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96293005131057091030934999 144439507696585636546402499)
      ·
        refine ⟨216659261544878454819603749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144439507696585636546402499 216659261544878454819603749)
        ·
          refine ⟨40623611539664710278675703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216659261544878454819603749 40623611539664710278675703)
          ·
            refine ⟨60935417309497065418013555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40623611539664710278675703 60935417309497065418013555)
            ·
              refine ⟨91403125964245598127020333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60935417309497065418013555 91403125964245598127020333)
              ·
                refine ⟨34276172236592099297632625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91403125964245598127020333 34276172236592099297632625)
                ·
                  refine ⟨25707129177444074473224469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34276172236592099297632625 25707129177444074473224469)
                  ·
                    refine ⟨1205021680192690990932397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25707129177444074473224469 1205021680192690990932397)
                    ·
                      rfl

theorem cell23_7040314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_7040314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040314 prefixEnd_7040314 := by exact prefixLift 7040314
  have htrace : WordTrace (prefixWord ++ tailWord_7040314) baseStart_7040314 baseEnd_7040314 := by
    simpa [prefixWord, tailWord_7040314, baseEnd_7040314] using wordTrace_append hprefix tailTrace_7040314
  have hstable : (prefixWord ++ tailWord_7040314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040314).length < 2 ^ (prefixWord ++ tailWord_7040314).sum := by decide
  have hdescent : baseEnd_7040314 < baseStart_7040314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040333 : List Nat := [1, 6, 1, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7040333 : Nat := 118140960795 + 7040333 * 2 ^ 59
def prefixEnd_7040333 : Nat := 4983230072969 + 3 ^ 40 * 7040333 * 2
def baseEnd_7040333 : Nat := 3615074796710508398459605

theorem tailTrace_7040333 : CollatzResearch.WordTrace tailWord_7040333 prefixEnd_7040333 3615074796710508398459605 := by
  unfold tailWord_7040333
  simp only [CollatzResearch.WordTrace]
  refine ⟨256782040003083408994101653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171188026668722272662734435 256782040003083408994101653)
  ·
    refine ⟨12036658125144534796598515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 256782040003083408994101653 12036658125144534796598515)
    ·
      refine ⟨18054987187716802194897773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12036658125144534796598515 18054987187716802194897773)
      ·
        refine ⟨6770620195393800823086665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18054987187716802194897773 6770620195393800823086665)
        ·
          refine ⟨5077965146545350617314999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6770620195393800823086665 5077965146545350617314999)
          ·
            refine ⟨7616947719818025925972499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077965146545350617314999 7616947719818025925972499)
            ·
              refine ⟨11425421579727038888958749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616947719818025925972499 11425421579727038888958749)
              ·
                refine ⟨4284533092397639583359531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11425421579727038888958749 4284533092397639583359531)
                ·
                  refine ⟨6426799638596459375039297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4284533092397639583359531 6426799638596459375039297)
                  ·
                    refine ⟨4820099728947344531279473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6426799638596459375039297 4820099728947344531279473)
                    ·
                      refine ⟨3615074796710508398459605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820099728947344531279473 3615074796710508398459605)
                      ·
                        rfl

theorem cell23_7040333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7040333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040333 prefixEnd_7040333 := by exact prefixLift 7040333
  have htrace : WordTrace (prefixWord ++ tailWord_7040333) baseStart_7040333 baseEnd_7040333 := by
    simpa [prefixWord, tailWord_7040333, baseEnd_7040333] using wordTrace_append hprefix tailTrace_7040333
  have hstable : (prefixWord ++ tailWord_7040333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040333).length < 2 ^ (prefixWord ++ tailWord_7040333).sum := by decide
  have hdescent : baseEnd_7040333 < baseStart_7040333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040341 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_7040341 : Nat := 118140960795 + 7040341 * 2 ^ 59
def prefixEnd_7040341 : Nat := 4983230072969 + 3 ^ 40 * 7040341 * 2
def baseEnd_7040341 : Nat := 3615078904555744367159567

theorem tailTrace_7040341 : CollatzResearch.WordTrace tailWord_7040341 prefixEnd_7040341 3615078904555744367159567 := by
  unfold tailWord_7040341
  simp only [CollatzResearch.WordTrace]
  refine ⟨256782331787054426360392877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171188221191369617573595251 256782331787054426360392877)
  ·
    refine ⟨96293374420145409885147329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256782331787054426360392877 96293374420145409885147329)
    ·
      refine ⟨72220030815109057413860497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96293374420145409885147329 72220030815109057413860497)
      ·
        refine ⟨54165023111331793060395373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72220030815109057413860497 54165023111331793060395373)
        ·
          refine ⟨20311883666749422397648265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54165023111331793060395373 20311883666749422397648265)
          ·
            refine ⟨15233912750062066798236199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20311883666749422397648265 15233912750062066798236199)
            ·
              refine ⟨22850869125093100197354299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15233912750062066798236199 22850869125093100197354299)
              ·
                refine ⟨34276303687639650296031449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22850869125093100197354299 34276303687639650296031449)
                ·
                  refine ⟨25707227765729737722023587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34276303687639650296031449 25707227765729737722023587)
                  ·
                    refine ⟨38560841648594606583035381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25707227765729737722023587 38560841648594606583035381)
                    ·
                      refine ⟨3615078904555744367159567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38560841648594606583035381 3615078904555744367159567)
                      ·
                        rfl

theorem cell23_7040341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_7040341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040341 prefixEnd_7040341 := by exact prefixLift 7040341
  have htrace : WordTrace (prefixWord ++ tailWord_7040341) baseStart_7040341 baseEnd_7040341 := by
    simpa [prefixWord, tailWord_7040341, baseEnd_7040341] using wordTrace_append hprefix tailTrace_7040341
  have hstable : (prefixWord ++ tailWord_7040341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040341).length < 2 ^ (prefixWord ++ tailWord_7040341).sum := by decide
  have hdescent : baseEnd_7040341 < baseStart_7040341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040366 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_7040366 : Nat := 118140960795 + 7040366 * 2 ^ 59
def prefixEnd_7040366 : Nat := 4983230072969 + 3 ^ 40 * 7040366 * 2
def baseEnd_7040366 : Nat := 3615091741572106769346953

theorem tailTrace_7040366 : CollatzResearch.WordTrace tailWord_7040366 prefixEnd_7040366 3615091741572106769346953 := by
  unfold tailWord_7040366
  simp only [CollatzResearch.WordTrace]
  refine ⟨32097905451495481953756619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171188829074642570420035301 32097905451495481953756619)
  ·
    refine ⟨48146858177243222930634929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32097905451495481953756619 48146858177243222930634929)
    ·
      refine ⟨36110143632932417197976197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48146858177243222930634929 36110143632932417197976197)
      ·
        refine ⟨6770651931174828224620537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36110143632932417197976197 6770651931174828224620537)
        ·
          refine ⟨5077988948381121168465403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6770651931174828224620537 5077988948381121168465403)
          ·
            refine ⟨7616983422571681752698105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077988948381121168465403 7616983422571681752698105)
            ·
              refine ⟨5712737566928761314523579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7616983422571681752698105 5712737566928761314523579)
              ·
                refine ⟨8569106350393141971785369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712737566928761314523579 8569106350393141971785369)
                ·
                  refine ⟨6426829762794856478839027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8569106350393141971785369 6426829762794856478839027)
                  ·
                    refine ⟨9640244644192284718258541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6426829762794856478839027 9640244644192284718258541)
                    ·
                      refine ⟨3615091741572106769346953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9640244644192284718258541 3615091741572106769346953)
                      ·
                        rfl

theorem cell23_7040366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_7040366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040366 prefixEnd_7040366 := by exact prefixLift 7040366
  have htrace : WordTrace (prefixWord ++ tailWord_7040366) baseStart_7040366 baseEnd_7040366 := by
    simpa [prefixWord, tailWord_7040366, baseEnd_7040366] using wordTrace_append hprefix tailTrace_7040366
  have hstable : (prefixWord ++ tailWord_7040366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040366).length < 2 ^ (prefixWord ++ tailWord_7040366).sum := by decide
  have hdescent : baseEnd_7040366 < baseStart_7040366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040391 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 2, 5]
def baseStart_7040391 : Nat := 118140960795 + 7040391 * 2 ^ 59
def prefixEnd_7040391 : Nat := 4983230072969 + 3 ^ 40 * 7040391 * 2
def baseEnd_7040391 : Nat := 1205034859529489723844779

theorem tailTrace_7040391 : CollatzResearch.WordTrace tailWord_7040391 prefixEnd_7040391 1205034859529489723844779 := by
  unfold tailWord_7040391
  simp only [CollatzResearch.WordTrace]
  refine ⟨256784155436873284899713027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171189436957915523266475351 256784155436873284899713027)
  ·
    refine ⟨385176233155309927349569541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256784155436873284899713027 385176233155309927349569541)
    ·
      refine ⟨72220543716620611378044289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385176233155309927349569541 72220543716620611378044289)
      ·
        refine ⟨54165407787465458533533217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72220543716620611378044289 54165407787465458533533217)
        ·
          refine ⟨40624055840599093900149913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54165407787465458533533217 40624055840599093900149913)
          ·
            refine ⟨30468041880449320425112435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40624055840599093900149913 30468041880449320425112435)
            ·
              refine ⟨45702062820673980637668653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30468041880449320425112435 45702062820673980637668653)
              ·
                refine ⟨17138273557752742739125745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45702062820673980637668653 17138273557752742739125745)
                ·
                  refine ⟨12853705168314557054344309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17138273557752742739125745 12853705168314557054344309)
                  ·
                    refine ⟨1205034859529489723844779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12853705168314557054344309 1205034859529489723844779)
                    ·
                      rfl

theorem cell23_7040391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_7040391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040391 prefixEnd_7040391 := by exact prefixLift 7040391
  have htrace : WordTrace (prefixWord ++ tailWord_7040391) baseStart_7040391 baseEnd_7040391 := by
    simpa [prefixWord, tailWord_7040391, baseEnd_7040391] using wordTrace_append hprefix tailTrace_7040391
  have hstable : (prefixWord ++ tailWord_7040391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040391).length < 2 ^ (prefixWord ++ tailWord_7040391).sum := by decide
  have hdescent : baseEnd_7040391 < baseStart_7040391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040431 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 3]
def baseStart_7040431 : Nat := 118140960795 + 7040431 * 2 ^ 59
def prefixEnd_7040431 : Nat := 4983230072969 + 3 ^ 40 * 7040431 * 2
def baseEnd_7040431 : Nat := 3615125117814649015034153

theorem tailTrace_7040431 : CollatzResearch.WordTrace tailWord_7040431 prefixEnd_7040431 3615125117814649015034153 := by
  unfold tailWord_7040431
  simp only [CollatzResearch.WordTrace]
  refine ⟨256785614356728371731169147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171190409571152247820779431 256785614356728371731169147)
  ·
    refine ⟨385178421535092557596753721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256785614356728371731169147 385178421535092557596753721)
    ·
      refine ⟨288883816151319418197565291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385178421535092557596753721 288883816151319418197565291)
      ·
        refine ⟨433325724226979127296347937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288883816151319418197565291 433325724226979127296347937)
        ·
          refine ⟨324994293170234345472260953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433325724226979127296347937 324994293170234345472260953)
          ·
            refine ⟨243745719877675759104195715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324994293170234345472260953 243745719877675759104195715)
            ·
              refine ⟨365618579816513638656293573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243745719877675759104195715 365618579816513638656293573)
              ·
                refine ⟨68553483715596307248055045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365618579816513638656293573 68553483715596307248055045)
                ·
                  refine ⟨12853778196674307609010321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68553483715596307248055045 12853778196674307609010321)
                  ·
                    refine ⟨9640333647505730706757741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12853778196674307609010321 9640333647505730706757741)
                    ·
                      refine ⟨3615125117814649015034153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9640333647505730706757741 3615125117814649015034153)
                      ·
                        rfl

theorem cell23_7040431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 3].length) (baseStart_7040431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040431 prefixEnd_7040431 := by exact prefixLift 7040431
  have htrace : WordTrace (prefixWord ++ tailWord_7040431) baseStart_7040431 baseEnd_7040431 := by
    simpa [prefixWord, tailWord_7040431, baseEnd_7040431] using wordTrace_append hprefix tailTrace_7040431
  have hstable : (prefixWord ++ tailWord_7040431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040431).length < 2 ^ (prefixWord ++ tailWord_7040431).sum := by decide
  have hdescent : baseEnd_7040431 < baseStart_7040431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040448 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 3]
def baseStart_7040448 : Nat := 118140960795 + 7040448 * 2 ^ 59
def prefixEnd_7040448 : Nat := 4983230072969 + 3 ^ 40 * 7040448 * 2
def baseEnd_7040448 : Nat := 3615133846985775448521575

theorem tailTrace_7040448 : CollatzResearch.WordTrace tailWord_7040448 prefixEnd_7040448 3615133846985775448521575 := by
  unfold tailWord_7040448
  simp only [CollatzResearch.WordTrace]
  refine ⟨128393117198833391817268999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171190822931777855756358665 128393117198833391817268999)
  ·
    refine ⟨192589675798250087725903499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128393117198833391817268999 192589675798250087725903499)
    ·
      refine ⟨288884513697375131588855249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192589675798250087725903499 288884513697375131588855249)
      ·
        refine ⟨216663385273031348691641437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288884513697375131588855249 216663385273031348691641437)
        ·
          refine ⟨81248769477386755759365539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216663385273031348691641437 81248769477386755759365539)
          ·
            refine ⟨121873154216080133639048309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81248769477386755759365539 121873154216080133639048309)
            ·
              refine ⟨11425608207757512528660779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121873154216080133639048309 11425608207757512528660779)
              ·
                refine ⟨17138412311636268792991169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11425608207757512528660779 17138412311636268792991169)
                ·
                  refine ⟨12853809233727201594743377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17138412311636268792991169 12853809233727201594743377)
                  ·
                    refine ⟨9640356925295401196057533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12853809233727201594743377 9640356925295401196057533)
                    ·
                      refine ⟨3615133846985775448521575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9640356925295401196057533 3615133846985775448521575)
                      ·
                        rfl

theorem cell23_7040448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_7040448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040448 prefixEnd_7040448 := by exact prefixLift 7040448
  have htrace : WordTrace (prefixWord ++ tailWord_7040448) baseStart_7040448 baseEnd_7040448 := by
    simpa [prefixWord, tailWord_7040448, baseEnd_7040448] using wordTrace_append hprefix tailTrace_7040448
  have hstable : (prefixWord ++ tailWord_7040448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040448).length < 2 ^ (prefixWord ++ tailWord_7040448).sum := by decide
  have hdescent : baseEnd_7040448 < baseStart_7040448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040455 : List Nat := [1, 1, 4, 1, 1, 3, 4, 3, 1, 4]
def baseStart_7040455 : Nat := 118140960795 + 7040455 * 2 ^ 59
def prefixEnd_7040455 : Nat := 4983230072969 + 3 ^ 40 * 7040455 * 2
def baseEnd_7040455 : Nat := 1205045813783452307044681

theorem tailTrace_7040455 : CollatzResearch.WordTrace tailWord_7040455 prefixEnd_7040455 1205045813783452307044681 := by
  unfold tailWord_7040455
  simp only [CollatzResearch.WordTrace]
  refine ⟨256786489708641423830042819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171190993139094282553361879 256786489708641423830042819)
  ·
    refine ⟨385179734562962135745064229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256786489708641423830042819 385179734562962135745064229)
    ·
      refine ⟨72221200230555400452199543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385179734562962135745064229 72221200230555400452199543)
      ·
        refine ⟨108331800345833100678299315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72221200230555400452199543 108331800345833100678299315)
        ·
          refine ⟨162497700518749651017448973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108331800345833100678299315 162497700518749651017448973)
          ·
            refine ⟨60936637694531119131543365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162497700518749651017448973 60936637694531119131543365)
            ·
              refine ⟨11425619567724584837164381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60936637694531119131543365 11425619567724584837164381)
              ·
                refine ⟨4284607337896719313936643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11425619567724584837164381 4284607337896719313936643)
                ·
                  refine ⟨6426911006845078970904965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4284607337896719313936643 6426911006845078970904965)
                  ·
                    refine ⟨1205045813783452307044681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6426911006845078970904965 1205045813783452307044681)
                    ·
                      rfl

theorem cell23_7040455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_7040455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040455 prefixEnd_7040455 := by exact prefixLift 7040455
  have htrace : WordTrace (prefixWord ++ tailWord_7040455) baseStart_7040455 baseEnd_7040455 := by
    simpa [prefixWord, tailWord_7040455, baseEnd_7040455] using wordTrace_append hprefix tailTrace_7040455
  have hstable : (prefixWord ++ tailWord_7040455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040455).length < 2 ^ (prefixWord ++ tailWord_7040455).sum := by decide
  have hdescent : baseEnd_7040455 < baseStart_7040455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040468 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 8]
def baseStart_7040468 : Nat := 118140960795 + 7040468 * 2 ^ 59
def prefixEnd_7040468 : Nat := 4983230072969 + 3 ^ 40 * 7040468 * 2
def baseEnd_7040468 : Nat := 401682679622096152252387

theorem tailTrace_7040468 : CollatzResearch.WordTrace tailWord_7040468 prefixEnd_7040468 401682679622096152252387 := by
  unfold tailWord_7040468
  simp only [CollatzResearch.WordTrace]
  refine ⟨128393481928797163525133029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171191309238396218033510705 128393481928797163525133029)
  ·
    refine ⟨24073777861649468160962443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128393481928797163525133029 24073777861649468160962443)
    ·
      refine ⟨36110666792474202241443665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24073777861649468160962443 36110666792474202241443665)
      ·
        refine ⟨27083000094355651681082749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36110666792474202241443665 27083000094355651681082749)
        ·
          refine ⟨10156125035383369380406031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27083000094355651681082749 10156125035383369380406031)
          ·
            refine ⟨15234187553075054070609047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10156125035383369380406031 15234187553075054070609047)
            ·
              refine ⟨22851281329612581105913571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15234187553075054070609047 22851281329612581105913571)
              ·
                refine ⟨34276921994418871658870357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22851281329612581105913571 34276921994418871658870357)
                ·
                  refine ⟨401682679622096152252387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34276921994418871658870357 401682679622096152252387)
                  ·
                    rfl

theorem cell23_7040468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_7040468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040468 prefixEnd_7040468 := by exact prefixLift 7040468
  have htrace : WordTrace (prefixWord ++ tailWord_7040468) baseStart_7040468 baseEnd_7040468 := by
    simpa [prefixWord, tailWord_7040468, baseEnd_7040468] using wordTrace_append hprefix tailTrace_7040468
  have hstable : (prefixWord ++ tailWord_7040468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040468).length < 2 ^ (prefixWord ++ tailWord_7040468).sum := by decide
  have hdescent : baseEnd_7040468 < baseStart_7040468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040485 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 6]
def baseStart_7040485 : Nat := 118140960795 + 7040485 * 2 ^ 59
def prefixEnd_7040485 : Nat := 4983230072969 + 3 ^ 40 * 7040485 * 2
def baseEnd_7040485 : Nat := 401683649529999089306545

theorem tailTrace_7040485 : CollatzResearch.WordTrace tailWord_7040485 prefixEnd_7040485 401683649529999089306545 := by
  unfold tailWord_7040485
  simp only [CollatzResearch.WordTrace]
  refine ⟨256787583898532738953634909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171191722599021825969089939 256787583898532738953634909)
  ·
    refine ⟨96295343961949777107613091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256787583898532738953634909 96295343961949777107613091)
    ·
      refine ⟨144443015942924665661419637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96295343961949777107613091 144443015942924665661419637)
      ·
        refine ⟨13541532744649187405758091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144443015942924665661419637 13541532744649187405758091)
        ·
          refine ⟨20312299116973781108637137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13541532744649187405758091 20312299116973781108637137)
          ·
            refine ⟨15234224337730335831477853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20312299116973781108637137 15234224337730335831477853)
            ·
              refine ⟨5712834126648875936804195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15234224337730335831477853 5712834126648875936804195)
              ·
                refine ⟨8569251189973313905206293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712834126648875936804195 8569251189973313905206293)
                ·
                  refine ⟨401683649529999089306545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8569251189973313905206293 401683649529999089306545)
                  ·
                    rfl

theorem cell23_7040485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_7040485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040485 prefixEnd_7040485 := by exact prefixLift 7040485
  have htrace : WordTrace (prefixWord ++ tailWord_7040485) baseStart_7040485 baseEnd_7040485 := by
    simpa [prefixWord, tailWord_7040485, baseEnd_7040485] using wordTrace_append hprefix tailTrace_7040485
  have hstable : (prefixWord ++ tailWord_7040485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040485).length < 2 ^ (prefixWord ++ tailWord_7040485).sum := by decide
  have hdescent : baseEnd_7040485 < baseStart_7040485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040488 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_7040488 : Nat := 118140960795 + 7040488 * 2 ^ 59
def prefixEnd_7040488 : Nat := 4983230072969 + 3 ^ 40 * 7040488 * 2
def baseEnd_7040488 : Nat := 3615154386211955292021391

theorem tailTrace_7040488 : CollatzResearch.WordTrace tailWord_7040488 prefixEnd_7040488 3615154386211955292021391 := by
  unfold tailWord_7040488
  simp only [CollatzResearch.WordTrace]
  refine ⟨128393846658760935232997059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171191795545014580310662745 128393846658760935232997059)
  ·
    refine ⟨192590769988141402849495589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128393846658760935232997059 192590769988141402849495589)
    ·
      refine ⟨36110769372776513034280423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192590769988141402849495589 36110769372776513034280423)
      ·
        refine ⟨54166154059164769551420635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36110769372776513034280423 54166154059164769551420635)
        ·
          refine ⟨81249231088747154327130953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54166154059164769551420635 81249231088747154327130953)
          ·
            refine ⟨60936923316560365745348215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81249231088747154327130953 60936923316560365745348215)
            ·
              refine ⟨91405384974840548618022323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60936923316560365745348215 91405384974840548618022323)
              ·
                refine ⟨137108077462260822927033485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91405384974840548618022323 137108077462260822927033485)
                ·
                  refine ⟨51415529048347808597637557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137108077462260822927033485 51415529048347808597637557)
                  ·
                    refine ⟨4820205848282607056028521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51415529048347808597637557 4820205848282607056028521)
                    ·
                      refine ⟨3615154386211955292021391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820205848282607056028521 3615154386211955292021391)
                      ·
                        rfl

theorem cell23_7040488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_7040488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040488 prefixEnd_7040488 := by exact prefixLift 7040488
  have htrace : WordTrace (prefixWord ++ tailWord_7040488) baseStart_7040488 baseEnd_7040488 := by
    simpa [prefixWord, tailWord_7040488, baseEnd_7040488] using wordTrace_append hprefix tailTrace_7040488
  have hstable : (prefixWord ++ tailWord_7040488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040488).length < 2 ^ (prefixWord ++ tailWord_7040488).sum := by decide
  have hdescent : baseEnd_7040488 < baseStart_7040488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040531 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 6]
def baseStart_7040531 : Nat := 118140960795 + 7040531 * 2 ^ 59
def prefixEnd_7040531 : Nat := 4983230072969 + 3 ^ 40 * 7040531 * 2
def baseEnd_7040531 : Nat := 3615176465880098623783693

theorem tailTrace_7040531 : CollatzResearch.WordTrace tailWord_7040531 prefixEnd_7040531 3615176465880098623783693 := by
  unfold tailWord_7040531
  simp only [CollatzResearch.WordTrace]
  refine ⟨256789261656366088809809447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171192841104244059206539631 256789261656366088809809447)
  ·
    refine ⟨385183892484549133214714171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256789261656366088809809447 385183892484549133214714171)
    ·
      refine ⟨577775838726823699822071257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385183892484549133214714171 577775838726823699822071257)
      ·
        refine ⟨433331879045117774866553443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577775838726823699822071257 433331879045117774866553443)
        ·
          refine ⟨649997818567676662299830165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433331879045117774866553443 649997818567676662299830165)
          ·
            refine ⟨30468647745359843545304539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 649997818567676662299830165 30468647745359843545304539)
            ·
              refine ⟨45702971618039765317956809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30468647745359843545304539 45702971618039765317956809)
              ·
                refine ⟨34277228713529823988467607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45702971618039765317956809 34277228713529823988467607)
                ·
                  refine ⟨51415843070294735982701411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34277228713529823988467607 51415843070294735982701411)
                  ·
                    refine ⟨77123764605442103974052117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51415843070294735982701411 77123764605442103974052117)
                    ·
                      refine ⟨3615176465880098623783693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77123764605442103974052117 3615176465880098623783693)
                      ·
                        rfl

theorem cell23_7040531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_7040531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040531 prefixEnd_7040531 := by exact prefixLift 7040531
  have htrace : WordTrace (prefixWord ++ tailWord_7040531) baseStart_7040531 baseEnd_7040531 := by
    simpa [prefixWord, tailWord_7040531, baseEnd_7040531] using wordTrace_append hprefix tailTrace_7040531
  have hstable : (prefixWord ++ tailWord_7040531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040531).length < 2 ^ (prefixWord ++ tailWord_7040531).sum := by decide
  have hdescent : baseEnd_7040531 < baseStart_7040531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040538 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3]
def baseStart_7040538 : Nat := 118140960795 + 7040538 * 2 ^ 59
def prefixEnd_7040538 : Nat := 4983230072969 + 3 ^ 40 * 7040538 * 2
def baseEnd_7040538 : Nat := 3615180060244680096396161

theorem tailTrace_7040538 : CollatzResearch.WordTrace tailWord_7040538 prefixEnd_7040538 3615180060244680096396161 := by
  unfold tailWord_7040538
  simp only [CollatzResearch.WordTrace]
  refine ⟨64197379241835182251328567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171193011311560486003542845 64197379241835182251328567)
  ·
    refine ⟨96296068862752773376992851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64197379241835182251328567 96296068862752773376992851)
    ·
      refine ⟨144444103294129160065489277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96296068862752773376992851 144444103294129160065489277)
      ·
        refine ⟨54166538735298435024558479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144444103294129160065489277 54166538735298435024558479)
        ·
          refine ⟨81249808102947652536837719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54166538735298435024558479 81249808102947652536837719)
          ·
            refine ⟨121874712154421478805256579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81249808102947652536837719 121874712154421478805256579)
            ·
              refine ⟨182812068231632218207884869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121874712154421478805256579 182812068231632218207884869)
              ·
                refine ⟨34277262793431040913978413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182812068231632218207884869 34277262793431040913978413)
                ·
                  refine ⟨12853973547536640342741905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34277262793431040913978413 12853973547536640342741905)
                  ·
                    refine ⟨9640480160652480257056429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12853973547536640342741905 9640480160652480257056429)
                    ·
                      refine ⟨3615180060244680096396161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9640480160652480257056429 3615180060244680096396161)
                      ·
                        rfl

theorem cell23_7040538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_7040538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040538 prefixEnd_7040538 := by exact prefixLift 7040538
  have htrace : WordTrace (prefixWord ++ tailWord_7040538) baseStart_7040538 baseEnd_7040538 := by
    simpa [prefixWord, tailWord_7040538, baseEnd_7040538] using wordTrace_append hprefix tailTrace_7040538
  have hstable : (prefixWord ++ tailWord_7040538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040538).length < 2 ^ (prefixWord ++ tailWord_7040538).sum := by decide
  have hdescent : baseEnd_7040538 < baseStart_7040538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040545 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 2, 4]
def baseStart_7040545 : Nat := 118140960795 + 7040545 * 2 ^ 59
def prefixEnd_7040545 : Nat := 4983230072969 + 3 ^ 40 * 7040545 * 2
def baseEnd_7040545 : Nat := 1205061218203087189669543

theorem tailTrace_7040545 : CollatzResearch.WordTrace tailWord_7040545 prefixEnd_7040545 1205061218203087189669543 := by
  unfold tailWord_7040545
  simp only [CollatzResearch.WordTrace]
  refine ⟨256789772278315369200819089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171193181518876912800546059 256789772278315369200819089)
  ·
    refine ⟨192592329208736526900614317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256789772278315369200819089 192592329208736526900614317)
    ·
      refine ⟨72222123453276197587730369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192592329208736526900614317 72222123453276197587730369)
      ·
        refine ⟨54166592589957148190797777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72222123453276197587730369 54166592589957148190797777)
        ·
          refine ⟨40624944442467861143098333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54166592589957148190797777 40624944442467861143098333)
          ·
            refine ⟨15234354165925447928661875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40624944442467861143098333 15234354165925447928661875)
            ·
              refine ⟨22851531248888171892992813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15234354165925447928661875 22851531248888171892992813)
              ·
                refine ⟨8569324218333064459872305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22851531248888171892992813 8569324218333064459872305)
                ·
                  refine ⟨6426993163749798344904229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8569324218333064459872305 6426993163749798344904229)
                  ·
                    refine ⟨1205061218203087189669543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6426993163749798344904229 1205061218203087189669543)
                    ·
                      rfl

theorem cell23_7040545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_7040545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040545 prefixEnd_7040545 := by exact prefixLift 7040545
  have htrace : WordTrace (prefixWord ++ tailWord_7040545) baseStart_7040545 baseEnd_7040545 := by
    simpa [prefixWord, tailWord_7040545, baseEnd_7040545] using wordTrace_append hprefix tailTrace_7040545
  have hstable : (prefixWord ++ tailWord_7040545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040545).length < 2 ^ (prefixWord ++ tailWord_7040545).sum := by decide
  have hdescent : baseEnd_7040545 < baseStart_7040545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040558 : List Nat := [4, 1, 3, 1, 2, 1, 2, 9]
def baseStart_7040558 : Nat := 118140960795 + 7040558 * 2 ^ 59
def prefixEnd_7040558 : Nat := 4983230072969 + 3 ^ 40 * 7040558 * 2
def baseEnd_7040558 : Nat := 133895938142880371042447

theorem tailTrace_7040558 : CollatzResearch.WordTrace tailWord_7040558 prefixEnd_7040558 133895938142880371042447 := by
  unfold tailWord_7040558
  simp only [CollatzResearch.WordTrace]
  refine ⟨32098780803408534052630291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171193497618178848280694885 32098780803408534052630291)
  ·
    refine ⟨48148171205112801078945437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32098780803408534052630291 48148171205112801078945437)
    ·
      refine ⟨18055564201917300404604539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48148171205112801078945437 18055564201917300404604539)
      ·
        refine ⟨27083346302875950606906809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18055564201917300404604539 27083346302875950606906809)
        ·
          refine ⟨20312509727156962955180107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27083346302875950606906809 20312509727156962955180107)
          ·
            refine ⟨30468764590735444432770161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20312509727156962955180107 30468764590735444432770161)
            ·
              refine ⟨22851573443051583324577621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30468764590735444432770161 22851573443051583324577621)
              ·
                refine ⟨133895938142880371042447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22851573443051583324577621 133895938142880371042447)
                ·
                  rfl

theorem cell23_7040558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_7040558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040558 prefixEnd_7040558 := by exact prefixLift 7040558
  have htrace : WordTrace (prefixWord ++ tailWord_7040558) baseStart_7040558 baseEnd_7040558 := by
    simpa [prefixWord, tailWord_7040558, baseEnd_7040558] using wordTrace_append hprefix tailTrace_7040558
  have hstable : (prefixWord ++ tailWord_7040558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040558).length < 2 ^ (prefixWord ++ tailWord_7040558).sum := by decide
  have hdescent : baseEnd_7040558 < baseStart_7040558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040568 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 3, 3, 3]
def baseStart_7040568 : Nat := 118140960795 + 7040568 * 2 ^ 59
def prefixEnd_7040568 : Nat := 4983230072969 + 3 ^ 40 * 7040568 * 2
def baseEnd_7040568 : Nat := 3615195464664314979021023

theorem tailTrace_7040568 : CollatzResearch.WordTrace tailWord_7040568 prefixEnd_7040568 3615195464664314979021023 := by
  unfold tailWord_7040568
  simp only [CollatzResearch.WordTrace]
  refine ⟨128395305578616022064453179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171193740771488029419270905 128395305578616022064453179)
  ·
    refine ⟨192592958367924033096679769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128395305578616022064453179 192592958367924033096679769)
    ·
      refine ⟨144444718775943024822509827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192592958367924033096679769 144444718775943024822509827)
      ·
        refine ⟨216667078163914537233764741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144444718775943024822509827 216667078163914537233764741)
        ·
          refine ⟨40625077155733975731330889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216667078163914537233764741 40625077155733975731330889)
          ·
            refine ⟨30468807866800481798498167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40625077155733975731330889 30468807866800481798498167)
            ·
              refine ⟨45703211800200722697747251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30468807866800481798498167 45703211800200722697747251)
              ·
                refine ⟨68554817700301084046620877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45703211800200722697747251 68554817700301084046620877)
                ·
                  refine ⟨25708056637612906517482829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68554817700301084046620877 25708056637612906517482829)
                  ·
                    refine ⟨9640521239104839944056061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25708056637612906517482829 9640521239104839944056061)
                    ·
                      refine ⟨3615195464664314979021023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9640521239104839944056061 3615195464664314979021023)
                      ·
                        rfl

theorem cell23_7040568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_7040568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040568 prefixEnd_7040568 := by exact prefixLift 7040568
  have htrace : WordTrace (prefixWord ++ tailWord_7040568) baseStart_7040568 baseEnd_7040568 := by
    simpa [prefixWord, tailWord_7040568, baseEnd_7040568] using wordTrace_append hprefix tailTrace_7040568
  have hstable : (prefixWord ++ tailWord_7040568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040568).length < 2 ^ (prefixWord ++ tailWord_7040568).sum := by decide
  have hdescent : baseEnd_7040568 < baseStart_7040568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040572 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 1, 1, 5]
def baseStart_7040572 : Nat := 118140960795 + 7040572 * 2 ^ 59
def prefixEnd_7040572 : Nat := 4983230072969 + 3 ^ 40 * 7040572 * 2
def baseEnd_7040572 : Nat := 3615197518586932963371005

theorem tailTrace_7040572 : CollatzResearch.WordTrace tailWord_7040572 prefixEnd_7040572 3615197518586932963371005 := by
  unfold tailWord_7040572
  simp only [CollatzResearch.WordTrace]
  refine ⟨128395378524608776406025985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171193838032811701874701313 128395378524608776406025985)
  ·
    refine ⟨96296533893456582304519489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128395378524608776406025985 96296533893456582304519489)
    ·
      refine ⟨72222400420092436728389617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96296533893456582304519489 72222400420092436728389617)
      ·
        refine ⟨54166800315069327546292213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72222400420092436728389617 54166800315069327546292213)
        ·
          refine ⟨5078137529537749457464895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54166800315069327546292213 5078137529537749457464895)
          ·
            refine ⟨7617206294306624186197343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078137529537749457464895 7617206294306624186197343)
            ·
              refine ⟨11425809441459936279296015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617206294306624186197343 11425809441459936279296015)
              ·
                refine ⟨17138714162189904418944023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11425809441459936279296015 17138714162189904418944023)
                ·
                  refine ⟨25708071243284856628416035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17138714162189904418944023 25708071243284856628416035)
                  ·
                    refine ⟨38562106864927284942624053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25708071243284856628416035 38562106864927284942624053)
                    ·
                      refine ⟨3615197518586932963371005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38562106864927284942624053 3615197518586932963371005)
                      ·
                        rfl

theorem cell23_7040572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_7040572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040572 prefixEnd_7040572 := by exact prefixLift 7040572
  have htrace : WordTrace (prefixWord ++ tailWord_7040572) baseStart_7040572 baseEnd_7040572 := by
    simpa [prefixWord, tailWord_7040572, baseEnd_7040572] using wordTrace_append hprefix tailTrace_7040572
  have hstable : (prefixWord ++ tailWord_7040572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040572).length < 2 ^ (prefixWord ++ tailWord_7040572).sum := by decide
  have hdescent : baseEnd_7040572 < baseStart_7040572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040629 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_7040629 : Nat := 118140960795 + 7040629 * 2 ^ 59
def prefixEnd_7040629 : Nat := 4983230072969 + 3 ^ 40 * 7040629 * 2
def baseEnd_7040629 : Nat := 3615226786984239240358243

theorem tailTrace_7040629 : CollatzResearch.WordTrace tailWord_7040629 prefixEnd_7040629 3615226786984239240358243 := by
  unfold tailWord_7040629
  simp only [CollatzResearch.WordTrace]
  refine ⟨256792836010011051546876941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171195224006674034364584627 256792836010011051546876941)
  ·
    refine ⟨96297313503754144330078853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256792836010011051546876941 96297313503754144330078853)
    ·
      refine ⟨18055746281953902061889785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96297313503754144330078853 18055746281953902061889785)
      ·
        refine ⟨13541809711465426546417339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18055746281953902061889785 13541809711465426546417339)
        ·
          refine ⟨20312714567198139819626009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13541809711465426546417339 20312714567198139819626009)
          ·
            refine ⟨15234535925398604864719507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20312714567198139819626009 15234535925398604864719507)
            ·
              refine ⟨22851803888097907297079261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15234535925398604864719507 22851803888097907297079261)
              ·
                refine ⟨8569426458036715236404723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22851803888097907297079261 8569426458036715236404723)
                ·
                  refine ⟨12854139687055072854607085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8569426458036715236404723 12854139687055072854607085)
                  ·
                    refine ⟨4820302382645652320477657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12854139687055072854607085 4820302382645652320477657)
                    ·
                      refine ⟨3615226786984239240358243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820302382645652320477657 3615226786984239240358243)
                      ·
                        rfl

theorem cell23_7040629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_7040629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040629 prefixEnd_7040629 := by exact prefixLift 7040629
  have htrace : WordTrace (prefixWord ++ tailWord_7040629) baseStart_7040629 baseEnd_7040629 := by
    simpa [prefixWord, tailWord_7040629, baseEnd_7040629] using wordTrace_append hprefix tailTrace_7040629
  have hstable : (prefixWord ++ tailWord_7040629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040629).length < 2 ^ (prefixWord ++ tailWord_7040629).sum := by decide
  have hdescent : baseEnd_7040629 < baseStart_7040629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040631 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 11]
def baseStart_7040631 : Nat := 118140960795 + 7040631 * 2 ^ 59
def prefixEnd_7040631 : Nat := 4983230072969 + 3 ^ 40 * 7040631 * 2
def baseEnd_7040631 : Nat := 401691979327283136948137

theorem tailTrace_7040631 : CollatzResearch.WordTrace tailWord_7040631 prefixEnd_7040631 401691979327283136948137 := by
  unfold tailWord_7040631
  simp only [CollatzResearch.WordTrace]
  refine ⟨256792908956003805888449747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171195272637335870592299831 256792908956003805888449747)
  ·
    refine ⟨385189363434005708832674621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256792908956003805888449747 385189363434005708832674621)
    ·
      refine ⟨144446011287752140812252983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385189363434005708832674621 144446011287752140812252983)
      ·
        refine ⟨216669016931628211218379475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144446011287752140812252983 216669016931628211218379475)
        ·
          refine ⟨325003525397442316827569213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216669016931628211218379475 325003525397442316827569213)
          ·
            refine ⟨121876322024040868810338455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325003525397442316827569213 121876322024040868810338455)
            ·
              refine ⟨182814483036061303215507683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121876322024040868810338455 182814483036061303215507683)
              ·
                refine ⟨274221724554091954823261525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182814483036061303215507683 274221724554091954823261525)
                ·
                  refine ⟨401691979327283136948137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 274221724554091954823261525 401691979327283136948137)
                  ·
                    rfl

theorem cell23_7040631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 11].length) (baseStart_7040631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040631 prefixEnd_7040631 := by exact prefixLift 7040631
  have htrace : WordTrace (prefixWord ++ tailWord_7040631) baseStart_7040631 baseEnd_7040631 := by
    simpa [prefixWord, tailWord_7040631, baseEnd_7040631] using wordTrace_append hprefix tailTrace_7040631
  have hstable : (prefixWord ++ tailWord_7040631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040631).length < 2 ^ (prefixWord ++ tailWord_7040631).sum := by decide
  have hdescent : baseEnd_7040631 < baseStart_7040631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040695 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 2, 5]
def baseStart_7040695 : Nat := 118140960795 + 7040695 * 2 ^ 59
def prefixEnd_7040695 : Nat := 4983230072969 + 3 ^ 40 * 7040695 * 2
def baseEnd_7040695 : Nat := 1205086892235811994044313

theorem tailTrace_7040695 : CollatzResearch.WordTrace tailWord_7040695 prefixEnd_7040695 1205086892235811994044313 := by
  unfold tailWord_7040695
  simp only [CollatzResearch.WordTrace]
  refine ⟨256795243227771944818779539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171196828818514629879186359 256795243227771944818779539)
  ·
    refine ⟨385192864841657917228169309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256795243227771944818779539 385192864841657917228169309)
    ·
      refine ⟨144447324315621718960563491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385192864841657917228169309 144447324315621718960563491)
      ·
        refine ⟨216670986473432578440845237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144447324315621718960563491 216670986473432578440845237)
        ·
          refine ⟨20312904981884304228829241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216670986473432578440845237 20312904981884304228829241)
          ·
            refine ⟨15234678736413228171621931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20312904981884304228829241 15234678736413228171621931)
            ·
              refine ⟨22852018104619842257432897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15234678736413228171621931 22852018104619842257432897)
              ·
                refine ⟨17139013578464881693074673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22852018104619842257432897 17139013578464881693074673)
                ·
                  refine ⟨12854260183848661269806005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17139013578464881693074673 12854260183848661269806005)
                  ·
                    refine ⟨1205086892235811994044313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12854260183848661269806005 1205086892235811994044313)
                    ·
                      rfl

theorem cell23_7040695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_7040695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040695 prefixEnd_7040695 := by exact prefixLift 7040695
  have htrace : WordTrace (prefixWord ++ tailWord_7040695) baseStart_7040695 baseEnd_7040695 := by
    simpa [prefixWord, tailWord_7040695, baseEnd_7040695] using wordTrace_append hprefix tailTrace_7040695
  have hstable : (prefixWord ++ tailWord_7040695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040695).length < 2 ^ (prefixWord ++ tailWord_7040695).sum := by decide
  have hdescent : baseEnd_7040695 < baseStart_7040695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040710 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7040710 : Nat := 118140960795 + 7040710 * 2 ^ 59
def prefixEnd_7040710 : Nat := 4983230072969 + 3 ^ 40 * 7040710 * 2
def baseEnd_7040710 : Nat := 3615268378917253423445371

theorem tailTrace_7040710 : CollatzResearch.WordTrace tailWord_7040710 prefixEnd_7040710 3615268378917253423445371 := by
  unfold tailWord_7040710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024868447584925074392987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 171197193548478401587050389 8024868447584925074392987)
  ·
    refine ⟨12037302671377387611589481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8024868447584925074392987 12037302671377387611589481)
    ·
      refine ⟨9027977003533040708692111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12037302671377387611589481 9027977003533040708692111)
      ·
        refine ⟨13541965505299561063038167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9027977003533040708692111 13541965505299561063038167)
        ·
          refine ⟨20312948257949341594557251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13541965505299561063038167 20312948257949341594557251)
          ·
            refine ⟨30469422386924012391835877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20312948257949341594557251 30469422386924012391835877)
            ·
              refine ⟨5713016697548252323469227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30469422386924012391835877 5713016697548252323469227)
              ·
                refine ⟨8569525046322378485203841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713016697548252323469227 8569525046322378485203841)
                ·
                  refine ⟨6427143784741783863902881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8569525046322378485203841 6427143784741783863902881)
                  ·
                    refine ⟨4820357838556337897927161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6427143784741783863902881 4820357838556337897927161)
                    ·
                      refine ⟨3615268378917253423445371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820357838556337897927161 3615268378917253423445371)
                      ·
                        rfl

theorem cell23_7040710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7040710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040710 prefixEnd_7040710 := by exact prefixLift 7040710
  have htrace : WordTrace (prefixWord ++ tailWord_7040710) baseStart_7040710 baseEnd_7040710 := by
    simpa [prefixWord, tailWord_7040710, baseEnd_7040710] using wordTrace_append hprefix tailTrace_7040710
  have hstable : (prefixWord ++ tailWord_7040710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040710).length < 2 ^ (prefixWord ++ tailWord_7040710).sum := by decide
  have hdescent : baseEnd_7040710 < baseStart_7040710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040715 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 2, 4, 2]
def baseStart_7040715 : Nat := 118140960795 + 7040715 * 2 ^ 59
def prefixEnd_7040715 : Nat := 4983230072969 + 3 ^ 40 * 7040715 * 2
def baseEnd_7040715 : Nat := 3615270946320525903882847

theorem tailTrace_7040715 : CollatzResearch.WordTrace tailWord_7040715 prefixEnd_7040715 3615270946320525903882847 := by
  unfold tailWord_7040715
  simp only [CollatzResearch.WordTrace]
  refine ⟨256795972687699488234507599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171197315125132992156338399 256795972687699488234507599)
  ·
    refine ⟨385193959031549232351761399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256795972687699488234507599 385193959031549232351761399)
    ·
      refine ⟨577790938547323848527642099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385193959031549232351761399 577790938547323848527642099)
      ·
        refine ⟨866686407820985772791463149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577790938547323848527642099 866686407820985772791463149)
        ·
          refine ⟨325007402932869664796798681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 866686407820985772791463149 325007402932869664796798681)
          ·
            refine ⟨243755552199652248597599011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325007402932869664796798681 243755552199652248597599011)
            ·
              refine ⟨365633328299478372896398517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243755552199652248597599011 365633328299478372896398517)
              ·
                refine ⟨34278124528076097459037361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 365633328299478372896398517 34278124528076097459037361)
                ·
                  refine ⟨25708593396057073094278021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34278124528076097459037361 25708593396057073094278021)
                  ·
                    refine ⟨4820361261760701205177129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25708593396057073094278021 4820361261760701205177129)
                    ·
                      refine ⟨3615270946320525903882847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820361261760701205177129 3615270946320525903882847)
                      ·
                        rfl

theorem cell23_7040715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 4, 2].length) (baseStart_7040715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040715 prefixEnd_7040715 := by exact prefixLift 7040715
  have htrace : WordTrace (prefixWord ++ tailWord_7040715) baseStart_7040715 baseEnd_7040715 := by
    simpa [prefixWord, tailWord_7040715, baseEnd_7040715] using wordTrace_append hprefix tailTrace_7040715
  have hstable : (prefixWord ++ tailWord_7040715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040715).length < 2 ^ (prefixWord ++ tailWord_7040715).sum := by decide
  have hdescent : baseEnd_7040715 < baseStart_7040715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040759 : List Nat := [1, 1, 3, 1, 1, 1, 8, 2, 1, 4]
def baseStart_7040759 : Nat := 118140960795 + 7040759 * 2 ^ 59
def prefixEnd_7040759 : Nat := 4983230072969 + 3 ^ 40 * 7040759 * 2
def baseEnd_7040759 : Nat := 1205097846489774577244215

theorem tailTrace_7040759 : CollatzResearch.WordTrace tailWord_7040759 prefixEnd_7040759 1205097846489774577244215 := by
  unfold tailWord_7040759
  simp only [CollatzResearch.WordTrace]
  refine ⟨256797577499540083749109331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171198384999693389166072887 256797577499540083749109331)
  ·
    refine ⟨385196366249310125623663997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256797577499540083749109331 385196366249310125623663997)
    ·
      refine ⟨144448637343491297108873999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385196366249310125623663997 144448637343491297108873999)
      ·
        refine ⟨216672956015236945663310999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144448637343491297108873999 216672956015236945663310999)
        ·
          refine ⟨325009434022855418494966499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216672956015236945663310999 325009434022855418494966499)
          ·
            refine ⟨487514151034283127742449749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325009434022855418494966499 487514151034283127742449749)
            ·
              refine ⟨5713056457433005403231833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 487514151034283127742449749 5713056457433005403231833)
              ·
                refine ⟨4284792343074754052423875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5713056457433005403231833 4284792343074754052423875)
                ·
                  refine ⟨6427188514612131078635813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4284792343074754052423875 6427188514612131078635813)
                  ·
                    refine ⟨1205097846489774577244215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6427188514612131078635813 1205097846489774577244215)
                    ·
                      rfl

theorem cell23_7040759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_7040759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040759 prefixEnd_7040759 := by exact prefixLift 7040759
  have htrace : WordTrace (prefixWord ++ tailWord_7040759) baseStart_7040759 baseEnd_7040759 := by
    simpa [prefixWord, tailWord_7040759, baseEnd_7040759] using wordTrace_append hprefix tailTrace_7040759
  have hstable : (prefixWord ++ tailWord_7040759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040759).length < 2 ^ (prefixWord ++ tailWord_7040759).sum := by decide
  have hdescent : baseEnd_7040759 < baseStart_7040759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040782 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_7040782 : Nat := 118140960795 + 7040782 * 2 ^ 59
def prefixEnd_7040782 : Nat := 4983230072969 + 3 ^ 40 * 7040782 * 2
def baseEnd_7040782 : Nat := 3615305349524377141745039

theorem tailTrace_7040782 : CollatzResearch.WordTrace tailWord_7040782 prefixEnd_7040782 3615305349524377141745039 := by
  unfold tailWord_7040782
  simp only [CollatzResearch.WordTrace]
  refine ⟨32099802047307094834649575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171198944252304505784797733 32099802047307094834649575)
  ·
    refine ⟨48149703070960642251974363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32099802047307094834649575 48149703070960642251974363)
    ·
      refine ⟨72224554606440963377961545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48149703070960642251974363 72224554606440963377961545)
      ·
        refine ⟨54168415954830722533471159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72224554606440963377961545 54168415954830722533471159)
        ·
          refine ⟨81252623932246083800206739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54168415954830722533471159 81252623932246083800206739)
          ·
            refine ⟨121878935898369125700310109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81252623932246083800206739 121878935898369125700310109)
            ·
              refine ⟨45704600961888422137616291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121878935898369125700310109 45704600961888422137616291)
              ·
                refine ⟨68556901442832633206424437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45704600961888422137616291 68556901442832633206424437)
                ·
                  refine ⟨6427209510265559363102291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68556901442832633206424437 6427209510265559363102291)
                  ·
                    refine ⟨9640814265398339044653437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6427209510265559363102291 9640814265398339044653437)
                    ·
                      refine ⟨3615305349524377141745039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9640814265398339044653437 3615305349524377141745039)
                      ·
                        rfl

theorem cell23_7040782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_7040782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040782 prefixEnd_7040782 := by exact prefixLift 7040782
  have htrace : WordTrace (prefixWord ++ tailWord_7040782) baseStart_7040782 baseEnd_7040782 := by
    simpa [prefixWord, tailWord_7040782, baseEnd_7040782] using wordTrace_append hprefix tailTrace_7040782
  have hstable : (prefixWord ++ tailWord_7040782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040782).length < 2 ^ (prefixWord ++ tailWord_7040782).sum := by decide
  have hdescent : baseEnd_7040782 < baseStart_7040782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040785 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 1, 5]
def baseStart_7040785 : Nat := 118140960795 + 7040785 * 2 ^ 59
def prefixEnd_7040785 : Nat := 4983230072969 + 3 ^ 40 * 7040785 * 2
def baseEnd_7040785 : Nat := 1205102296655446876669175

theorem tailTrace_7040785 : CollatzResearch.WordTrace tailWord_7040785 prefixEnd_7040785 1205102296655446876669175 := by
  unfold tailWord_7040785
  simp only [CollatzResearch.WordTrace]
  refine ⟨256798525797445890189555809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171199017198297260126370539 256798525797445890189555809)
  ·
    refine ⟨192598894348084417642166857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256798525797445890189555809 192598894348084417642166857)
    ·
      refine ⟨144449170761063313231625143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192598894348084417642166857 144449170761063313231625143)
      ·
        refine ⟨216673756141594969847437715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144449170761063313231625143 216673756141594969847437715)
        ·
          refine ⟨325010634212392454771156573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216673756141594969847437715 325010634212392454771156573)
          ·
            refine ⟨121878987829647170539183715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325010634212392454771156573 121878987829647170539183715)
            ·
              refine ⟨182818481744470755808775573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121878987829647170539183715 182818481744470755808775573)
              ·
                refine ⟨8569616331772066678536355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182818481744470755808775573 8569616331772066678536355)
                ·
                  refine ⟨12854424497658100017804533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8569616331772066678536355 12854424497658100017804533)
                  ·
                    refine ⟨1205102296655446876669175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12854424497658100017804533 1205102296655446876669175)
                    ·
                      rfl

theorem cell23_7040785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_7040785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040785 prefixEnd_7040785 := by exact prefixLift 7040785
  have htrace : WordTrace (prefixWord ++ tailWord_7040785) baseStart_7040785 baseEnd_7040785 := by
    simpa [prefixWord, tailWord_7040785, baseEnd_7040785] using wordTrace_append hprefix tailTrace_7040785
  have hstable : (prefixWord ++ tailWord_7040785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040785).length < 2 ^ (prefixWord ++ tailWord_7040785).sum := by decide
  have hdescent : baseEnd_7040785 < baseStart_7040785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040786 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_7040786 : Nat := 118140960795 + 7040786 * 2 ^ 59
def prefixEnd_7040786 : Nat := 4983230072969 + 3 ^ 40 * 7040786 * 2
def baseEnd_7040786 : Nat := 3615307403446995126095021

theorem tailTrace_7040786 : CollatzResearch.WordTrace tailWord_7040786 prefixEnd_7040786 3615307403446995126095021 := by
  unfold tailWord_7040786
  simp only [CollatzResearch.WordTrace]
  refine ⟨64199640567610566840085553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171199041513628178240228141 64199640567610566840085553)
  ·
    refine ⟨48149730425707925130064165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64199640567610566840085553 48149730425707925130064165)
    ·
      refine ⟨9028074454820235961887031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48149730425707925130064165 9028074454820235961887031)
      ·
        refine ⟨13542111682230353942830547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9028074454820235961887031 13542111682230353942830547)
        ·
          refine ⟨20313167523345530914245821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13542111682230353942830547 20313167523345530914245821)
          ·
            refine ⟨7617437821254574092842183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20313167523345530914245821 7617437821254574092842183)
            ·
              refine ⟨11426156731881861139263275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617437821254574092842183 11426156731881861139263275)
              ·
                refine ⟨17139235097822791708894913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11426156731881861139263275 17139235097822791708894913)
                ·
                  refine ⟨12854426323367093781671185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17139235097822791708894913 12854426323367093781671185)
                  ·
                    refine ⟨9640819742525320336253389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12854426323367093781671185 9640819742525320336253389)
                    ·
                      refine ⟨3615307403446995126095021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9640819742525320336253389 3615307403446995126095021)
                      ·
                        rfl

theorem cell23_7040786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_7040786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040786 prefixEnd_7040786 := by exact prefixLift 7040786
  have htrace : WordTrace (prefixWord ++ tailWord_7040786) baseStart_7040786 baseEnd_7040786 := by
    simpa [prefixWord, tailWord_7040786, baseEnd_7040786] using wordTrace_append hprefix tailTrace_7040786
  have hstable : (prefixWord ++ tailWord_7040786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040786).length < 2 ^ (prefixWord ++ tailWord_7040786).sum := by decide
  have hdescent : baseEnd_7040786 < baseStart_7040786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040802 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_7040802 : Nat := 118140960795 + 7040802 * 2 ^ 59
def prefixEnd_7040802 : Nat := 4983230072969 + 3 ^ 40 * 7040802 * 2
def baseEnd_7040802 : Nat := 1205105206379155687831649

theorem tailTrace_7040802 : CollatzResearch.WordTrace tailWord_7040802 prefixEnd_7040802 1205105206379155687831649 := by
  unfold tailWord_7040802
  simp only [CollatzResearch.WordTrace]
  refine ⟨64199786459596075523231165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171199430558922868061949773 64199786459596075523231165)
  ·
    refine ⟨24074919922348528321211687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64199786459596075523231165 24074919922348528321211687)
    ·
      refine ⟨36112379883522792481817531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24074919922348528321211687 36112379883522792481817531)
      ·
        refine ⟨54168569825284188722726297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36112379883522792481817531 54168569825284188722726297)
        ·
          refine ⟨40626427368963141542044723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54168569825284188722726297 40626427368963141542044723)
          ·
            refine ⟨60939641053444712313067085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40626427368963141542044723 60939641053444712313067085)
            ·
              refine ⟨22852365395041767117400157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60939641053444712313067085 22852365395041767117400157)
              ·
                refine ⟨8569637023140662669025059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22852365395041767117400157 8569637023140662669025059)
                ·
                  refine ⟨12854455534710994003537589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8569637023140662669025059 12854455534710994003537589)
                  ·
                    refine ⟨1205105206379155687831649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12854455534710994003537589 1205105206379155687831649)
                    ·
                      rfl

theorem cell23_7040802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_7040802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040802 prefixEnd_7040802 := by exact prefixLift 7040802
  have htrace : WordTrace (prefixWord ++ tailWord_7040802) baseStart_7040802 baseEnd_7040802 := by
    simpa [prefixWord, tailWord_7040802, baseEnd_7040802] using wordTrace_append hprefix tailTrace_7040802
  have hstable : (prefixWord ++ tailWord_7040802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040802).length < 2 ^ (prefixWord ++ tailWord_7040802).sum := by decide
  have hdescent : baseEnd_7040802 < baseStart_7040802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040815 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 4, 4]
def baseStart_7040815 : Nat := 118140960795 + 7040815 * 2 ^ 59
def prefixEnd_7040815 : Nat := 4983230072969 + 3 ^ 40 * 7040815 * 2
def baseEnd_7040815 : Nat := 1205107431461991837544129

theorem tailTrace_7040815 : CollatzResearch.WordTrace tailWord_7040815 prefixEnd_7040815 1205107431461991837544129 := by
  unfold tailWord_7040815
  simp only [CollatzResearch.WordTrace]
  refine ⟨256799619987337205313147899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171199746658224803542098599 256799619987337205313147899)
  ·
    refine ⟨385199429981005807969721849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256799619987337205313147899 385199429981005807969721849)
    ·
      refine ⟨288899572485754355977291387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385199429981005807969721849 288899572485754355977291387)
      ·
        refine ⟨433349358728631533965937081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288899572485754355977291387 433349358728631533965937081)
        ·
          refine ⟨325012019046473650474452811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433349358728631533965937081 325012019046473650474452811)
          ·
            refine ⟨487518028569710475711679217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325012019046473650474452811 487518028569710475711679217)
            ·
              refine ⟨365638521427282856783759413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487518028569710475711679217 365638521427282856783759413)
              ·
                refine ⟨34278611383807767823477445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 365638521427282856783759413 34278611383807767823477445)
                ·
                  refine ⟨6427239634463956466902021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34278611383807767823477445 6427239634463956466902021)
                  ·
                    refine ⟨1205107431461991837544129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6427239634463956466902021 1205107431461991837544129)
                    ·
                      rfl

theorem cell23_7040815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 4].length) (baseStart_7040815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040815 prefixEnd_7040815 := by exact prefixLift 7040815
  have htrace : WordTrace (prefixWord ++ tailWord_7040815) baseStart_7040815 baseEnd_7040815 := by
    simpa [prefixWord, tailWord_7040815, baseEnd_7040815] using wordTrace_append hprefix tailTrace_7040815
  have hstable : (prefixWord ++ tailWord_7040815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040815).length < 2 ^ (prefixWord ++ tailWord_7040815).sum := by decide
  have hdescent : baseEnd_7040815 < baseStart_7040815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040835 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 6]
def baseStart_7040835 : Nat := 118140960795 + 7040835 * 2 ^ 59
def prefixEnd_7040835 : Nat := 4983230072969 + 3 ^ 40 * 7040835 * 2
def baseEnd_7040835 : Nat := 3615332563999065434382295

theorem tailTrace_7040835 : CollatzResearch.WordTrace tailWord_7040835 prefixEnd_7040835 3615332563999065434382295 := by
  unfold tailWord_7040835
  simp only [CollatzResearch.WordTrace]
  refine ⟨256800349447264748728875959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171200232964843165819250639 256800349447264748728875959)
  ·
    refine ⟨385200524170897123093313939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256800349447264748728875959 385200524170897123093313939)
    ·
      refine ⟨577800786256345684639970909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385200524170897123093313939 577800786256345684639970909)
      ·
        refine ⟨216675294846129631739989091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577800786256345684639970909 216675294846129631739989091)
        ·
          refine ⟨325012942269194447609983637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216675294846129631739989091 325012942269194447609983637)
          ·
            refine ⟨15234981668868489731717983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 325012942269194447609983637 15234981668868489731717983)
            ·
              refine ⟨22852472503302734597576975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15234981668868489731717983 22852472503302734597576975)
              ·
                refine ⟨34278708754954101896365463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22852472503302734597576975 34278708754954101896365463)
                ·
                  refine ⟨51418063132431152844548195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34278708754954101896365463 51418063132431152844548195)
                  ·
                    refine ⟨77127094698646729266822293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51418063132431152844548195 77127094698646729266822293)
                    ·
                      refine ⟨3615332563999065434382295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77127094698646729266822293 3615332563999065434382295)
                      ·
                        rfl

theorem cell23_7040835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_7040835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040835 prefixEnd_7040835 := by exact prefixLift 7040835
  have htrace : WordTrace (prefixWord ++ tailWord_7040835) baseStart_7040835 baseEnd_7040835 := by
    simpa [prefixWord, tailWord_7040835, baseEnd_7040835] using wordTrace_append hprefix tailTrace_7040835
  have hstable : (prefixWord ++ tailWord_7040835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040835).length < 2 ^ (prefixWord ++ tailWord_7040835).sum := by decide
  have hdescent : baseEnd_7040835 < baseStart_7040835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040839 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 3, 2, 2]
def baseStart_7040839 : Nat := 118140960795 + 7040839 * 2 ^ 59
def prefixEnd_7040839 : Nat := 4983230072969 + 3 ^ 40 * 7040839 * 2
def baseEnd_7040839 : Nat := 3615334617921683418732277

theorem tailTrace_7040839 : CollatzResearch.WordTrace tailWord_7040839 prefixEnd_7040839 3615334617921683418732277 := by
  unfold tailWord_7040839
  simp only [CollatzResearch.WordTrace]
  refine ⟨256800495339250257412021571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171200330226166838274681047 256800495339250257412021571)
  ·
    refine ⟨385200743008875386118032357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256800495339250257412021571 385200743008875386118032357)
    ·
      refine ⟨72225139314164134897131067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385200743008875386118032357 72225139314164134897131067)
      ·
        refine ⟨108337708971246202345696601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72225139314164134897131067 108337708971246202345696601)
        ·
          refine ⟨81253281728434651759272451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108337708971246202345696601 81253281728434651759272451)
          ·
            refine ⟨121879922592651977638908677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81253281728434651759272451 121879922592651977638908677)
            ·
              refine ⟨22852485486122245807295377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121879922592651977638908677 22852485486122245807295377)
              ·
                refine ⟨17139364114591684355471533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22852485486122245807295377 17139364114591684355471533)
                ·
                  refine ⟨6427261542971881633301825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17139364114591684355471533 6427261542971881633301825)
                  ·
                    refine ⟨4820446157228911224976369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6427261542971881633301825 4820446157228911224976369)
                    ·
                      refine ⟨3615334617921683418732277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820446157228911224976369 3615334617921683418732277)
                      ·
                        rfl

theorem cell23_7040839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_7040839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040839 prefixEnd_7040839 := by exact prefixLift 7040839
  have htrace : WordTrace (prefixWord ++ tailWord_7040839) baseStart_7040839 baseEnd_7040839 := by
    simpa [prefixWord, tailWord_7040839, baseEnd_7040839] using wordTrace_append hprefix tailTrace_7040839
  have hstable : (prefixWord ++ tailWord_7040839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040839).length < 2 ^ (prefixWord ++ tailWord_7040839).sum := by decide
  have hdescent : baseEnd_7040839 < baseStart_7040839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040882 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 2, 7, 2]
def baseStart_7040882 : Nat := 118140960795 + 7040882 * 2 ^ 59
def prefixEnd_7040882 : Nat := 4983230072969 + 3 ^ 40 * 7040882 * 2
def baseEnd_7040882 : Nat := 3615356697589826750494579

theorem tailTrace_7040882 : CollatzResearch.WordTrace tailWord_7040882 prefixEnd_7040882 3615356697589826750494579 := by
  unfold tailWord_7040882
  simp only [CollatzResearch.WordTrace]
  refine ⟨64200515919523618938959225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171201375785396317170557933 64200515919523618938959225)
  ·
    refine ⟨48150386939642714204219419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64200515919523618938959225 48150386939642714204219419)
    ·
      refine ⟨72225580409464071306329129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48150386939642714204219419 72225580409464071306329129)
      ·
        refine ⟨54169185307098053479746847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72225580409464071306329129 54169185307098053479746847)
        ·
          refine ⟨81253777960647080219620271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54169185307098053479746847 81253777960647080219620271)
          ·
            refine ⟨121880666940970620329430407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81253777960647080219620271 121880666940970620329430407)
            ·
              refine ⟨182821000411455930494145611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121880666940970620329430407 182821000411455930494145611)
              ·
                refine ⟨274231500617183895741218417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182821000411455930494145611 274231500617183895741218417)
                ·
                  refine ⟨205673625462887921805913813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274231500617183895741218417 205673625462887921805913813)
                  ·
                    refine ⟨4820475596786435667326105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 205673625462887921805913813 4820475596786435667326105)
                    ·
                      refine ⟨3615356697589826750494579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820475596786435667326105 3615356697589826750494579)
                      ·
                        rfl

theorem cell23_7040882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_7040882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040882 prefixEnd_7040882 := by exact prefixLift 7040882
  have htrace : WordTrace (prefixWord ++ tailWord_7040882) baseStart_7040882 baseEnd_7040882 := by
    simpa [prefixWord, tailWord_7040882, baseEnd_7040882] using wordTrace_append hprefix tailTrace_7040882
  have hstable : (prefixWord ++ tailWord_7040882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040882).length < 2 ^ (prefixWord ++ tailWord_7040882).sum := by decide
  have hdescent : baseEnd_7040882 < baseStart_7040882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040889 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 2, 1, 3]
def baseStart_7040889 : Nat := 118140960795 + 7040889 * 2 ^ 59
def prefixEnd_7040889 : Nat := 4983230072969 + 3 ^ 40 * 7040889 * 2
def baseEnd_7040889 : Nat := 3615360291954408223107047

theorem tailTrace_7040889 : CollatzResearch.WordTrace tailWord_7040889 prefixEnd_7040889 3615360291954408223107047 := by
  unfold tailWord_7040889
  simp only [CollatzResearch.WordTrace]
  refine ⟨256802318989069115951341721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171201545992712743967561147 256802318989069115951341721)
  ·
    refine ⟨192601739241801836963506291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256802318989069115951341721 192601739241801836963506291)
    ·
      refine ⟨288902608862702755445259437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192601739241801836963506291 288902608862702755445259437)
      ·
        refine ⟨108338478323513533291972289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288902608862702755445259437 108338478323513533291972289)
        ·
          refine ⟨81253858742635149968979217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108338478323513533291972289 81253858742635149968979217)
          ·
            refine ⟨60940394056976362476734413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81253858742635149968979217 60940394056976362476734413)
            ·
              refine ⟨22852647771366135928775405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60940394056976362476734413 22852647771366135928775405)
              ·
                refine ⟨8569742914262300973290777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22852647771366135928775405 8569742914262300973290777)
                ·
                  refine ⟨6427307185696725729968083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8569742914262300973290777 6427307185696725729968083)
                  ·
                    refine ⟨9640960778545088594952125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6427307185696725729968083 9640960778545088594952125)
                    ·
                      refine ⟨3615360291954408223107047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9640960778545088594952125 3615360291954408223107047)
                      ·
                        rfl

theorem cell23_7040889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_7040889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040889 prefixEnd_7040889 := by exact prefixLift 7040889
  have htrace : WordTrace (prefixWord ++ tailWord_7040889) baseStart_7040889 baseEnd_7040889 := by
    simpa [prefixWord, tailWord_7040889, baseEnd_7040889] using wordTrace_append hprefix tailTrace_7040889
  have hstable : (prefixWord ++ tailWord_7040889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040889).length < 2 ^ (prefixWord ++ tailWord_7040889).sum := by decide
  have hdescent : baseEnd_7040889 < baseStart_7040889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040899 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 3, 3, 2]
def baseStart_7040899 : Nat := 118140960795 + 7040899 * 2 ^ 59
def prefixEnd_7040899 : Nat := 4983230072969 + 3 ^ 40 * 7040899 * 2
def baseEnd_7040899 : Nat := 3615365426760953183982001

theorem tailTrace_7040899 : CollatzResearch.WordTrace tailWord_7040899 prefixEnd_7040899 3615365426760953183982001 := by
  unfold tailWord_7040899
  simp only [CollatzResearch.WordTrace]
  refine ⟨256802683719032887659205751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171201789146021925106137167 256802683719032887659205751)
  ·
    refine ⟨385204025578549331488808627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256802683719032887659205751 385204025578549331488808627)
    ·
      refine ⟨577806038367823997233212941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385204025578549331488808627 577806038367823997233212941)
      ·
        refine ⟨216677264387933998962454853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577806038367823997233212941 216677264387933998962454853)
        ·
          refine ⟨40626987072737624805460285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216677264387933998962454853 40626987072737624805460285)
          ·
            refine ⟨15235120152276609302047607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40626987072737624805460285 15235120152276609302047607)
            ·
              refine ⟨22852680228414913953071411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15235120152276609302047607 22852680228414913953071411)
              ·
                refine ⟨34279020342622370929607117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22852680228414913953071411 34279020342622370929607117)
                ·
                  refine ⟨12854632628483389098602669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34279020342622370929607117 12854632628483389098602669)
                  ·
                    refine ⟨4820487235681270911976001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12854632628483389098602669 4820487235681270911976001)
                    ·
                      refine ⟨3615365426760953183982001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820487235681270911976001 3615365426760953183982001)
                      ·
                        rfl

theorem cell23_7040899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_7040899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040899 prefixEnd_7040899 := by exact prefixLift 7040899
  have htrace : WordTrace (prefixWord ++ tailWord_7040899) baseStart_7040899 baseEnd_7040899 := by
    simpa [prefixWord, tailWord_7040899, baseEnd_7040899] using wordTrace_append hprefix tailTrace_7040899
  have hstable : (prefixWord ++ tailWord_7040899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040899).length < 2 ^ (prefixWord ++ tailWord_7040899).sum := by decide
  have hdescent : baseEnd_7040899 < baseStart_7040899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040912 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 3, 4, 2]
def baseStart_7040912 : Nat := 118140960795 + 7040912 * 2 ^ 59
def prefixEnd_7040912 : Nat := 4983230072969 + 3 ^ 40 * 7040912 * 2
def baseEnd_7040912 : Nat := 3615372102009461633119441

theorem tailTrace_7040912 : CollatzResearch.WordTrace tailWord_7040912 prefixEnd_7040912 3615372102009461633119441 := by
  unfold tailWord_7040912
  simp only [CollatzResearch.WordTrace]
  refine ⟨128401578933992895439714495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171202105245323860586285993 128401578933992895439714495)
  ·
    refine ⟨192602368400989343159571743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128401578933992895439714495 192602368400989343159571743)
    ·
      refine ⟨288903552601484014739357615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192602368400989343159571743 288903552601484014739357615)
      ·
        refine ⟨433355328902226022109036423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288903552601484014739357615 433355328902226022109036423)
        ·
          refine ⟨650032993353339033163554635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433355328902226022109036423 650032993353339033163554635)
          ·
            refine ⟨975049490030008549745331953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650032993353339033163554635 975049490030008549745331953)
            ·
              refine ⟨731287117522506412308998965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975049490030008549745331953 731287117522506412308998965)
              ·
                refine ⟨68558167267734976153968653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731287117522506412308998965 68558167267734976153968653)
                ·
                  refine ⟨25709312725400616057738245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68558167267734976153968653 25709312725400616057738245)
                  ·
                    refine ⟨4820496136012615510825921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25709312725400616057738245 4820496136012615510825921)
                    ·
                      refine ⟨3615372102009461633119441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820496136012615510825921 3615372102009461633119441)
                      ·
                        rfl

theorem cell23_7040912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 4, 2].length) (baseStart_7040912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040912 prefixEnd_7040912 := by exact prefixLift 7040912
  have htrace : WordTrace (prefixWord ++ tailWord_7040912) baseStart_7040912 baseEnd_7040912 := by
    simpa [prefixWord, tailWord_7040912, baseEnd_7040912] using wordTrace_append hprefix tailTrace_7040912
  have hstable : (prefixWord ++ tailWord_7040912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040912).length < 2 ^ (prefixWord ++ tailWord_7040912).sum := by decide
  have hdescent : baseEnd_7040912 < baseStart_7040912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7040932 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_7040932 : Nat := 118140960795 + 7040932 * 2 ^ 59
def prefixEnd_7040932 : Nat := 4983230072969 + 3 ^ 40 * 7040932 * 2
def baseEnd_7040932 : Nat := 3615382371622551554869349

theorem tailTrace_7040932 : CollatzResearch.WordTrace tailWord_7040932 prefixEnd_7040932 3615382371622551554869349 := by
  unfold tailWord_7040932
  simp only [CollatzResearch.WordTrace]
  refine ⟨128401943663956667147578525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171202591551942222863438033 128401943663956667147578525)
  ·
    refine ⟨48150728873983750180341947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128401943663956667147578525 48150728873983750180341947)
    ·
      refine ⟨72226093310975625270512921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48150728873983750180341947 72226093310975625270512921)
      ·
        refine ⟨54169569983231718952884691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72226093310975625270512921 54169569983231718952884691)
        ·
          refine ⟨81254354974847578429327037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54169569983231718952884691 81254354974847578429327037)
          ·
            refine ⟨30470383115567841910997639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81254354974847578429327037 30470383115567841910997639)
            ·
              refine ⟨45705574673351762866496459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30470383115567841910997639 45705574673351762866496459)
              ·
                refine ⟨68558362010027644299744689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45705574673351762866496459 68558362010027644299744689)
                ·
                  refine ⟨51418771507520733224808517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68558362010027644299744689 51418771507520733224808517)
                  ·
                    refine ⟨9641019657660137479651597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51418771507520733224808517 9641019657660137479651597)
                    ·
                      refine ⟨3615382371622551554869349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9641019657660137479651597 3615382371622551554869349)
                      ·
                        rfl

theorem cell23_7040932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_7040932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7040932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7040932 prefixEnd_7040932 := by exact prefixLift 7040932
  have htrace : WordTrace (prefixWord ++ tailWord_7040932) baseStart_7040932 baseEnd_7040932 := by
    simpa [prefixWord, tailWord_7040932, baseEnd_7040932] using wordTrace_append hprefix tailTrace_7040932
  have hstable : (prefixWord ++ tailWord_7040932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7040932).length < 2 ^ (prefixWord ++ tailWord_7040932).sum := by decide
  have hdescent : baseEnd_7040932 < baseStart_7040932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7040932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041002 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_7041002 : Nat := 118140960795 + 7041002 * 2 ^ 59
def prefixEnd_7041002 : Nat := 4983230072969 + 3 ^ 40 * 7041002 * 2
def baseEnd_7041002 : Nat := 3615418315268366280994027

theorem tailTrace_7041002 : CollatzResearch.WordTrace tailWord_7041002 prefixEnd_7041002 3615418315268366280994027 := by
  unfold tailWord_7041002
  simp only [CollatzResearch.WordTrace]
  refine ⟨64201610109414934062551315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171204293625106490833470173 64201610109414934062551315)
  ·
    refine ⟨96302415164122401093826973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64201610109414934062551315 96302415164122401093826973)
    ·
      refine ⟨36113405686545900410185115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96302415164122401093826973 36113405686545900410185115)
      ·
        refine ⟨54170108529818850615277673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36113405686545900410185115 54170108529818850615277673)
        ·
          refine ⟨40627581397364137961458255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54170108529818850615277673 40627581397364137961458255)
          ·
            refine ⟨60941372096046206942187383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40627581397364137961458255 60941372096046206942187383)
            ·
              refine ⟨91412058144069310413281075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60941372096046206942187383 91412058144069310413281075)
              ·
                refine ⟨137118087216103965619921613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91412058144069310413281075 137118087216103965619921613)
                ·
                  refine ⟨51419282706038987107470605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137118087216103965619921613 51419282706038987107470605)
                  ·
                    refine ⟨19282231014764620165301477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51419282706038987107470605 19282231014764620165301477)
                    ·
                      refine ⟨3615418315268366280994027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19282231014764620165301477 3615418315268366280994027)
                      ·
                        rfl

theorem cell23_7041002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_7041002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041002 prefixEnd_7041002 := by exact prefixLift 7041002
  have htrace : WordTrace (prefixWord ++ tailWord_7041002) baseStart_7041002 baseEnd_7041002 := by
    simpa [prefixWord, tailWord_7041002, baseEnd_7041002] using wordTrace_append hprefix tailTrace_7041002
  have hstable : (prefixWord ++ tailWord_7041002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041002).length < 2 ^ (prefixWord ++ tailWord_7041002).sum := by decide
  have hdescent : baseEnd_7041002 < baseStart_7041002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041037 : List Nat := [1, 7, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7041037 : Nat := 118140960795 + 7041037 * 2 ^ 59
def prefixEnd_7041037 : Nat := 4983230072969 + 3 ^ 40 * 7041037 * 2
def baseEnd_7041037 : Nat := 401715143010141516006263

theorem tailTrace_7041037 : CollatzResearch.WordTrace tailWord_7041037 prefixEnd_7041037 401715143010141516006263 := by
  unfold tailWord_7041037
  simp only [CollatzResearch.WordTrace]
  refine ⟨256807716992532937227729365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171205144661688624818486243 256807716992532937227729365)
  ·
    refine ⟨6018930867012490716274907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 256807716992532937227729365 6018930867012490716274907)
    ·
      refine ⟨9028396300518736074412361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6018930867012490716274907 9028396300518736074412361)
      ·
        refine ⟨6771297225389052055809271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9028396300518736074412361 6771297225389052055809271)
        ·
          refine ⟨10156945838083578083713907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6771297225389052055809271 10156945838083578083713907)
          ·
            refine ⟨15235418757125367125570861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10156945838083578083713907 15235418757125367125570861)
            ·
              refine ⟨5713282033922012672089073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15235418757125367125570861 5713282033922012672089073)
              ·
                refine ⟨4284961525441509504066805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5713282033922012672089073 4284961525441509504066805)
                ·
                  refine ⟨401715143010141516006263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4284961525441509504066805 401715143010141516006263)
                  ·
                    rfl

theorem cell23_7041037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7041037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041037 prefixEnd_7041037 := by exact prefixLift 7041037
  have htrace : WordTrace (prefixWord ++ tailWord_7041037) baseStart_7041037 baseEnd_7041037 := by
    simpa [prefixWord, tailWord_7041037, baseEnd_7041037] using wordTrace_append hprefix tailTrace_7041037
  have hstable : (prefixWord ++ tailWord_7041037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041037).length < 2 ^ (prefixWord ++ tailWord_7041037).sum := by decide
  have hdescent : baseEnd_7041037 < baseStart_7041037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041079 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 1, 5, 2]
def baseStart_7041079 : Nat := 118140960795 + 7041079 * 2 ^ 59
def prefixEnd_7041079 : Nat := 4983230072969 + 3 ^ 40 * 7041079 * 2
def baseEnd_7041079 : Nat := 3615457853278762479731173

theorem tailTrace_7041079 : CollatzResearch.WordTrace tailWord_7041079 prefixEnd_7041079 3615457853278762479731173 := by
  unfold tailWord_7041079
  simp only [CollatzResearch.WordTrace]
  refine ⟨256809248858380778400758291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171206165905587185600505527 256809248858380778400758291)
  ·
    refine ⟨385213873287571167601137437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256809248858380778400758291 385213873287571167601137437)
    ·
      refine ⟨144455202482839187850426539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385213873287571167601137437 144455202482839187850426539)
      ·
        refine ⟨216682803724258781775639809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144455202482839187850426539 216682803724258781775639809)
        ·
          refine ⟨162512102793194086331729857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216682803724258781775639809 162512102793194086331729857)
          ·
            refine ⟨121884077094895564748797393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162512102793194086331729857 121884077094895564748797393)
            ·
              refine ⟨91413057821171673561598045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121884077094895564748797393 91413057821171673561598045)
              ·
                refine ⟨34279896682939377585599267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91413057821171673561598045 34279896682939377585599267)
                ·
                  refine ⟨51419845024409066378398901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34279896682939377585599267 51419845024409066378398901)
                  ·
                    refine ⟨4820610471038349972974897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51419845024409066378398901 4820610471038349972974897)
                    ·
                      refine ⟨3615457853278762479731173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820610471038349972974897 3615457853278762479731173)
                      ·
                        rfl

theorem cell23_7041079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_7041079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041079 prefixEnd_7041079 := by exact prefixLift 7041079
  have htrace : WordTrace (prefixWord ++ tailWord_7041079) baseStart_7041079 baseEnd_7041079 := by
    simpa [prefixWord, tailWord_7041079, baseEnd_7041079] using wordTrace_append hprefix tailTrace_7041079
  have hstable : (prefixWord ++ tailWord_7041079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041079).length < 2 ^ (prefixWord ++ tailWord_7041079).sum := by decide
  have hdescent : baseEnd_7041079 < baseStart_7041079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041109 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_7041109 : Nat := 118140960795 + 7041109 * 2 ^ 59
def prefixEnd_7041109 : Nat := 4983230072969 + 3 ^ 40 * 7041109 * 2
def baseEnd_7041109 : Nat := 3615473257698397362356035

theorem tailTrace_7041109 : CollatzResearch.WordTrace tailWord_7041109 prefixEnd_7041109 3615473257698397362356035 := by
  unfold tailWord_7041109
  simp only [CollatzResearch.WordTrace]
  refine ⟨256810343048272093524350381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171206895365514729016233587 256810343048272093524350381)
  ·
    refine ⟨96303878643102035071631393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256810343048272093524350381 96303878643102035071631393)
    ·
      refine ⟨72227908982326526303723545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96303878643102035071631393 72227908982326526303723545)
      ·
        refine ⟨54170931736744894727792659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72227908982326526303723545 54170931736744894727792659)
        ·
          refine ⟨81256397605117342091688989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54170931736744894727792659 81256397605117342091688989)
          ·
            refine ⟨30471149101919003284383371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81256397605117342091688989 30471149101919003284383371)
            ·
              refine ⟨45706723652878504926575057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30471149101919003284383371 45706723652878504926575057)
              ·
                refine ⟨34280042739658878694931293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45706723652878504926575057 34280042739658878694931293)
                ·
                  refine ⟨12855016027372079510599235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34280042739658878694931293 12855016027372079510599235)
                  ·
                    refine ⟨19282524041058119265898853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12855016027372079510599235 19282524041058119265898853)
                    ·
                      refine ⟨3615473257698397362356035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19282524041058119265898853 3615473257698397362356035)
                      ·
                        rfl

theorem cell23_7041109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_7041109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041109 prefixEnd_7041109 := by exact prefixLift 7041109
  have htrace : WordTrace (prefixWord ++ tailWord_7041109) baseStart_7041109 baseEnd_7041109 := by
    simpa [prefixWord, tailWord_7041109, baseEnd_7041109] using wordTrace_append hprefix tailTrace_7041109
  have hstable : (prefixWord ++ tailWord_7041109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041109).length < 2 ^ (prefixWord ++ tailWord_7041109).sum := by decide
  have hdescent : baseEnd_7041109 < baseStart_7041109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041129 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 3, 2, 3]
def baseStart_7041129 : Nat := 118140960795 + 7041129 * 2 ^ 59
def prefixEnd_7041129 : Nat := 4983230072969 + 3 ^ 40 * 7041129 * 2
def baseEnd_7041129 : Nat := 3615483527311487284105943

theorem tailTrace_7041129 : CollatzResearch.WordTrace tailWord_7041129 prefixEnd_7041129 3615483527311487284105943 := by
  unfold tailWord_7041129
  simp only [CollatzResearch.WordTrace]
  refine ⟨256811072508199636940078441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171207381672133091293385627 256811072508199636940078441)
  ·
    refine ⟨192608304381149727705058831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256811072508199636940078441 192608304381149727705058831)
    ·
      refine ⟨288912456571724591557588247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192608304381149727705058831 288912456571724591557588247)
      ·
        refine ⟨433368684857586887336382371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288912456571724591557588247 433368684857586887336382371)
        ·
          refine ⟨650053027286380331004573557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433368684857586887336382371 650053027286380331004573557)
          ·
            refine ⟨60942471308098156031678771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 650053027286380331004573557 60942471308098156031678771)
            ·
              refine ⟨91413706962147234047518157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60942471308098156031678771 91413706962147234047518157)
              ·
                refine ⟨34280140110805212767819309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91413706962147234047518157 34280140110805212767819309)
                ·
                  refine ⟨12855052541551954787932241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34280140110805212767819309 12855052541551954787932241)
                  ·
                    refine ⟨9641289406163966090949181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12855052541551954787932241 9641289406163966090949181)
                    ·
                      refine ⟨3615483527311487284105943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9641289406163966090949181 3615483527311487284105943)
                      ·
                        rfl

theorem cell23_7041129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2, 3].length) (baseStart_7041129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041129 prefixEnd_7041129 := by exact prefixLift 7041129
  have htrace : WordTrace (prefixWord ++ tailWord_7041129) baseStart_7041129 baseEnd_7041129 := by
    simpa [prefixWord, tailWord_7041129, baseEnd_7041129] using wordTrace_append hprefix tailTrace_7041129
  have hstable : (prefixWord ++ tailWord_7041129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041129).length < 2 ^ (prefixWord ++ tailWord_7041129).sum := by decide
  have hdescent : baseEnd_7041129 < baseStart_7041129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041130 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_7041130 : Nat := 118140960795 + 7041130 * 2 ^ 59
def prefixEnd_7041130 : Nat := 4983230072969 + 3 ^ 40 * 7041130 * 2
def baseEnd_7041130 : Nat := 3615484040792141780193439

theorem tailTrace_7041130 : CollatzResearch.WordTrace tailWord_7041130 prefixEnd_7041130 3615484040792141780193439 := by
  unfold tailWord_7041130
  simp only [CollatzResearch.WordTrace]
  refine ⟨64202777245299003527716211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171207405987464009407243229 64202777245299003527716211)
  ·
    refine ⟨96304165867948505291574317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64202777245299003527716211 96304165867948505291574317)
    ·
      refine ⟨36114062200480689484340369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96304165867948505291574317 36114062200480689484340369)
      ·
        refine ⟨27085546650360517113255277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36114062200480689484340369 27085546650360517113255277)
        ·
          refine ⟨10157079993885193917470729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27085546650360517113255277 10157079993885193917470729)
          ·
            refine ⟨7617809995413895438103047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10157079993885193917470729 7617809995413895438103047)
            ·
              refine ⟨11426714993120843157154571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617809995413895438103047 11426714993120843157154571)
              ·
                refine ⟨17140072489681264735731857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11426714993120843157154571 17140072489681264735731857)
                ·
                  refine ⟨12855054367260948551798893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17140072489681264735731857 12855054367260948551798893)
                  ·
                    refine ⟨4820645387722855706924585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12855054367260948551798893 4820645387722855706924585)
                    ·
                      refine ⟨3615484040792141780193439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820645387722855706924585 3615484040792141780193439)
                      ·
                        rfl

theorem cell23_7041130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_7041130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041130 prefixEnd_7041130 := by exact prefixLift 7041130
  have htrace : WordTrace (prefixWord ++ tailWord_7041130) baseStart_7041130 baseEnd_7041130 := by
    simpa [prefixWord, tailWord_7041130, baseEnd_7041130] using wordTrace_append hprefix tailTrace_7041130
  have hstable : (prefixWord ++ tailWord_7041130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041130).length < 2 ^ (prefixWord ++ tailWord_7041130).sum := by decide
  have hdescent : baseEnd_7041130 < baseStart_7041130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041143 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 1, 1, 4]
def baseStart_7041143 : Nat := 118140960795 + 7041143 * 2 ^ 59
def prefixEnd_7041143 : Nat := 4983230072969 + 3 ^ 40 * 7041143 * 2
def baseEnd_7041143 : Nat := 3615490716040650229330879

theorem tailTrace_7041143 : CollatzResearch.WordTrace tailWord_7041143 prefixEnd_7041143 3615490716040650229330879 := by
  unfold tailWord_7041143
  simp only [CollatzResearch.WordTrace]
  refine ⟨256811583130148917331088083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171207722086765944887392055 256811583130148917331088083)
  ·
    refine ⟨385217374695223375996632125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256811583130148917331088083 385217374695223375996632125)
    ·
      refine ⟨144456515510708765998737047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385217374695223375996632125 144456515510708765998737047)
      ·
        refine ⟨216684773266063148998105571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144456515510708765998737047 216684773266063148998105571)
        ·
          refine ⟨325027159899094723497158357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216684773266063148998105571 325027159899094723497158357)
          ·
            refine ⟨7617824060135032581964649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 325027159899094723497158357 7617824060135032581964649)
            ·
              refine ⟨5713368045101274436473487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7617824060135032581964649 5713368045101274436473487)
              ·
                refine ⟨8570052067651911654710231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713368045101274436473487 8570052067651911654710231)
                ·
                  refine ⟨12855078101477867482065347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8570052067651911654710231 12855078101477867482065347)
                  ·
                    refine ⟨19282617152216801223098021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12855078101477867482065347 19282617152216801223098021)
                    ·
                      refine ⟨3615490716040650229330879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19282617152216801223098021 3615490716040650229330879)
                      ·
                        rfl

theorem cell23_7041143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_7041143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041143 prefixEnd_7041143 := by exact prefixLift 7041143
  have htrace : WordTrace (prefixWord ++ tailWord_7041143) baseStart_7041143 baseEnd_7041143 := by
    simpa [prefixWord, tailWord_7041143, baseEnd_7041143] using wordTrace_append hprefix tailTrace_7041143
  have hstable : (prefixWord ++ tailWord_7041143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041143).length < 2 ^ (prefixWord ++ tailWord_7041143).sum := by decide
  have hdescent : baseEnd_7041143 < baseStart_7041143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041152 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_7041152 : Nat := 118140960795 + 7041152 * 2 ^ 59
def prefixEnd_7041152 : Nat := 4983230072969 + 3 ^ 40 * 7041152 * 2
def baseEnd_7041152 : Nat := 3615495337366540694118337

theorem tailTrace_7041152 : CollatzResearch.WordTrace tailWord_7041152 prefixEnd_7041152 3615495337366540694118337 := by
  unfold tailWord_7041152
  simp only [CollatzResearch.WordTrace]
  refine ⟨128405955693558155934082855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171207940924744207912110473 128405955693558155934082855)
  ·
    refine ⟨192608933540337233901124283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128405955693558155934082855 192608933540337233901124283)
    ·
      refine ⟨288913400310505850851686425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192608933540337233901124283 288913400310505850851686425)
      ·
        refine ⟨216685050232879388138764819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288913400310505850851686425 216685050232879388138764819)
        ·
          refine ⟨325027575349319082208147229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216685050232879388138764819 325027575349319082208147229)
          ·
            refine ⟨121885340755994655828055211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325027575349319082208147229 121885340755994655828055211)
            ·
              refine ⟨182828011133991983742082817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121885340755994655828055211 182828011133991983742082817)
              ·
                refine ⟨137121008350493987806562113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182828011133991983742082817 137121008350493987806562113)
                ·
                  refine ⟨102840756262870490854921585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137121008350493987806562113 102840756262870490854921585)
                  ·
                    refine ⟨77130567197152868141191189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102840756262870490854921585 77130567197152868141191189)
                    ·
                      refine ⟨3615495337366540694118337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77130567197152868141191189 3615495337366540694118337)
                      ·
                        rfl

theorem cell23_7041152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_7041152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041152 prefixEnd_7041152 := by exact prefixLift 7041152
  have htrace : WordTrace (prefixWord ++ tailWord_7041152) baseStart_7041152 baseEnd_7041152 := by
    simpa [prefixWord, tailWord_7041152, baseEnd_7041152] using wordTrace_append hprefix tailTrace_7041152
  have hstable : (prefixWord ++ tailWord_7041152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041152).length < 2 ^ (prefixWord ++ tailWord_7041152).sum := by decide
  have hdescent : baseEnd_7041152 < baseStart_7041152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041159 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_7041159 : Nat := 118140960795 + 7041159 * 2 ^ 59
def prefixEnd_7041159 : Nat := 4983230072969 + 3 ^ 40 * 7041159 * 2
def baseEnd_7041159 : Nat := 3615498931731122166730805

theorem tailTrace_7041159 : CollatzResearch.WordTrace tailWord_7041159 prefixEnd_7041159 3615498931731122166730805 := by
  unfold tailWord_7041159
  simp only [CollatzResearch.WordTrace]
  refine ⟨256812166698090952063670531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171208111132060634709113687 256812166698090952063670531)
  ·
    refine ⟨385218250047136428095505797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256812166698090952063670531 385218250047136428095505797)
    ·
      refine ⟨72228421883838080267907337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385218250047136428095505797 72228421883838080267907337)
      ·
        refine ⟨54171316412878560200930503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72228421883838080267907337 54171316412878560200930503)
        ·
          refine ⟨81256974619317840301395755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54171316412878560200930503 81256974619317840301395755)
          ·
            refine ⟨121885461928976760452093633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81256974619317840301395755 121885461928976760452093633)
            ·
              refine ⟨91414096446732570339070225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121885461928976760452093633 91414096446732570339070225)
              ·
                refine ⟨68560572335049427754302669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91414096446732570339070225 68560572335049427754302669)
                ·
                  refine ⟨25710214625643535407863501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68560572335049427754302669 25710214625643535407863501)
                  ·
                    refine ⟨9641330484616325777948813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25710214625643535407863501 9641330484616325777948813)
                    ·
                      refine ⟨3615498931731122166730805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9641330484616325777948813 3615498931731122166730805)
                      ·
                        rfl

theorem cell23_7041159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_7041159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041159 prefixEnd_7041159 := by exact prefixLift 7041159
  have htrace : WordTrace (prefixWord ++ tailWord_7041159) baseStart_7041159 baseEnd_7041159 := by
    simpa [prefixWord, tailWord_7041159, baseEnd_7041159] using wordTrace_append hprefix tailTrace_7041159
  have hstable : (prefixWord ++ tailWord_7041159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041159).length < 2 ^ (prefixWord ++ tailWord_7041159).sum := by decide
  have hdescent : baseEnd_7041159 < baseStart_7041159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041160 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 3, 2, 2]
def baseStart_7041160 : Nat := 118140960795 + 7041160 * 2 ^ 59
def prefixEnd_7041160 : Nat := 4983230072969 + 3 ^ 40 * 7041160 * 2
def baseEnd_7041160 : Nat := 3615499445211776662818301

theorem tailTrace_7041160 : CollatzResearch.WordTrace tailWord_7041160 prefixEnd_7041160 3615499445211776662818301 := by
  unfold tailWord_7041160
  simp only [CollatzResearch.WordTrace]
  refine ⟨128406101585543664617228467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171208135447391552822971289 128406101585543664617228467)
  ·
    refine ⟨192609152378315496925842701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128406101585543664617228467 192609152378315496925842701)
    ·
      refine ⟨72228432141868311347191013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192609152378315496925842701 72228432141868311347191013)
      ·
        refine ⟨13542831026600308377598315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72228432141868311347191013 13542831026600308377598315)
        ·
          refine ⟨20314246539900462566397473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13542831026600308377598315 20314246539900462566397473)
          ·
            refine ⟨15235684904925346924798105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20314246539900462566397473 15235684904925346924798105)
            ·
              refine ⟨11426763678694010193598579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15235684904925346924798105 11426763678694010193598579)
              ·
                refine ⟨17140145518041015290397869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11426763678694010193598579 17140145518041015290397869)
                ·
                  refine ⟨6427554569265380733899201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17140145518041015290397869 6427554569265380733899201)
                  ·
                    refine ⟨4820665926949035550424401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6427554569265380733899201 4820665926949035550424401)
                    ·
                      refine ⟨3615499445211776662818301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820665926949035550424401 3615499445211776662818301)
                      ·
                        rfl

theorem cell23_7041160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_7041160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041160 prefixEnd_7041160 := by exact prefixLift 7041160
  have htrace : WordTrace (prefixWord ++ tailWord_7041160) baseStart_7041160 baseEnd_7041160 := by
    simpa [prefixWord, tailWord_7041160, baseEnd_7041160] using wordTrace_append hprefix tailTrace_7041160
  have hstable : (prefixWord ++ tailWord_7041160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041160).length < 2 ^ (prefixWord ++ tailWord_7041160).sum := by decide
  have hdescent : baseEnd_7041160 < baseStart_7041160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041174 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7041174 : Nat := 118140960795 + 7041174 * 2 ^ 59
def prefixEnd_7041174 : Nat := 4983230072969 + 3 ^ 40 * 7041174 * 2
def baseEnd_7041174 : Nat := 1205168877980313202681079

theorem tailTrace_7041174 : CollatzResearch.WordTrace tailWord_7041174 prefixEnd_7041174 1205168877980313202681079 := by
  unfold tailWord_7041174
  simp only [CollatzResearch.WordTrace]
  refine ⟨16050794612064788101591661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171208475862024406416977717 16050794612064788101591661)
  ·
    refine ⟨6019047979524295538096873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16050794612064788101591661 6019047979524295538096873)
    ·
      refine ⟨4514285984643221653572655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6019047979524295538096873 4514285984643221653572655)
      ·
        refine ⟨6771428976964832480358983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514285984643221653572655 6771428976964832480358983)
        ·
          refine ⟨10157143465447248720538475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6771428976964832480358983 10157143465447248720538475)
          ·
            refine ⟨15235715198170873080807713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10157143465447248720538475 15235715198170873080807713)
            ·
              refine ⟨11426786398628154810605785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15235715198170873080807713 11426786398628154810605785)
              ·
                refine ⟨8570089798971116107954339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11426786398628154810605785 8570089798971116107954339)
                ·
                  refine ⟨12855134698456674161931509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8570089798971116107954339 12855134698456674161931509)
                  ·
                    refine ⟨1205168877980313202681079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12855134698456674161931509 1205168877980313202681079)
                    ·
                      rfl

theorem cell23_7041174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7041174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041174 prefixEnd_7041174 := by exact prefixLift 7041174
  have htrace : WordTrace (prefixWord ++ tailWord_7041174) baseStart_7041174 baseEnd_7041174 := by
    simpa [prefixWord, tailWord_7041174, baseEnd_7041174] using wordTrace_append hprefix tailTrace_7041174
  have hstable : (prefixWord ++ tailWord_7041174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041174).length < 2 ^ (prefixWord ++ tailWord_7041174).sum := by decide
  have hdescent : baseEnd_7041174 < baseStart_7041174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041237 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 1, 3, 2]
def baseStart_7041237 : Nat := 118140960795 + 7041237 * 2 ^ 59
def prefixEnd_7041237 : Nat := 4983230072969 + 3 ^ 40 * 7041237 * 2
def baseEnd_7041237 : Nat := 3615538983222172861555447

theorem tailTrace_7041237 : CollatzResearch.WordTrace tailWord_7041237 prefixEnd_7041237 3615538983222172861555447 := by
  unfold tailWord_7041237
  simp only [CollatzResearch.WordTrace]
  refine ⟨256815011591808371385009965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171210007727872247590006643 256815011591808371385009965)
  ·
    refine ⟨96305629346928139269378737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256815011591808371385009965 96305629346928139269378737)
    ·
      refine ⟨72229222010196104452034053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96305629346928139269378737 72229222010196104452034053)
      ·
        refine ⟨13542979126911769584756385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72229222010196104452034053 13542979126911769584756385)
        ·
          refine ⟨10157234345183827188567289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13542979126911769584756385 10157234345183827188567289)
          ·
            refine ⟨7617925758887870391425467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10157234345183827188567289 7617925758887870391425467)
            ·
              refine ⟨11426888638331805587138201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617925758887870391425467 11426888638331805587138201)
              ·
                refine ⟨8570166478748854190353651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11426888638331805587138201 8570166478748854190353651)
                ·
                  refine ⟨12855249718123281285530477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8570166478748854190353651 12855249718123281285530477)
                  ·
                    refine ⟨4820718644296230482073929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12855249718123281285530477 4820718644296230482073929)
                    ·
                      refine ⟨3615538983222172861555447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820718644296230482073929 3615538983222172861555447)
                      ·
                        rfl

theorem cell23_7041237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_7041237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041237 prefixEnd_7041237 := by exact prefixLift 7041237
  have htrace : WordTrace (prefixWord ++ tailWord_7041237) baseStart_7041237 baseEnd_7041237 := by
    simpa [prefixWord, tailWord_7041237, baseEnd_7041237] using wordTrace_append hprefix tailTrace_7041237
  have hstable : (prefixWord ++ tailWord_7041237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041237).length < 2 ^ (prefixWord ++ tailWord_7041237).sum := by decide
  have hdescent : baseEnd_7041237 < baseStart_7041237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041279 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_7041279 : Nat := 118140960795 + 7041279 * 2 ^ 59
def prefixEnd_7041279 : Nat := 4983230072969 + 3 ^ 40 * 7041279 * 2
def baseEnd_7041279 : Nat := 3615560549409661697230253

theorem tailTrace_7041279 : CollatzResearch.WordTrace tailWord_7041279 prefixEnd_7041279 3615560549409661697230253 := by
  unfold tailWord_7041279
  simp only [CollatzResearch.WordTrace]
  refine ⟨256816543457656212558038891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171211028971770808372025927 256816543457656212558038891)
  ·
    refine ⟨385224815186484318837058337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256816543457656212558038891 385224815186484318837058337)
    ·
      refine ⟨288918611389863239127793753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385224815186484318837058337 288918611389863239127793753)
      ·
        refine ⟨216688958542397429345845315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288918611389863239127793753 216688958542397429345845315)
        ·
          refine ⟨325033437813596144018767973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216688958542397429345845315 325033437813596144018767973)
          ·
            refine ⟨60943769590049277003518995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 325033437813596144018767973 60943769590049277003518995)
            ·
              refine ⟨91415654385073915505278493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60943769590049277003518995 91415654385073915505278493)
              ·
                refine ⟨34280870394402718314479435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91415654385073915505278493 34280870394402718314479435)
                ·
                  refine ⟨51421305591604077471719153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34280870394402718314479435 51421305591604077471719153)
                  ·
                    refine ⟨38565979193703058103789365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51421305591604077471719153 38565979193703058103789365)
                    ·
                      refine ⟨3615560549409661697230253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38565979193703058103789365 3615560549409661697230253)
                      ·
                        rfl

theorem cell23_7041279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_7041279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041279 prefixEnd_7041279 := by exact prefixLift 7041279
  have htrace : WordTrace (prefixWord ++ tailWord_7041279) baseStart_7041279 baseEnd_7041279 := by
    simpa [prefixWord, tailWord_7041279, baseEnd_7041279] using wordTrace_append hprefix tailTrace_7041279
  have hstable : (prefixWord ++ tailWord_7041279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041279).length < 2 ^ (prefixWord ++ tailWord_7041279).sum := by decide
  have hdescent : baseEnd_7041279 < baseStart_7041279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041303 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 2, 5]
def baseStart_7041303 : Nat := 118140960795 + 7041303 * 2 ^ 59
def prefixEnd_7041303 : Nat := 4983230072969 + 3 ^ 40 * 7041303 * 2
def baseEnd_7041303 : Nat := 1205190957648456534443381

theorem tailTrace_7041303 : CollatzResearch.WordTrace tailWord_7041303 prefixEnd_7041303 1205190957648456534443381 := by
  unfold tailWord_7041303
  simp only [CollatzResearch.WordTrace]
  refine ⟨256817418809569264656912563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171211612539712843104608375 256817418809569264656912563)
  ·
    refine ⟨385226128214353896985368845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256817418809569264656912563 385226128214353896985368845)
    ·
      refine ⟨144459798080382711369513317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385226128214353896985368845 144459798080382711369513317)
      ·
        refine ⟨27086212140071758381783747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144459798080382711369513317 27086212140071758381783747)
        ·
          refine ⟨40629318210107637572675621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27086212140071758381783747 40629318210107637572675621)
          ·
            refine ⟨7617997164395182044876679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40629318210107637572675621 7617997164395182044876679)
            ·
              refine ⟨11426995746592773067315019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617997164395182044876679 11426995746592773067315019)
              ·
                refine ⟨17140493619889159600972529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11426995746592773067315019 17140493619889159600972529)
                ·
                  refine ⟨12855370214916869700729397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17140493619889159600972529 12855370214916869700729397)
                  ·
                    refine ⟨1205190957648456534443381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12855370214916869700729397 1205190957648456534443381)
                    ·
                      rfl

theorem cell23_7041303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_7041303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041303 prefixEnd_7041303 := by exact prefixLift 7041303
  have htrace : WordTrace (prefixWord ++ tailWord_7041303) baseStart_7041303 baseEnd_7041303 := by
    simpa [prefixWord, tailWord_7041303, baseEnd_7041303] using wordTrace_append hprefix tailTrace_7041303
  have hstable : (prefixWord ++ tailWord_7041303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041303).length < 2 ^ (prefixWord ++ tailWord_7041303).sum := by decide
  have hdescent : baseEnd_7041303 < baseStart_7041303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041333 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_7041333 : Nat := 118140960795 + 7041333 * 2 ^ 59
def prefixEnd_7041333 : Nat := 4983230072969 + 3 ^ 40 * 7041333 * 2
def baseEnd_7041333 : Nat := 1205196092455001495318335

theorem tailTrace_7041333 : CollatzResearch.WordTrace tailWord_7041333 prefixEnd_7041333 1205196092455001495318335 := by
  unfold tailWord_7041333
  simp only [CollatzResearch.WordTrace]
  refine ⟨256818512999460579780504653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171212341999640386520336435 256818512999460579780504653)
  ·
    refine ⟨96306942374797717417689245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256818512999460579780504653 96306942374797717417689245)
    ·
      refine ⟨36115103390549144031633467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96306942374797717417689245 36115103390549144031633467)
      ·
        refine ⟨54172655085823716047450201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36115103390549144031633467 54172655085823716047450201)
        ·
          refine ⟨40629491314367787035587651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54172655085823716047450201 40629491314367787035587651)
          ·
            refine ⟨60944236971551680553381477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40629491314367787035587651 60944236971551680553381477)
            ·
              refine ⟨11427044432165940103759027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60944236971551680553381477 11427044432165940103759027)
              ·
                refine ⟨17140566648248910155638541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11427044432165940103759027 17140566648248910155638541)
                ·
                  refine ⟨6427712493093341308364453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17140566648248910155638541 6427712493093341308364453)
                  ·
                    refine ⟨1205196092455001495318335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6427712493093341308364453 1205196092455001495318335)
                    ·
                      rfl

theorem cell23_7041333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_7041333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041333 prefixEnd_7041333 := by exact prefixLift 7041333
  have htrace : WordTrace (prefixWord ++ tailWord_7041333) baseStart_7041333 baseEnd_7041333 := by
    simpa [prefixWord, tailWord_7041333, baseEnd_7041333] using wordTrace_append hprefix tailTrace_7041333
  have hstable : (prefixWord ++ tailWord_7041333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041333).length < 2 ^ (prefixWord ++ tailWord_7041333).sum := by decide
  have hdescent : baseEnd_7041333 < baseStart_7041333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041356 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 2, 5, 3]
def baseStart_7041356 : Nat := 118140960795 + 7041356 * 2 ^ 59
def prefixEnd_7041356 : Nat := 4983230072969 + 3 ^ 40 * 7041356 * 2
def baseEnd_7041356 : Nat := 3615600087420057895967399

theorem tailTrace_7041356 : CollatzResearch.WordTrace tailWord_7041356 prefixEnd_7041356 3615600087420057895967399 := by
  unfold tailWord_7041356
  simp only [CollatzResearch.WordTrace]
  refine ⟨128409675939188627354295961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171212901252251503139061281 128409675939188627354295961)
  ·
    refine ⟨96307256954391470515721971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128409675939188627354295961 96307256954391470515721971)
    ·
      refine ⟨144460885431587205773582957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96307256954391470515721971 144460885431587205773582957)
      ·
        refine ⟨54172832036845202165093609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144460885431587205773582957 54172832036845202165093609)
        ·
          refine ⟨40629624027633901623820207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54172832036845202165093609 40629624027633901623820207)
          ·
            refine ⟨60944436041450852435730311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40629624027633901623820207 60944436041450852435730311)
            ·
              refine ⟨91416654062176278653595467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60944436041450852435730311 91416654062176278653595467)
              ·
                refine ⟨137124981093264417980393201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91416654062176278653595467 137124981093264417980393201)
                ·
                  refine ⟨102843735819948313485294901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137124981093264417980393201 102843735819948313485294901)
                  ·
                    refine ⟨9641600233120154389246397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102843735819948313485294901 9641600233120154389246397)
                    ·
                      refine ⟨3615600087420057895967399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9641600233120154389246397 3615600087420057895967399)
                      ·
                        rfl

theorem cell23_7041356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_7041356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041356 prefixEnd_7041356 := by exact prefixLift 7041356
  have htrace : WordTrace (prefixWord ++ tailWord_7041356) baseStart_7041356 baseEnd_7041356 := by
    simpa [prefixWord, tailWord_7041356, baseEnd_7041356] using wordTrace_append hprefix tailTrace_7041356
  have hstable : (prefixWord ++ tailWord_7041356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041356).length < 2 ^ (prefixWord ++ tailWord_7041356).sum := by decide
  have hdescent : baseEnd_7041356 < baseStart_7041356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041440 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 2, 4]
def baseStart_7041440 : Nat := 118140960795 + 7041440 * 2 ^ 59
def prefixEnd_7041440 : Nat := 4983230072969 + 3 ^ 40 * 7041440 * 2
def baseEnd_7041440 : Nat := 1205214406598345189105671

theorem tailTrace_7041440 : CollatzResearch.WordTrace tailWord_7041440 prefixEnd_7041440 1205214406598345189105671 := by
  unfold tailWord_7041440
  simp only [CollatzResearch.WordTrace]
  refine ⟨128411207805036468527324887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171214943740048624703099849 128411207805036468527324887)
  ·
    refine ⟨192616811707554702790987331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128411207805036468527324887 192616811707554702790987331)
    ·
      refine ⟨288925217561332054186480997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192616811707554702790987331 288925217561332054186480997)
      ·
        refine ⟨54173478292749760159965187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288925217561332054186480997 54173478292749760159965187)
        ·
          refine ⟨81260217439124640239947781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54173478292749760159965187 81260217439124640239947781)
          ·
            refine ⟨15236290769835870044990209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81260217439124640239947781 15236290769835870044990209)
            ·
              refine ⟨11427218077376902533742657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15236290769835870044990209 11427218077376902533742657)
              ·
                refine ⟨8570413558032676900306993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11427218077376902533742657 8570413558032676900306993)
                ·
                  refine ⟨6427810168524507675230245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8570413558032676900306993 6427810168524507675230245)
                  ·
                    refine ⟨1205214406598345189105671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6427810168524507675230245 1205214406598345189105671)
                    ·
                      rfl

theorem cell23_7041440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2, 4].length) (baseStart_7041440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041440 prefixEnd_7041440 := by exact prefixLift 7041440
  have htrace : WordTrace (prefixWord ++ tailWord_7041440) baseStart_7041440 baseEnd_7041440 := by
    simpa [prefixWord, tailWord_7041440, baseEnd_7041440] using wordTrace_append hprefix tailTrace_7041440
  have hstable : (prefixWord ++ tailWord_7041440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041440).length < 2 ^ (prefixWord ++ tailWord_7041440).sum := by decide
  have hdescent : baseEnd_7041440 < baseStart_7041440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041463 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3]
def baseStart_7041463 : Nat := 118140960795 + 7041463 * 2 ^ 59
def prefixEnd_7041463 : Nat := 4983230072969 + 3 ^ 40 * 7041463 * 2
def baseEnd_7041463 : Nat := 3615655029850088977329407

theorem tailTrace_7041463 : CollatzResearch.WordTrace tailWord_7041463 prefixEnd_7041463 3615655029850088977329407 := by
  unfold tailWord_7041463
  simp only [CollatzResearch.WordTrace]
  refine ⟨256823254488989611982737043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171215502992659741321824695 256823254488989611982737043)
  ·
    refine ⟨385234881733484417974105565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256823254488989611982737043 385234881733484417974105565)
    ·
      refine ⟨144463080650056656740289587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385234881733484417974105565 144463080650056656740289587)
      ·
        refine ⟨216694620975084985110434381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144463080650056656740289587 216694620975084985110434381)
        ·
          refine ⟨81260482865656869416412893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216694620975084985110434381 81260482865656869416412893)
          ·
            refine ⟨30472681074621326031154835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81260482865656869416412893 30472681074621326031154835)
            ·
              refine ⟨45709021611931989046732253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30472681074621326031154835 45709021611931989046732253)
              ·
                refine ⟨17140883104474495892524595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45709021611931989046732253 17140883104474495892524595)
                ·
                  refine ⟨25711324656711743838786893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17140883104474495892524595 25711324656711743838786893)
                  ·
                    refine ⟨9641746746266903939545085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25711324656711743838786893 9641746746266903939545085)
                    ·
                      refine ⟨3615655029850088977329407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9641746746266903939545085 3615655029850088977329407)
                      ·
                        rfl

theorem cell23_7041463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_7041463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041463 prefixEnd_7041463 := by exact prefixLift 7041463
  have htrace : WordTrace (prefixWord ++ tailWord_7041463) baseStart_7041463 baseEnd_7041463 := by
    simpa [prefixWord, tailWord_7041463, baseEnd_7041463] using wordTrace_append hprefix tailTrace_7041463
  have hstable : (prefixWord ++ tailWord_7041463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041463).length < 2 ^ (prefixWord ++ tailWord_7041463).sum := by decide
  have hdescent : baseEnd_7041463 < baseStart_7041463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041484 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 1, 2, 3]
def baseStart_7041484 : Nat := 118140960795 + 7041484 * 2 ^ 59
def prefixEnd_7041484 : Nat := 4983230072969 + 3 ^ 40 * 7041484 * 2
def baseEnd_7041484 : Nat := 3615665812943833395166811

theorem tailTrace_7041484 : CollatzResearch.WordTrace tailWord_7041484 prefixEnd_7041484 3615665812943833395166811 := by
  unfold tailWord_7041484
  simp only [CollatzResearch.WordTrace]
  refine ⟨128412010210956766284625753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171216013614609021712834337 128412010210956766284625753)
  ·
    refine ⟨96309007658217574713469315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128412010210956766284625753 96309007658217574713469315)
    ·
      refine ⟨144463511487326362070203973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96309007658217574713469315 144463511487326362070203973)
      ·
        refine ⟨27086908403873692888163245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144463511487326362070203973 27086908403873692888163245)
        ·
          refine ⟨10157590651452634833061217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27086908403873692888163245 10157590651452634833061217)
          ·
            refine ⟨7618192988589476124795913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10157590651452634833061217 7618192988589476124795913)
            ·
              refine ⟨5713644741442107093596935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7618192988589476124795913 5713644741442107093596935)
              ·
                refine ⟨8570467112163160640395403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713644741442107093596935 8570467112163160640395403)
                ·
                  refine ⟨12855700668244740960593105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8570467112163160640395403 12855700668244740960593105)
                  ·
                    refine ⟨9641775501183555720444829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12855700668244740960593105 9641775501183555720444829)
                    ·
                      refine ⟨3615665812943833395166811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9641775501183555720444829 3615665812943833395166811)
                      ·
                        rfl

theorem cell23_7041484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_7041484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041484 prefixEnd_7041484 := by exact prefixLift 7041484
  have htrace : WordTrace (prefixWord ++ tailWord_7041484) baseStart_7041484 baseEnd_7041484 := by
    simpa [prefixWord, tailWord_7041484, baseEnd_7041484] using wordTrace_append hprefix tailTrace_7041484
  have hstable : (prefixWord ++ tailWord_7041484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041484).length < 2 ^ (prefixWord ++ tailWord_7041484).sum := by decide
  have hdescent : baseEnd_7041484 < baseStart_7041484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041514 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_7041514 : Nat := 118140960795 + 7041514 * 2 ^ 59
def prefixEnd_7041514 : Nat := 4983230072969 + 3 ^ 40 * 7041514 * 2
def baseEnd_7041514 : Nat := 3615681217363468277791673

theorem tailTrace_7041514 : CollatzResearch.WordTrace tailWord_7041514 prefixEnd_7041514 3615681217363468277791673 := by
  unfold tailWord_7041514
  simp only [CollatzResearch.WordTrace]
  refine ⟨64206278652951211923210899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171216743074536565128562397 64206278652951211923210899)
  ·
    refine ⟨96309417979426817884816349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64206278652951211923210899 96309417979426817884816349)
    ·
      refine ⟨36116031742285056706806131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96309417979426817884816349 36116031742285056706806131)
      ·
        refine ⟨54174047613427585060209197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36116031742285056706806131 54174047613427585060209197)
        ·
          refine ⟨20315267855035344397578449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54174047613427585060209197 20315267855035344397578449)
          ·
            refine ⟨15236450891276508298183837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20315267855035344397578449 15236450891276508298183837)
            ·
              refine ⟨5713669084228690611818939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15236450891276508298183837 5713669084228690611818939)
              ·
                refine ⟨8570503626343035917728409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713669084228690611818939 8570503626343035917728409)
                ·
                  refine ⟨6427877719757276938296307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8570503626343035917728409 6427877719757276938296307)
                  ·
                    refine ⟨9641816579635915407444461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6427877719757276938296307 9641816579635915407444461)
                    ·
                      refine ⟨3615681217363468277791673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9641816579635915407444461 3615681217363468277791673)
                      ·
                        rfl

theorem cell23_7041514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_7041514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041514 prefixEnd_7041514 := by exact prefixLift 7041514
  have htrace : WordTrace (prefixWord ++ tailWord_7041514) baseStart_7041514 baseEnd_7041514 := by
    simpa [prefixWord, tailWord_7041514, baseEnd_7041514] using wordTrace_append hprefix tailTrace_7041514
  have hstable : (prefixWord ++ tailWord_7041514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041514).length < 2 ^ (prefixWord ++ tailWord_7041514).sum := by decide
  have hdescent : baseEnd_7041514 < baseStart_7041514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041537 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_7041537 : Nat := 118140960795 + 7041537 * 2 ^ 59
def prefixEnd_7041537 : Nat := 4983230072969 + 3 ^ 40 * 7041537 * 2
def baseEnd_7041537 : Nat := 3615693027418521687804067

theorem tailTrace_7041537 : CollatzResearch.WordTrace tailWord_7041537 prefixEnd_7041537 3615693027418521687804067 := by
  unfold tailWord_7041537
  simp only [CollatzResearch.WordTrace]
  refine ⟨256825953490721522620930865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171217302327147681747287243 256825953490721522620930865)
  ·
    refine ⟨192619465118041141965698149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256825953490721522620930865 192619465118041141965698149)
    ·
      refine ⟨36116149709632714118568403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192619465118041141965698149 36116149709632714118568403)
      ·
        refine ⟨54174224564449071177852605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36116149709632714118568403 54174224564449071177852605)
        ·
          refine ⟨20315334211668401691694727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54174224564449071177852605 20315334211668401691694727)
          ·
            refine ⟨30473001317502602537542091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20315334211668401691694727 30473001317502602537542091)
            ·
              refine ⟨45709501976253903806313137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30473001317502602537542091 45709501976253903806313137)
              ·
                refine ⟨34282126482190427854734853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45709501976253903806313137 34282126482190427854734853)
                ·
                  refine ⟨6427898715410705222762785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34282126482190427854734853 6427898715410705222762785)
                  ·
                    refine ⟨4820924036558028917072089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6427898715410705222762785 4820924036558028917072089)
                    ·
                      refine ⟨3615693027418521687804067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820924036558028917072089 3615693027418521687804067)
                      ·
                        rfl

theorem cell23_7041537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_7041537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041537 prefixEnd_7041537 := by exact prefixLift 7041537
  have htrace : WordTrace (prefixWord ++ tailWord_7041537) baseStart_7041537 baseEnd_7041537 := by
    simpa [prefixWord, tailWord_7041537, baseEnd_7041537] using wordTrace_append hprefix tailTrace_7041537
  have hstable : (prefixWord ++ tailWord_7041537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041537).length < 2 ^ (prefixWord ++ tailWord_7041537).sum := by decide
  have hdescent : baseEnd_7041537 < baseStart_7041537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041540 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7041540 : Nat := 118140960795 + 7041540 * 2 ^ 59
def prefixEnd_7041540 : Nat := 4983230072969 + 3 ^ 40 * 7041540 * 2
def baseEnd_7041540 : Nat := 3615694567860485176066553

theorem tailTrace_7041540 : CollatzResearch.WordTrace tailWord_7041540 prefixEnd_7041540 3615694567860485176066553 := by
  unfold tailWord_7041540
  simp only [CollatzResearch.WordTrace]
  refine ⟨128413031454855327066645037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171217375273140436088860049 128413031454855327066645037)
  ·
    refine ⟨48154886795570747649991889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128413031454855327066645037 48154886795570747649991889)
    ·
      refine ⟨36116165096678060737493917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48154886795570747649991889 36116165096678060737493917)
      ·
        refine ⟨13543561911254272776560219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36116165096678060737493917 13543561911254272776560219)
        ·
          refine ⟨20315342866881409164840329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13543561911254272776560219 20315342866881409164840329)
          ·
            refine ⟨15236507150161056873630247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20315342866881409164840329 15236507150161056873630247)
            ·
              refine ⟨22854760725241585310445371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15236507150161056873630247 22854760725241585310445371)
              ·
                refine ⟨34282141087862377965668057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22854760725241585310445371 34282141087862377965668057)
                ·
                  refine ⟨25711605815896783474251043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34282141087862377965668057 25711605815896783474251043)
                  ·
                    refine ⟨38567408723845175211376565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25711605815896783474251043 38567408723845175211376565)
                    ·
                      refine ⟨3615694567860485176066553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38567408723845175211376565 3615694567860485176066553)
                      ·
                        rfl

theorem cell23_7041540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7041540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041540 prefixEnd_7041540 := by exact prefixLift 7041540
  have htrace : WordTrace (prefixWord ++ tailWord_7041540) baseStart_7041540 baseEnd_7041540 := by
    simpa [prefixWord, tailWord_7041540, baseEnd_7041540] using wordTrace_append hprefix tailTrace_7041540
  have hstable : (prefixWord ++ tailWord_7041540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041540).length < 2 ^ (prefixWord ++ tailWord_7041540).sum := by decide
  have hdescent : baseEnd_7041540 < baseStart_7041540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041553 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 3]
def baseStart_7041553 : Nat := 118140960795 + 7041553 * 2 ^ 59
def prefixEnd_7041553 : Nat := 4983230072969 + 3 ^ 40 * 7041553 * 2
def baseEnd_7041553 : Nat := 3615701243108993625203993

theorem tailTrace_7041553 : CollatzResearch.WordTrace tailWord_7041553 prefixEnd_7041553 3615701243108993625203993 := by
  unfold tailWord_7041553
  simp only [CollatzResearch.WordTrace]
  refine ⟨256826537058663557353513313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171217691372442371569008875 256826537058663557353513313)
  ·
    refine ⟨192619902793997668015134985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256826537058663557353513313 192619902793997668015134985)
    ·
      refine ⟨144464927095498251011351239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192619902793997668015134985 144464927095498251011351239)
      ·
        refine ⟨216697390643247376517026859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144464927095498251011351239 216697390643247376517026859)
        ·
          refine ⟨325046085964871064775540289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216697390643247376517026859 325046085964871064775540289)
          ·
            refine ⟨243784564473653298581655217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325046085964871064775540289 243784564473653298581655217)
            ·
              refine ⟨182838423355239973936241413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243784564473653298581655217 182838423355239973936241413)
              ·
                refine ⟨34282204379107495113045265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182838423355239973936241413 34282204379107495113045265)
                ·
                  refine ⟨25711653284330621334783949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34282204379107495113045265 25711653284330621334783949)
                  ·
                    refine ⟨9641869981623983000543981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25711653284330621334783949 9641869981623983000543981)
                    ·
                      refine ⟨3615701243108993625203993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9641869981623983000543981 3615701243108993625203993)
                      ·
                        rfl

theorem cell23_7041553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_7041553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041553 prefixEnd_7041553 := by exact prefixLift 7041553
  have htrace : WordTrace (prefixWord ++ tailWord_7041553) baseStart_7041553 baseEnd_7041553 := by
    simpa [prefixWord, tailWord_7041553, baseEnd_7041553] using wordTrace_append hprefix tailTrace_7041553
  have hstable : (prefixWord ++ tailWord_7041553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041553).length < 2 ^ (prefixWord ++ tailWord_7041553).sum := by decide
  have hdescent : baseEnd_7041553 < baseStart_7041553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041560 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 7]
def baseStart_7041560 : Nat := 118140960795 + 7041560 * 2 ^ 59
def prefixEnd_7041560 : Nat := 4983230072969 + 3 ^ 40 * 7041560 * 2
def baseEnd_7041560 : Nat := 401744981941508344201829

theorem tailTrace_7041560 : CollatzResearch.WordTrace tailWord_7041560 prefixEnd_7041560 401744981941508344201829 := by
  unfold tailWord_7041560
  simp only [CollatzResearch.WordTrace]
  refine ⟨128413396184819098774509067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171217861579758798366012089 128413396184819098774509067)
  ·
    refine ⟨192620094277228648161763601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128413396184819098774509067 192620094277228648161763601)
    ·
      refine ⟨144465070707921486121322701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192620094277228648161763601 144465070707921486121322701)
      ·
        refine ⟨54174401515470557295496013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144465070707921486121322701 54174401515470557295496013)
        ·
          refine ⟨20315400568301458985811005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54174401515470557295496013 20315400568301458985811005)
          ·
            refine ⟨7618275213113047119679127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20315400568301458985811005 7618275213113047119679127)
            ·
              refine ⟨11427412819669570679518691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7618275213113047119679127 11427412819669570679518691)
              ·
                refine ⟨17141119229504356019278037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11427412819669570679518691 17141119229504356019278037)
                ·
                  refine ⟨401744981941508344201829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17141119229504356019278037 401744981941508344201829)
                  ·
                    rfl

theorem cell23_7041560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 7].length) (baseStart_7041560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041560 prefixEnd_7041560 := by exact prefixLift 7041560
  have htrace : WordTrace (prefixWord ++ tailWord_7041560) baseStart_7041560 baseEnd_7041560 := by
    simpa [prefixWord, tailWord_7041560, baseEnd_7041560] using wordTrace_append hprefix tailTrace_7041560
  have hstable : (prefixWord ++ tailWord_7041560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041560).length < 2 ^ (prefixWord ++ tailWord_7041560).sum := by decide
  have hdescent : baseEnd_7041560 < baseStart_7041560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041571 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 2, 2, 2]
def baseStart_7041571 : Nat := 118140960795 + 7041571 * 2 ^ 59
def prefixEnd_7041571 : Nat := 4983230072969 + 3 ^ 40 * 7041571 * 2
def baseEnd_7041571 : Nat := 3615710485760774554778911

theorem tailTrace_7041571 : CollatzResearch.WordTrace tailWord_7041571 prefixEnd_7041571 3615710485760774554778911 := by
  unfold tailWord_7041571
  simp only [CollatzResearch.WordTrace]
  refine ⟨256827193572598346427668567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171218129048398897618445711 256827193572598346427668567)
  ·
    refine ⟨385240790358897519641502851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256827193572598346427668567 385240790358897519641502851)
    ·
      refine ⟨577861185538346279462254277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385240790358897519641502851 577861185538346279462254277)
      ·
        refine ⟨108348972288439927399172677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 577861185538346279462254277 108348972288439927399172677)
        ·
          refine ⟨20315432304082486387344877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108348972288439927399172677 20315432304082486387344877)
          ·
            refine ⟨7618287114030932395254329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20315432304082486387344877 7618287114030932395254329)
            ·
              refine ⟨5713715335523199296440747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7618287114030932395254329 5713715335523199296440747)
              ·
                refine ⟨8570573003284798944661121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713715335523199296440747 8570573003284798944661121)
                ·
                  refine ⟨6427929752463599208495841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8570573003284798944661121 6427929752463599208495841)
                  ·
                    refine ⟨4820947314347699406371881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6427929752463599208495841 4820947314347699406371881)
                    ·
                      refine ⟨3615710485760774554778911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4820947314347699406371881 3615710485760774554778911)
                      ·
                        rfl

theorem cell23_7041571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_7041571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041571 prefixEnd_7041571 := by exact prefixLift 7041571
  have htrace : WordTrace (prefixWord ++ tailWord_7041571) baseStart_7041571 baseEnd_7041571 := by
    simpa [prefixWord, tailWord_7041571, baseEnd_7041571] using wordTrace_append hprefix tailTrace_7041571
  have hstable : (prefixWord ++ tailWord_7041571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041571).length < 2 ^ (prefixWord ++ tailWord_7041571).sum := by decide
  have hdescent : baseEnd_7041571 < baseStart_7041571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041610 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_7041610 : Nat := 118140960795 + 7041610 * 2 ^ 59
def prefixEnd_7041610 : Nat := 4983230072969 + 3 ^ 40 * 7041610 * 2
def baseEnd_7041610 : Nat := 3615730511506299902191231

theorem tailTrace_7041610 : CollatzResearch.WordTrace tailWord_7041610 prefixEnd_7041610 3615730511506299902191231 := by
  unfold tailWord_7041610
  simp only [CollatzResearch.WordTrace]
  refine ⟨64207154004864264022084571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171219077346304704058892189 64207154004864264022084571)
  ·
    refine ⟨96310731007296396033126857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64207154004864264022084571 96310731007296396033126857)
    ·
      refine ⟨72233048255472297024845143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96310731007296396033126857 72233048255472297024845143)
      ·
        refine ⟨108349572383208445537267715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72233048255472297024845143 108349572383208445537267715)
        ·
          refine ⟨162524358574812668305901573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108349572383208445537267715 162524358574812668305901573)
          ·
            refine ⟨30473317232777375307356545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162524358574812668305901573 30473317232777375307356545)
            ·
              refine ⟨22854987924583031480517409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30473317232777375307356545 22854987924583031480517409)
              ·
                refine ⟨17141240943437273610388057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22854987924583031480517409 17141240943437273610388057)
                ·
                  refine ⟨12855930707577955207791043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17141240943437273610388057 12855930707577955207791043)
                  ·
                    refine ⟨19283896061366932811686565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12855930707577955207791043 19283896061366932811686565)
                    ·
                      refine ⟨3615730511506299902191231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19283896061366932811686565 3615730511506299902191231)
                      ·
                        rfl

theorem cell23_7041610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_7041610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041610 prefixEnd_7041610 := by exact prefixLift 7041610
  have htrace : WordTrace (prefixWord ++ tailWord_7041610) baseStart_7041610 baseEnd_7041610 := by
    simpa [prefixWord, tailWord_7041610, baseEnd_7041610] using wordTrace_append hprefix tailTrace_7041610
  have hstable : (prefixWord ++ tailWord_7041610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041610).length < 2 ^ (prefixWord ++ tailWord_7041610).sum := by decide
  have hdescent : baseEnd_7041610 < baseStart_7041610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041637 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_7041637 : Nat := 118140960795 + 7041637 * 2 ^ 59
def prefixEnd_7041637 : Nat := 4983230072969 + 3 ^ 40 * 7041637 * 2
def baseEnd_7041637 : Nat := 1205248125161323765517869

theorem tailTrace_7041637 : CollatzResearch.WordTrace tailWord_7041637 prefixEnd_7041637 1205248125161323765517869 := by
  unfold tailWord_7041637
  simp only [CollatzResearch.WordTrace]
  refine ⟨256829600790359239699571165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171219733860239493133047443 256829600790359239699571165)
  ·
    refine ⟨96311100296384714887339187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256829600790359239699571165 96311100296384714887339187)
    ·
      refine ⟨144466650444577072331008781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96311100296384714887339187 144466650444577072331008781)
      ·
        refine ⟨54174993916716402124128293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144466650444577072331008781 54174993916716402124128293)
        ·
          refine ⟨10157811359384325398274055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54174993916716402124128293 10157811359384325398274055)
          ·
            refine ⟨15236717039076488097411083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10157811359384325398274055 15236717039076488097411083)
            ·
              refine ⟨22855075558614732146116625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15236717039076488097411083 22855075558614732146116625)
              ·
                refine ⟨17141306668961049109587469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22855075558614732146116625 17141306668961049109587469)
                ·
                  refine ⟨6427990000860393416095301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17141306668961049109587469 6427990000860393416095301)
                  ·
                    refine ⟨1205248125161323765517869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6427990000860393416095301 1205248125161323765517869)
                    ·
                      rfl

theorem cell23_7041637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_7041637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041637 prefixEnd_7041637 := by exact prefixLift 7041637
  have htrace : WordTrace (prefixWord ++ tailWord_7041637) baseStart_7041637 baseEnd_7041637 := by
    simpa [prefixWord, tailWord_7041637, baseEnd_7041637] using wordTrace_append hprefix tailTrace_7041637
  have hstable : (prefixWord ++ tailWord_7041637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041637).length < 2 ^ (prefixWord ++ tailWord_7041637).sum := by decide
  have hdescent : baseEnd_7041637 < baseStart_7041637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041643 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 3]
def baseStart_7041643 : Nat := 118140960795 + 7041643 * 2 ^ 59
def prefixEnd_7041643 : Nat := 4983230072969 + 3 ^ 40 * 7041643 * 2
def baseEnd_7041643 : Nat := 3615747456367898273078579

theorem tailTrace_7041643 : CollatzResearch.WordTrace tailWord_7041643 prefixEnd_7041643 3615747456367898273078579 := by
  unfold tailWord_7041643
  simp only [CollatzResearch.WordTrace]
  refine ⟨256829819628337502724289583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171219879752225001816193055 256829819628337502724289583)
  ·
    refine ⟨385244729442506254086434375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256829819628337502724289583 385244729442506254086434375)
    ·
      refine ⟨577867094163759381129651563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385244729442506254086434375 577867094163759381129651563)
      ·
        refine ⟨866800641245639071694477345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577867094163759381129651563 866800641245639071694477345)
        ·
          refine ⟨650100480934229303770858009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866800641245639071694477345 650100480934229303770858009)
          ·
            refine ⟨487575360700671977828143507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650100480934229303770858009 487575360700671977828143507)
            ·
              refine ⟨731363041051007966742215261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487575360700671977828143507 731363041051007966742215261)
              ·
                refine ⟨274261140394127987528330723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 731363041051007966742215261 274261140394127987528330723)
                ·
                  refine ⟨411391710591191981292496085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274261140394127987528330723 411391710591191981292496085)
                  ·
                    refine ⟨9641993216981062061542877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 411391710591191981292496085 9641993216981062061542877)
                    ·
                      refine ⟨3615747456367898273078579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9641993216981062061542877 3615747456367898273078579)
                      ·
                        rfl

theorem cell23_7041643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 3].length) (baseStart_7041643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041643 prefixEnd_7041643 := by exact prefixLift 7041643
  have htrace : WordTrace (prefixWord ++ tailWord_7041643) baseStart_7041643 baseEnd_7041643 := by
    simpa [prefixWord, tailWord_7041643, baseEnd_7041643] using wordTrace_append hprefix tailTrace_7041643
  have hstable : (prefixWord ++ tailWord_7041643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041643).length < 2 ^ (prefixWord ++ tailWord_7041643).sum := by decide
  have hdescent : baseEnd_7041643 < baseStart_7041643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041663 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 5, 5]
def baseStart_7041663 : Nat := 118140960795 + 7041663 * 2 ^ 59
def prefixEnd_7041663 : Nat := 4983230072969 + 3 ^ 40 * 7041663 * 2
def baseEnd_7041663 : Nat := 1205252575326996064942829

theorem tailTrace_7041663 : CollatzResearch.WordTrace tailWord_7041663 prefixEnd_7041663 1205252575326996064942829 := by
  unfold tailWord_7041663
  simp only [CollatzResearch.WordTrace]
  refine ⟨256830549088265046140017643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171220366058843364093345095 256830549088265046140017643)
  ·
    refine ⟨385245823632397569210026465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256830549088265046140017643 385245823632397569210026465)
    ·
      refine ⟨288934367724298176907519849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385245823632397569210026465 288934367724298176907519849)
      ·
        refine ⟨216700775793223632680639887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288934367724298176907519849 216700775793223632680639887)
        ·
          refine ⟨325051163689835449020959831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216700775793223632680639887 325051163689835449020959831)
          ·
            refine ⟨487576745534753173531439747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325051163689835449020959831 487576745534753173531439747)
            ·
              refine ⟨731365118302129760297159621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487576745534753173531439747 731365118302129760297159621)
              ·
                refine ⟨137130959681649330055717429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 731365118302129760297159621 137130959681649330055717429)
                ·
                  refine ⟨12856027470154624692723509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137130959681649330055717429 12856027470154624692723509)
                  ·
                    refine ⟨1205252575326996064942829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12856027470154624692723509 1205252575326996064942829)
                    ·
                      rfl

theorem cell23_7041663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_7041663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041663 prefixEnd_7041663 := by exact prefixLift 7041663
  have htrace : WordTrace (prefixWord ++ tailWord_7041663) baseStart_7041663 baseEnd_7041663 := by
    simpa [prefixWord, tailWord_7041663, baseEnd_7041663] using wordTrace_append hprefix tailTrace_7041663
  have hstable : (prefixWord ++ tailWord_7041663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041663).length < 2 ^ (prefixWord ++ tailWord_7041663).sum := by decide
  have hdescent : baseEnd_7041663 < baseStart_7041663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041684 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 6]
def baseStart_7041684 : Nat := 118140960795 + 7041684 * 2 ^ 59
def prefixEnd_7041684 : Nat := 4983230072969 + 3 ^ 40 * 7041684 * 2
def baseEnd_7041684 : Nat := 401752056563859179185099

theorem tailTrace_7041684 : CollatzResearch.WordTrace tailWord_7041684 prefixEnd_7041684 401752056563859179185099 := by
  unfold tailWord_7041684
  simp only [CollatzResearch.WordTrace]
  refine ⟨128415657510594483363266053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171220876680792644484354737 128415657510594483363266053)
  ·
    refine ⟨24077935783236465630612385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128415657510594483363266053 24077935783236465630612385)
    ·
      refine ⟨18058451837427349222959289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24077935783236465630612385 18058451837427349222959289)
      ·
        refine ⟨13543838878070511917219467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18058451837427349222959289 13543838878070511917219467)
        ·
          refine ⟨20315758317105767875829201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13543838878070511917219467 20315758317105767875829201)
          ·
            refine ⟨15236818737829325906871901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20315758317105767875829201 15236818737829325906871901)
            ·
              refine ⟨5713807026685997215076963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15236818737829325906871901 5713807026685997215076963)
              ·
                refine ⟨8570710540028995822615445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713807026685997215076963 8570710540028995822615445)
                ·
                  refine ⟨401752056563859179185099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8570710540028995822615445 401752056563859179185099)
                  ·
                    rfl

theorem cell23_7041684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_7041684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041684 prefixEnd_7041684 := by exact prefixLift 7041684
  have htrace : WordTrace (prefixWord ++ tailWord_7041684) baseStart_7041684 baseEnd_7041684 := by
    simpa [prefixWord, tailWord_7041684, baseEnd_7041684] using wordTrace_append hprefix tailTrace_7041684
  have hstable : (prefixWord ++ tailWord_7041684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041684).length < 2 ^ (prefixWord ++ tailWord_7041684).sum := by decide
  have hdescent : baseEnd_7041684 < baseStart_7041684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041694 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_7041694 : Nat := 118140960795 + 7041694 * 2 ^ 59
def prefixEnd_7041694 : Nat := 4983230072969 + 3 ^ 40 * 7041694 * 2
def baseEnd_7041694 : Nat := 3615773643881277573540845

theorem tailTrace_7041694 : CollatzResearch.WordTrace tailWord_7041694 prefixEnd_7041694 3615773643881277573540845 := by
  unfold tailWord_7041694
  simp only [CollatzResearch.WordTrace]
  refine ⟨32103959968894092304299517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171221119834101825622930757 32103959968894092304299517)
  ·
    refine ⟨12038984988335284614112319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32103959968894092304299517 12038984988335284614112319)
    ·
      refine ⟨18058477482502926921168479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12038984988335284614112319 18058477482502926921168479)
      ·
        refine ⟨27087716223754390381752719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18058477482502926921168479 27087716223754390381752719)
        ·
          refine ⟨40631574335631585572629079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27087716223754390381752719 40631574335631585572629079)
          ·
            refine ⟨60947361503447378358943619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40631574335631585572629079 60947361503447378358943619)
            ·
              refine ⟨91421042255171067538415429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60947361503447378358943619 91421042255171067538415429)
              ·
                refine ⟨17141445422844575163452893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91421042255171067538415429 17141445422844575163452893)
                ·
                  refine ⟨6428042033566715686294835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17141445422844575163452893 6428042033566715686294835)
                  ·
                    refine ⟨9642063050350073529442253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6428042033566715686294835 9642063050350073529442253)
                    ·
                      refine ⟨3615773643881277573540845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642063050350073529442253 3615773643881277573540845)
                      ·
                        rfl

theorem cell23_7041694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_7041694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041694 prefixEnd_7041694 := by exact prefixLift 7041694
  have htrace : WordTrace (prefixWord ++ tailWord_7041694) baseStart_7041694 baseEnd_7041694 := by
    simpa [prefixWord, tailWord_7041694, baseEnd_7041694] using wordTrace_append hprefix tailTrace_7041694
  have hstable : (prefixWord ++ tailWord_7041694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041694).length < 2 ^ (prefixWord ++ tailWord_7041694).sum := by decide
  have hdescent : baseEnd_7041694 < baseStart_7041694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041711 : List Nat := [1, 1, 2, 1, 2, 7, 1, 3, 1, 1, 3]
def baseStart_7041711 : Nat := 118140960795 + 7041711 * 2 ^ 59
def prefixEnd_7041711 : Nat := 4983230072969 + 3 ^ 40 * 7041711 * 2
def baseEnd_7041711 : Nat := 3615782373052404007028267

theorem tailTrace_7041711 : CollatzResearch.WordTrace tailWord_7041711 prefixEnd_7041711 3615782373052404007028267 := by
  unfold tailWord_7041711
  simp only [CollatzResearch.WordTrace]
  refine ⟨256832299792091150337764987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171221533194727433558509991 256832299792091150337764987)
  ·
    refine ⟨385248449688136725506647481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256832299792091150337764987 385248449688136725506647481)
    ·
      refine ⟨288936337266102544129985611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385248449688136725506647481 288936337266102544129985611)
      ·
        refine ⟨433404505899153816194978417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288936337266102544129985611 433404505899153816194978417)
        ·
          refine ⟨325053379424365362146233813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433404505899153816194978417 325053379424365362146233813)
          ·
            refine ⟨7618438580258563175302355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 325053379424365362146233813 7618438580258563175302355)
            ·
              refine ⟨11427657870387844762953533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7618438580258563175302355 11427657870387844762953533)
              ·
                refine ⟨4285371701395441786107575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11427657870387844762953533 4285371701395441786107575)
                ·
                  refine ⟨6428057552093162679161363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285371701395441786107575 6428057552093162679161363)
                  ·
                    refine ⟨9642086328139744018742045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6428057552093162679161363 9642086328139744018742045)
                    ·
                      refine ⟨3615782373052404007028267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642086328139744018742045 3615782373052404007028267)
                      ·
                        rfl

theorem cell23_7041711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 1, 1, 3].length) (baseStart_7041711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041711 prefixEnd_7041711 := by exact prefixLift 7041711
  have htrace : WordTrace (prefixWord ++ tailWord_7041711) baseStart_7041711 baseEnd_7041711 := by
    simpa [prefixWord, tailWord_7041711, baseEnd_7041711] using wordTrace_append hprefix tailTrace_7041711
  have hstable : (prefixWord ++ tailWord_7041711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041711).length < 2 ^ (prefixWord ++ tailWord_7041711).sum := by decide
  have hdescent : baseEnd_7041711 < baseStart_7041711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041720 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 7, 2, 3]
def baseStart_7041720 : Nat := 118140960795 + 7041720 * 2 ^ 59
def prefixEnd_7041720 : Nat := 4983230072969 + 3 ^ 40 * 7041720 * 2
def baseEnd_7041720 : Nat := 3615786994378294471815725

theorem tailTrace_7041720 : CollatzResearch.WordTrace tailWord_7041720 prefixEnd_7041720 3615786994378294471815725 := by
  unfold tailWord_7041720
  simp only [CollatzResearch.WordTrace]
  refine ⟨128416314024529272437421307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171221752032705696583228409 128416314024529272437421307)
  ·
    refine ⟨192624471036793908656131961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128416314024529272437421307 192624471036793908656131961)
    ·
      refine ⟨144468353277595431492098971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192624471036793908656131961 144468353277595431492098971)
      ·
        refine ⟨216702529916393147238148457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144468353277595431492098971 216702529916393147238148457)
        ·
          refine ⟨162526897437294860428611343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216702529916393147238148457 162526897437294860428611343)
          ·
            refine ⟨243790346155942290642917015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162526897437294860428611343 243790346155942290642917015)
            ·
              refine ⟨365685519233913435964375523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243790346155942290642917015 365685519233913435964375523)
              ·
                refine ⟨548528278850870153946563285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365685519233913435964375523 548528278850870153946563285)
                ·
                  refine ⟨12856131535567269233122577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 548528278850870153946563285 12856131535567269233122577)
                  ·
                    refine ⟨9642098651675451924841933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12856131535567269233122577 9642098651675451924841933)
                    ·
                      refine ⟨3615786994378294471815725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642098651675451924841933 3615786994378294471815725)
                      ·
                        rfl

theorem cell23_7041720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_7041720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041720 prefixEnd_7041720 := by exact prefixLift 7041720
  have htrace : WordTrace (prefixWord ++ tailWord_7041720) baseStart_7041720 baseEnd_7041720 := by
    simpa [prefixWord, tailWord_7041720, baseEnd_7041720] using wordTrace_append hprefix tailTrace_7041720
  have hstable : (prefixWord ++ tailWord_7041720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041720).length < 2 ^ (prefixWord ++ tailWord_7041720).sum := by decide
  have hdescent : baseEnd_7041720 < baseStart_7041720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041733 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_7041733 : Nat := 118140960795 + 7041733 * 2 ^ 59
def prefixEnd_7041733 : Nat := 4983230072969 + 3 ^ 40 * 7041733 * 2
def baseEnd_7041733 : Nat := 3615793669626802920953165

theorem tailTrace_7041733 : CollatzResearch.WordTrace tailWord_7041733 prefixEnd_7041733 3615793669626802920953165 := by
  unfold tailWord_7041733
  simp only [CollatzResearch.WordTrace]
  refine ⟨256833102198011448095065853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171222068132007632063377235 256833102198011448095065853)
  ·
    refine ⟨96312413324254293035649695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256833102198011448095065853 96312413324254293035649695)
    ·
      refine ⟨144468619986381439553474543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96312413324254293035649695 144468619986381439553474543)
      ·
        refine ⟨216702929979572159330211815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144468619986381439553474543 216702929979572159330211815)
        ·
          refine ⟨325054394969358238995317723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216702929979572159330211815 325054394969358238995317723)
          ·
            refine ⟨487581592454037358492976585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325054394969358238995317723 487581592454037358492976585)
            ·
              refine ⟨365686194340528018869732439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487581592454037358492976585 365686194340528018869732439)
              ·
                refine ⟨548529291510792028304598659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365686194340528018869732439 548529291510792028304598659)
                ·
                  refine ⟨822793937266188042456897989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548529291510792028304598659 822793937266188042456897989)
                  ·
                    refine ⟨154273863237410257960668373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 822793937266188042456897989 154273863237410257960668373)
                    ·
                      refine ⟨3615793669626802920953165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154273863237410257960668373 3615793669626802920953165)
                      ·
                        rfl

theorem cell23_7041733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_7041733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041733 prefixEnd_7041733 := by exact prefixLift 7041733
  have htrace : WordTrace (prefixWord ++ tailWord_7041733) baseStart_7041733 baseEnd_7041733 := by
    simpa [prefixWord, tailWord_7041733, baseEnd_7041733] using wordTrace_append hprefix tailTrace_7041733
  have hstable : (prefixWord ++ tailWord_7041733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041733).length < 2 ^ (prefixWord ++ tailWord_7041733).sum := by decide
  have hdescent : baseEnd_7041733 < baseStart_7041733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041740 : List Nat := [2, 2, 1, 5, 1, 1, 1, 10]
def baseStart_7041740 : Nat := 118140960795 + 7041740 * 2 ^ 59
def prefixEnd_7041740 : Nat := 4983230072969 + 3 ^ 40 * 7041740 * 2
def baseEnd_7041740 : Nat := 133918417184866088650579

theorem tailTrace_7041740 : CollatzResearch.WordTrace tailWord_7041740 prefixEnd_7041740 133918417184866088650579 := by
  unfold tailWord_7041740
  simp only [CollatzResearch.WordTrace]
  refine ⟨128416678754493044145285337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171222238339324058860380449 128416678754493044145285337)
  ·
    refine ⟨96312509065869783108964003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128416678754493044145285337 96312509065869783108964003)
    ·
      refine ⟨144468763598804674663446005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96312509065869783108964003 144468763598804674663446005)
      ·
        refine ⟨13543946587387938249698063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144468763598804674663446005 13543946587387938249698063)
        ·
          refine ⟨20315919881081907374547095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13543946587387938249698063 20315919881081907374547095)
          ·
            refine ⟨30473879821622861061820643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20315919881081907374547095 30473879821622861061820643)
            ·
              refine ⟨45710819732434291592730965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30473879821622861061820643 45710819732434291592730965)
              ·
                refine ⟨133918417184866088650579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45710819732434291592730965 133918417184866088650579)
                ·
                  rfl

theorem cell23_7041740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 10].length) (baseStart_7041740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041740 prefixEnd_7041740 := by exact prefixLift 7041740
  have htrace : WordTrace (prefixWord ++ tailWord_7041740) baseStart_7041740 baseEnd_7041740 := by
    simpa [prefixWord, tailWord_7041740, baseEnd_7041740] using wordTrace_append hprefix tailTrace_7041740
  have hstable : (prefixWord ++ tailWord_7041740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041740).length < 2 ^ (prefixWord ++ tailWord_7041740).sum := by decide
  have hdescent : baseEnd_7041740 < baseStart_7041740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041784 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 2, 1, 3]
def baseStart_7041784 : Nat := 118140960795 + 7041784 * 2 ^ 59
def prefixEnd_7041784 : Nat := 4983230072969 + 3 ^ 40 * 7041784 * 2
def baseEnd_7041784 : Nat := 3615819857140182221415431

theorem tailTrace_7041784 : CollatzResearch.WordTrace tailWord_7041784 prefixEnd_7041784 3615819857140182221415431 := by
  unfold tailWord_7041784
  simp only [CollatzResearch.WordTrace]
  refine ⟨128417481160413341902586203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171223308213884455870114937 128417481160413341902586203)
  ·
    refine ⟨192626221740620012853879305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128417481160413341902586203 192626221740620012853879305)
    ·
      refine ⟨144469666305465009640409479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192626221740620012853879305 144469666305465009640409479)
      ·
        refine ⟨216704499458197514460614219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144469666305465009640409479 216704499458197514460614219)
        ·
          refine ⟨325056749187296271690921329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216704499458197514460614219 325056749187296271690921329)
          ·
            refine ⟨243792561890472203768190997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325056749187296271690921329 243792561890472203768190997)
            ·
              refine ⟨11427776338615884551633953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 243792561890472203768190997 11427776338615884551633953)
              ·
                refine ⟨8570832253961913413725465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11427776338615884551633953 8570832253961913413725465)
                ·
                  refine ⟨6428124190471435060294099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8570832253961913413725465 6428124190471435060294099)
                  ·
                    refine ⟨9642186285707152590441149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6428124190471435060294099 9642186285707152590441149)
                    ·
                      refine ⟨3615819857140182221415431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642186285707152590441149 3615819857140182221415431)
                      ·
                        rfl

theorem cell23_7041784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_7041784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041784 prefixEnd_7041784 := by exact prefixLift 7041784
  have htrace : WordTrace (prefixWord ++ tailWord_7041784) baseStart_7041784 baseEnd_7041784 := by
    simpa [prefixWord, tailWord_7041784, baseEnd_7041784] using wordTrace_append hprefix tailTrace_7041784
  have hstable : (prefixWord ++ tailWord_7041784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041784).length < 2 ^ (prefixWord ++ tailWord_7041784).sum := by decide
  have hdescent : baseEnd_7041784 < baseStart_7041784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041800 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 1, 8]
def baseStart_7041800 : Nat := 118140960795 + 7041800 * 2 ^ 59
def prefixEnd_7041800 : Nat := 4983230072969 + 3 ^ 40 * 7041800 * 2
def baseEnd_7041800 : Nat := 1205276024276884719605119

theorem tailTrace_7041800 : CollatzResearch.WordTrace tailWord_7041800 prefixEnd_7041800 1205276024276884719605119 := by
  unfold tailWord_7041800
  simp only [CollatzResearch.WordTrace]
  refine ⟨128417772944384359268877427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171223697259179145691836569 128417772944384359268877427)
  ·
    refine ⟨192626659416576538903316141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128417772944384359268877427 192626659416576538903316141)
    ·
      refine ⟨72234997281216202088743553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192626659416576538903316141 72234997281216202088743553)
      ·
        refine ⟨54176247960912151566557665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72234997281216202088743553 54176247960912151566557665)
        ·
          refine ⟨40632185970684113674918249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54176247960912151566557665 40632185970684113674918249)
          ·
            refine ⟨30474139478013085256188687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40632185970684113674918249 30474139478013085256188687)
            ·
              refine ⟨45711209217019627884283031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30474139478013085256188687 45711209217019627884283031)
              ·
                refine ⟨68566813825529441826424547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45711209217019627884283031 68566813825529441826424547)
                ·
                  refine ⟨102850220738294162739636821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68566813825529441826424547 102850220738294162739636821)
                  ·
                    refine ⟨1205276024276884719605119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102850220738294162739636821 1205276024276884719605119)
                    ·
                      rfl

theorem cell23_7041800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_7041800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041800 prefixEnd_7041800 := by exact prefixLift 7041800
  have htrace : WordTrace (prefixWord ++ tailWord_7041800) baseStart_7041800 baseEnd_7041800 := by
    simpa [prefixWord, tailWord_7041800, baseEnd_7041800] using wordTrace_append hprefix tailTrace_7041800
  have hstable : (prefixWord ++ tailWord_7041800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041800).length < 2 ^ (prefixWord ++ tailWord_7041800).sum := by decide
  have hdescent : baseEnd_7041800 < baseStart_7041800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041824 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 1, 4, 2]
def baseStart_7041824 : Nat := 118140960795 + 7041824 * 2 ^ 59
def prefixEnd_7041824 : Nat := 4983230072969 + 3 ^ 40 * 7041824 * 2
def baseEnd_7041824 : Nat := 3615840396366362064915247

theorem tailTrace_7041824 : CollatzResearch.WordTrace tailWord_7041824 prefixEnd_7041824 3615840396366362064915247 := by
  unfold tailWord_7041824
  simp only [CollatzResearch.WordTrace]
  refine ⟨128418210620340885318314263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171224280827121180424419017 128418210620340885318314263)
  ·
    refine ⟨192627315930511327977471395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128418210620340885318314263 192627315930511327977471395)
    ·
      refine ⟨288940973895766991966207093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192627315930511327977471395 288940973895766991966207093)
      ·
        refine ⟨27088216302728155496831915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 288940973895766991966207093 27088216302728155496831915)
        ·
          refine ⟨40632324454092233245247873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27088216302728155496831915 40632324454092233245247873)
          ·
            refine ⟨30474243340569174933935905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40632324454092233245247873 30474243340569174933935905)
            ·
              refine ⟨22855682505426881200451929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30474243340569174933935905 22855682505426881200451929)
              ·
                refine ⟨17141761879070160900338947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22855682505426881200451929 17141761879070160900338947)
                ·
                  refine ⟨25712642818605241350508421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17141761879070160900338947 25712642818605241350508421)
                  ·
                    refine ⟨4821120528488482753220329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25712642818605241350508421 4821120528488482753220329)
                    ·
                      refine ⟨3615840396366362064915247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4821120528488482753220329 3615840396366362064915247)
                      ·
                        rfl

theorem cell23_7041824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_7041824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041824 prefixEnd_7041824 := by exact prefixLift 7041824
  have htrace : WordTrace (prefixWord ++ tailWord_7041824) baseStart_7041824 baseEnd_7041824 := by
    simpa [prefixWord, tailWord_7041824, baseEnd_7041824] using wordTrace_append hprefix tailTrace_7041824
  have hstable : (prefixWord ++ tailWord_7041824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041824).length < 2 ^ (prefixWord ++ tailWord_7041824).sum := by decide
  have hdescent : baseEnd_7041824 < baseStart_7041824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041847 : List Nat := [1, 1, 3, 1, 2, 1, 3, 6, 5]
def baseStart_7041847 : Nat := 118140960795 + 7041847 * 2 ^ 59
def prefixEnd_7041847 : Nat := 4983230072969 + 3 ^ 40 * 7041847 * 2
def baseEnd_7041847 : Nat := 401761356269046163880849

theorem tailTrace_7041847 : CollatzResearch.WordTrace tailWord_7041847 prefixEnd_7041847 401761356269046163880849 := by
  unfold tailWord_7041847
  simp only [CollatzResearch.WordTrace]
  refine ⟨256837260119598445564715795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171224840079732297043143863 256837260119598445564715795)
  ·
    refine ⟨385255890179397668347073693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256837260119598445564715795 385255890179397668347073693)
    ·
      refine ⟨144470958817274125630152635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385255890179397668347073693 144470958817274125630152635)
      ·
        refine ⟨216706438225911188445228953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144470958817274125630152635 216706438225911188445228953)
        ·
          refine ⟨162529828669433391333921715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216706438225911188445228953 162529828669433391333921715)
          ·
            refine ⟨243794743004150087000882573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162529828669433391333921715 243794743004150087000882573)
            ·
              refine ⟨91423028626556282625330965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243794743004150087000882573 91423028626556282625330965)
              ·
                refine ⟨4285454466869825748062389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91423028626556282625330965 4285454466869825748062389)
                ·
                  refine ⟨401761356269046163880849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4285454466869825748062389 401761356269046163880849)
                  ·
                    rfl

theorem cell23_7041847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 5].length) (baseStart_7041847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041847 prefixEnd_7041847 := by exact prefixLift 7041847
  have htrace : WordTrace (prefixWord ++ tailWord_7041847) baseStart_7041847 baseEnd_7041847 := by
    simpa [prefixWord, tailWord_7041847, baseEnd_7041847] using wordTrace_append hprefix tailTrace_7041847
  have hstable : (prefixWord ++ tailWord_7041847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041847).length < 2 ^ (prefixWord ++ tailWord_7041847).sum := by decide
  have hdescent : baseEnd_7041847 < baseStart_7041847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041877 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_7041877 : Nat := 118140960795 + 7041877 * 2 ^ 59
def prefixEnd_7041877 : Nat := 4983230072969 + 3 ^ 40 * 7041877 * 2
def baseEnd_7041877 : Nat := 1205289203613683452517501

theorem tailTrace_7041877 : CollatzResearch.WordTrace tailWord_7041877 prefixEnd_7041877 1205289203613683452517501 := by
  unfold tailWord_7041877
  simp only [CollatzResearch.WordTrace]
  refine ⟨256838354309489760688307885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171225569539659840458871923 256838354309489760688307885)
  ·
    refine ⟨96314382866058660258115457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256838354309489760688307885 96314382866058660258115457)
    ·
      refine ⟨72235787149543995193586593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96314382866058660258115457 72235787149543995193586593)
      ·
        refine ⟨54176840362157996395189945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72235787149543995193586593 54176840362157996395189945)
        ·
          refine ⟨40632630271618497296392459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54176840362157996395189945 40632630271618497296392459)
          ·
            refine ⟨60948945407427745944588689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40632630271618497296392459 60948945407427745944588689)
            ·
              refine ⟨45711709055570809458441517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60948945407427745944588689 45711709055570809458441517)
              ·
                refine ⟨17141890895839053546915569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45711709055570809458441517 17141890895839053546915569)
                ·
                  refine ⟨12856418171879290160186677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17141890895839053546915569 12856418171879290160186677)
                  ·
                    refine ⟨1205289203613683452517501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12856418171879290160186677 1205289203613683452517501)
                    ·
                      rfl

theorem cell23_7041877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_7041877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041877 prefixEnd_7041877 := by exact prefixLift 7041877
  have htrace : WordTrace (prefixWord ++ tailWord_7041877) baseStart_7041877 baseEnd_7041877 := by
    simpa [prefixWord, tailWord_7041877, baseEnd_7041877] using wordTrace_append hprefix tailTrace_7041877
  have hstable : (prefixWord ++ tailWord_7041877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041877).length < 2 ^ (prefixWord ++ tailWord_7041877).sum := by decide
  have hdescent : baseEnd_7041877 < baseStart_7041877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041917 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_7041917 : Nat := 118140960795 + 7041917 * 2 ^ 59
def prefixEnd_7041917 : Nat := 4983230072969 + 3 ^ 40 * 7041917 * 2
def baseEnd_7041917 : Nat := 3615888150067230201052319

theorem tailTrace_7041917 : CollatzResearch.WordTrace tailWord_7041917 prefixEnd_7041917 3615888150067230201052319 := by
  unfold tailWord_7041917
  simp only [CollatzResearch.WordTrace]
  refine ⟨256839813229344847519764005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171226542152896565013176003 256839813229344847519764005)
  ·
    refine ⟨48157464980502158909955751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256839813229344847519764005 48157464980502158909955751)
    ·
      refine ⟨72236197470753238364933627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48157464980502158909955751 72236197470753238364933627)
      ·
        refine ⟨108354296206129857547400441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72236197470753238364933627 108354296206129857547400441)
        ·
          refine ⟨81265722154597393160550331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108354296206129857547400441 81265722154597393160550331)
          ·
            refine ⟨121898583231896089740825497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81265722154597393160550331 121898583231896089740825497)
            ·
              refine ⟨91423937423922067305619123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121898583231896089740825497 91423937423922067305619123)
              ·
                refine ⟨137135906135883100958428685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91423937423922067305619123 137135906135883100958428685)
                ·
                  refine ⟨51425964800956162859410757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137135906135883100958428685 51425964800956162859410757)
                  ·
                    refine ⟨9642368400179280536139517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51425964800956162859410757 9642368400179280536139517)
                    ·
                      refine ⟨3615888150067230201052319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642368400179280536139517 3615888150067230201052319)
                      ·
                        rfl

theorem cell23_7041917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_7041917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041917 prefixEnd_7041917 := by exact prefixLift 7041917
  have htrace : WordTrace (prefixWord ++ tailWord_7041917) baseStart_7041917 baseEnd_7041917 := by
    simpa [prefixWord, tailWord_7041917, baseEnd_7041917] using wordTrace_append hprefix tailTrace_7041917
  have hstable : (prefixWord ++ tailWord_7041917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041917).length < 2 ^ (prefixWord ++ tailWord_7041917).sum := by decide
  have hdescent : baseEnd_7041917 < baseStart_7041917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041920 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 10]
def baseStart_7041920 : Nat := 118140960795 + 7041920 * 2 ^ 59
def prefixEnd_7041920 : Nat := 4983230072969 + 3 ^ 40 * 7041920 * 2
def baseEnd_7041920 : Nat := 401765521167688187701645

theorem tailTrace_7041920 : CollatzResearch.WordTrace tailWord_7041920 prefixEnd_7041920 401765521167688187701645 := by
  unfold tailWord_7041920
  simp only [CollatzResearch.WordTrace]
  refine ⟨128419961324166989516061607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171226615098889319354748809 128419961324166989516061607)
  ·
    refine ⟨192629941986250484274092411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128419961324166989516061607 192629941986250484274092411)
    ·
      refine ⟨288944912979375726411138617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192629941986250484274092411 288944912979375726411138617)
      ·
        refine ⟨216708684734531794808353963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288944912979375726411138617 216708684734531794808353963)
        ·
          refine ⟨325063027101797692212530945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216708684734531794808353963 325063027101797692212530945)
          ·
            refine ⟨243797270326348269159398209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325063027101797692212530945 243797270326348269159398209)
            ·
              refine ⟨182847952744761201869548657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243797270326348269159398209 182847952744761201869548657)
              ·
                refine ⟨137135964558570901402161493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182847952744761201869548657 137135964558570901402161493)
                ·
                  refine ⟨401765521167688187701645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 137135964558570901402161493 401765521167688187701645)
                  ·
                    rfl

theorem cell23_7041920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 10].length) (baseStart_7041920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041920 prefixEnd_7041920 := by exact prefixLift 7041920
  have htrace : WordTrace (prefixWord ++ tailWord_7041920) baseStart_7041920 baseEnd_7041920 := by
    simpa [prefixWord, tailWord_7041920, baseEnd_7041920] using wordTrace_append hprefix tailTrace_7041920
  have hstable : (prefixWord ++ tailWord_7041920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041920).length < 2 ^ (prefixWord ++ tailWord_7041920).sum := by decide
  have hdescent : baseEnd_7041920 < baseStart_7041920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041954 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 6]
def baseStart_7041954 : Nat := 118140960795 + 7041954 * 2 ^ 59
def prefixEnd_7041954 : Nat := 4983230072969 + 3 ^ 40 * 7041954 * 2
def baseEnd_7041954 : Nat := 401767460983494061809961

theorem tailTrace_7041954 : CollatzResearch.WordTrace tailWord_7041954 prefixEnd_7041954 401767460983494061809961 := by
  unfold tailWord_7041954
  simp only [CollatzResearch.WordTrace]
  refine ⟨64210290682552700709715229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171227441820140535225907277 64210290682552700709715229)
  ·
    refine ⟨24078859005957262766143211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64210290682552700709715229 24078859005957262766143211)
    ·
      refine ⟨36118288508935894149214817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24078859005957262766143211 36118288508935894149214817)
      ·
        refine ⟨27088716381701920611911113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36118288508935894149214817 27088716381701920611911113)
        ·
          refine ⟨20316537286276440458933335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27088716381701920611911113 20316537286276440458933335)
          ·
            refine ⟨30474805929414660688400003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20316537286276440458933335 30474805929414660688400003)
            ·
              refine ⟨45712208894121991032600005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30474805929414660688400003 45712208894121991032600005)
              ·
                refine ⟨8571039167647873318612501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45712208894121991032600005 8571039167647873318612501)
                ·
                  refine ⟨401767460983494061809961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8571039167647873318612501 401767460983494061809961)
                  ·
                    rfl

theorem cell23_7041954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_7041954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041954 prefixEnd_7041954 := by exact prefixLift 7041954
  have htrace : WordTrace (prefixWord ++ tailWord_7041954) baseStart_7041954 baseEnd_7041954 := by
    simpa [prefixWord, tailWord_7041954, baseEnd_7041954] using wordTrace_append hprefix tailTrace_7041954
  have hstable : (prefixWord ++ tailWord_7041954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041954).length < 2 ^ (prefixWord ++ tailWord_7041954).sum := by decide
  have hdescent : baseEnd_7041954 < baseStart_7041954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041991 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 2, 3, 2]
def baseStart_7041991 : Nat := 118140960795 + 7041991 * 2 ^ 59
def prefixEnd_7041991 : Nat := 4983230072969 + 3 ^ 40 * 7041991 * 2
def baseEnd_7041991 : Nat := 3615926147635662911526979

theorem tailTrace_7041991 : CollatzResearch.WordTrace tailWord_7041991 prefixEnd_7041991 3615926147635662911526979 := by
  unfold tailWord_7041991
  simp only [CollatzResearch.WordTrace]
  refine ⟨256842512231076758157957827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171228341487384505438638551 256842512231076758157957827)
  ·
    refine ⟨385263768346615137236936741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256842512231076758157957827 385263768346615137236936741)
    ·
      refine ⟨72236956564990338231925639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385263768346615137236936741 72236956564990338231925639)
      ·
        refine ⟨108355434847485507347888459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72236956564990338231925639 108355434847485507347888459)
        ·
          refine ⟨162533152271228261021832689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108355434847485507347888459 162533152271228261021832689)
          ·
            refine ⟨121899864203421195766374517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162533152271228261021832689 121899864203421195766374517)
            ·
              refine ⟨11428112269070737103097611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121899864203421195766374517 11428112269070737103097611)
              ·
                refine ⟨17142168403606105654646417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11428112269070737103097611 17142168403606105654646417)
                ·
                  refine ⟨12856626302704579240984813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17142168403606105654646417 12856626302704579240984813)
                  ·
                    refine ⟨4821234863514217215369305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12856626302704579240984813 4821234863514217215369305)
                    ·
                      refine ⟨3615926147635662911526979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4821234863514217215369305 3615926147635662911526979)
                      ·
                        rfl

theorem cell23_7041991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_7041991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041991 prefixEnd_7041991 := by exact prefixLift 7041991
  have htrace : WordTrace (prefixWord ++ tailWord_7041991) baseStart_7041991 baseEnd_7041991 := by
    simpa [prefixWord, tailWord_7041991, baseEnd_7041991] using wordTrace_append hprefix tailTrace_7041991
  have hstable : (prefixWord ++ tailWord_7041991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041991).length < 2 ^ (prefixWord ++ tailWord_7041991).sum := by decide
  have hdescent : baseEnd_7041991 < baseStart_7041991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7041998 : List Nat := [4, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3]
def baseStart_7041998 : Nat := 118140960795 + 7041998 * 2 ^ 59
def prefixEnd_7041998 : Nat := 4983230072969 + 3 ^ 40 * 7041998 * 2
def baseEnd_7041998 : Nat := 3615929742000244384139447

theorem tailTrace_7041998 : CollatzResearch.WordTrace tailWord_7041998 prefixEnd_7041998 3615929742000244384139447 := by
  unfold tailWord_7041998
  simp only [CollatzResearch.WordTrace]
  refine ⟨32105345942756424794182831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171228511694700932235641765 32105345942756424794182831)
  ·
    refine ⟨48158018914134637191274247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32105345942756424794182831 48158018914134637191274247)
    ·
      refine ⟨72237028371201955786911371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48158018914134637191274247 72237028371201955786911371)
      ·
        refine ⟨108355542556802933680367057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72237028371201955786911371 108355542556802933680367057)
        ·
          refine ⟨81266656917602200260275293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108355542556802933680367057 81266656917602200260275293)
          ·
            refine ⟨30474996344100825097603235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81266656917602200260275293 30474996344100825097603235)
            ·
              refine ⟨45712494516151237646404853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30474996344100825097603235 45712494516151237646404853)
              ·
                refine ⟨4285546360889178529350455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45712494516151237646404853 4285546360889178529350455)
                ·
                  refine ⟨6428319541333767794025683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285546360889178529350455 6428319541333767794025683)
                  ·
                    refine ⟨9642479312000651691038525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6428319541333767794025683 9642479312000651691038525)
                    ·
                      refine ⟨3615929742000244384139447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642479312000651691038525 3615929742000244384139447)
                      ·
                        rfl

theorem cell23_7041998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_7041998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7041998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7041998 prefixEnd_7041998 := by exact prefixLift 7041998
  have htrace : WordTrace (prefixWord ++ tailWord_7041998) baseStart_7041998 baseEnd_7041998 := by
    simpa [prefixWord, tailWord_7041998, baseEnd_7041998] using wordTrace_append hprefix tailTrace_7041998
  have hstable : (prefixWord ++ tailWord_7041998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7041998).length < 2 ^ (prefixWord ++ tailWord_7041998).sum := by decide
  have hdescent : baseEnd_7041998 < baseStart_7041998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7041998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042017 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_7042017 : Nat := 118140960795 + 7042017 * 2 ^ 59
def prefixEnd_7042017 : Nat := 4983230072969 + 3 ^ 40 * 7042017 * 2
def baseEnd_7042017 : Nat := 3615939498132679809801859

theorem tailTrace_7042017 : CollatzResearch.WordTrace tailWord_7042017 prefixEnd_7042017 3615939498132679809801859 := by
  unfold tailWord_7042017
  simp only [CollatzResearch.WordTrace]
  refine ⟨256843460528982564598404305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171228973685988376398936203 256843460528982564598404305)
  ·
    refine ⟨192632595396736923448803229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256843460528982564598404305 192632595396736923448803229)
    ·
      refine ⟨72237223273776346293301211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192632595396736923448803229 72237223273776346293301211)
      ·
        refine ⟨108355834910664519439951817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72237223273776346293301211 108355834910664519439951817)
        ·
          refine ⟨81266876182998389579963863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108355834910664519439951817 81266876182998389579963863)
          ·
            refine ⟨121900314274497584369945795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81266876182998389579963863 121900314274497584369945795)
            ·
              refine ⟨182850471411746376554918693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121900314274497584369945795 182850471411746376554918693)
              ·
                refine ⟨34284463389702445604047255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182850471411746376554918693 34284463389702445604047255)
                ·
                  refine ⟨51426695084553668406070883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34284463389702445604047255 51426695084553668406070883)
                  ·
                    refine ⟨77140042626830502609106325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51426695084553668406070883 77140042626830502609106325)
                    ·
                      refine ⟨3615939498132679809801859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77140042626830502609106325 3615939498132679809801859)
                      ·
                        rfl

theorem cell23_7042017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_7042017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042017 prefixEnd_7042017 := by exact prefixLift 7042017
  have htrace : WordTrace (prefixWord ++ tailWord_7042017) baseStart_7042017 baseEnd_7042017 := by
    simpa [prefixWord, tailWord_7042017, baseEnd_7042017] using wordTrace_append hprefix tailTrace_7042017
  have hstable : (prefixWord ++ tailWord_7042017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042017).length < 2 ^ (prefixWord ++ tailWord_7042017).sum := by decide
  have hdescent : baseEnd_7042017 < baseStart_7042017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042024 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_7042024 : Nat := 118140960795 + 7042024 * 2 ^ 59
def prefixEnd_7042024 : Nat := 4983230072969 + 3 ^ 40 * 7042024 * 2
def baseEnd_7042024 : Nat := 3615943092497261282414327

theorem tailTrace_7042024 : CollatzResearch.WordTrace tailWord_7042024 prefixEnd_7042024 3615943092497261282414327 := by
  unfold tailWord_7042024
  simp only [CollatzResearch.WordTrace]
  refine ⟨128421857919978602396954563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171229143893304803195939417 128421857919978602396954563)
  ·
    refine ⟨192632786879967903595431845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128421857919978602396954563 192632786879967903595431845)
    ·
      refine ⟨36118647539993981924143471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192632786879967903595431845 36118647539993981924143471)
      ·
        refine ⟨54177971309990972886215207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36118647539993981924143471 54177971309990972886215207)
        ·
          refine ⟨81266956964986459329322811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54177971309990972886215207 81266956964986459329322811)
          ·
            refine ⟨121900435447479688993984217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81266956964986459329322811 121900435447479688993984217)
            ·
              refine ⟨91425326585609766745488163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121900435447479688993984217 91425326585609766745488163)
              ·
                refine ⟨137137989878414650118232245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91425326585609766745488163 137137989878414650118232245)
                ·
                  refine ⟨12856686551101373448584273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137137989878414650118232245 12856686551101373448584273)
                  ·
                    refine ⟨9642514913326030086438205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12856686551101373448584273 9642514913326030086438205)
                    ·
                      refine ⟨3615943092497261282414327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642514913326030086438205 3615943092497261282414327)
                      ·
                        rfl

theorem cell23_7042024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_7042024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042024 prefixEnd_7042024 := by exact prefixLift 7042024
  have htrace : WordTrace (prefixWord ++ tailWord_7042024) baseStart_7042024 baseEnd_7042024 := by
    simpa [prefixWord, tailWord_7042024, baseEnd_7042024] using wordTrace_append hprefix tailTrace_7042024
  have hstable : (prefixWord ++ tailWord_7042024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042024).length < 2 ^ (prefixWord ++ tailWord_7042024).sum := by decide
  have hdescent : baseEnd_7042024 < baseStart_7042024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042038 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_7042038 : Nat := 118140960795 + 7042038 * 2 ^ 59
def prefixEnd_7042038 : Nat := 4983230072969 + 3 ^ 40 * 7042038 * 2
def baseEnd_7042038 : Nat := 3615950281226424227639263

theorem tailTrace_7042038 : CollatzResearch.WordTrace tailWord_7042038 prefixEnd_7042038 3615950281226424227639263 := by
  unfold tailWord_7042038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16052764153869155324057423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171229484307937656789945845 16052764153869155324057423)
  ·
    refine ⟨24079146230803732986086135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16052764153869155324057423 24079146230803732986086135)
    ·
      refine ⟨36118719346205599479129203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24079146230803732986086135 36118719346205599479129203)
      ·
        refine ⟨54178079019308399218693805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36118719346205599479129203 54178079019308399218693805)
        ·
          refine ⟨20316779632240649707010177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54178079019308399218693805 20316779632240649707010177)
          ·
            refine ⟨15237584724180487280257633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20316779632240649707010177 15237584724180487280257633)
            ·
              refine ⟨11428188543135365460193225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15237584724180487280257633 11428188543135365460193225)
              ·
                refine ⟨8571141407351524095144919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11428188543135365460193225 8571141407351524095144919)
                ·
                  refine ⟨12856712111027286142717379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8571141407351524095144919 12856712111027286142717379)
                  ·
                    refine ⟨19285068166540929214076069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12856712111027286142717379 19285068166540929214076069)
                    ·
                      refine ⟨3615950281226424227639263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19285068166540929214076069 3615950281226424227639263)
                      ·
                        rfl

theorem cell23_7042038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_7042038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042038 prefixEnd_7042038 := by exact prefixLift 7042038
  have htrace : WordTrace (prefixWord ++ tailWord_7042038) baseStart_7042038 baseEnd_7042038 := by
    simpa [prefixWord, tailWord_7042038, baseEnd_7042038] using wordTrace_append hprefix tailTrace_7042038
  have hstable : (prefixWord ++ tailWord_7042038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042038).length < 2 ^ (prefixWord ++ tailWord_7042038).sum := by decide
  have hdescent : baseEnd_7042038 < baseStart_7042038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042041 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 1, 2, 3]
def baseStart_7042041 : Nat := 118140960795 + 7042041 * 2 ^ 59
def prefixEnd_7042041 : Nat := 4983230072969 + 3 ^ 40 * 7042041 * 2
def baseEnd_7042041 : Nat := 3615951821668387715901749

theorem tailTrace_7042041 : CollatzResearch.WordTrace tailWord_7042041 prefixEnd_7042041 3615951821668387715901749 := by
  unfold tailWord_7042041
  simp only [CollatzResearch.WordTrace]
  refine ⟨256844335880895616697277977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171229557253930411131518651 256844335880895616697277977)
  ·
    refine ⟨192633251910671712522958483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256844335880895616697277977 192633251910671712522958483)
    ·
      refine ⟨288949877866007568784437725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192633251910671712522958483 288949877866007568784437725)
      ·
        refine ⟨108356204199752838294164147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288949877866007568784437725 108356204199752838294164147)
        ·
          refine ⟨162534306299629257441246221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108356204199752838294164147 162534306299629257441246221)
          ·
            refine ⟨60950364862360971540467333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162534306299629257441246221 60950364862360971540467333)
            ·
              refine ⟨11428193411692682163837625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60950364862360971540467333 11428193411692682163837625)
              ·
                refine ⟨8571145058769511622878219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11428193411692682163837625 8571145058769511622878219)
                ·
                  refine ⟨12856717588154267434317329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8571145058769511622878219 12856717588154267434317329)
                  ·
                    refine ⟨9642538191115700575737997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12856717588154267434317329 9642538191115700575737997)
                    ·
                      refine ⟨3615951821668387715901749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642538191115700575737997 3615951821668387715901749)
                      ·
                        rfl

theorem cell23_7042041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_7042041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042041 prefixEnd_7042041 := by exact prefixLift 7042041
  have htrace : WordTrace (prefixWord ++ tailWord_7042041) baseStart_7042041 baseEnd_7042041 := by
    simpa [prefixWord, tailWord_7042041, baseEnd_7042041] using wordTrace_append hprefix tailTrace_7042041
  have hstable : (prefixWord ++ tailWord_7042041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042041).length < 2 ^ (prefixWord ++ tailWord_7042041).sum := by decide
  have hdescent : baseEnd_7042041 < baseStart_7042041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042044 : List Nat := [2, 2, 2, 1, 2, 3, 4, 7]
def baseStart_7042044 : Nat := 118140960795 + 7042044 * 2 ^ 59
def prefixEnd_7042044 : Nat := 4983230072969 + 3 ^ 40 * 7042044 * 2
def baseEnd_7042044 : Nat := 133924198596679674228305

theorem tailTrace_7042044 : CollatzResearch.WordTrace tailWord_7042044 prefixEnd_7042044 133924198596679674228305 := by
  unfold tailWord_7042044
  simp only [CollatzResearch.WordTrace]
  refine ⟨128422222649942374104818593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171229630199923165473091457 128422222649942374104818593)
  ·
    refine ⟨96316666987456780578613945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128422222649942374104818593 96316666987456780578613945)
    ·
      refine ⟨72237500240592585433960459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96316666987456780578613945 72237500240592585433960459)
      ·
        refine ⟨108356250360888878150940689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72237500240592585433960459 108356250360888878150940689)
        ·
          refine ⟨81267187770666658613205517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108356250360888878150940689 81267187770666658613205517)
          ·
            refine ⟨30475195413999996979952069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81267187770666658613205517 30475195413999996979952069)
            ·
              refine ⟨5714099140124999433741013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30475195413999996979952069 5714099140124999433741013)
              ·
                refine ⟨133924198596679674228305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5714099140124999433741013 133924198596679674228305)
                ·
                  rfl

theorem cell23_7042044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 7].length) (baseStart_7042044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042044 prefixEnd_7042044 := by exact prefixLift 7042044
  have htrace : WordTrace (prefixWord ++ tailWord_7042044) baseStart_7042044 baseEnd_7042044 := by
    simpa [prefixWord, tailWord_7042044, baseEnd_7042044] using wordTrace_append hprefix tailTrace_7042044
  have hstable : (prefixWord ++ tailWord_7042044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042044).length < 2 ^ (prefixWord ++ tailWord_7042044).sum := by decide
  have hdescent : baseEnd_7042044 < baseStart_7042044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042066 : List Nat := [3, 2, 5, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7042066 : Nat := 118140960795 + 7042066 * 2 ^ 59
def prefixEnd_7042066 : Nat := 4983230072969 + 3 ^ 40 * 7042066 * 2
def baseEnd_7042066 : Nat := 3615964658684750118089135

theorem tailTrace_7042066 : CollatzResearch.WordTrace tailWord_7042066 prefixEnd_7042066 3615964658684750118089135 := by
  unfold tailWord_7042066
  simp only [CollatzResearch.WordTrace]
  refine ⟨64211311926451261491734513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171230165137203363977958701 64211311926451261491734513)
  ·
    refine ⟨48158483944838446118800885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64211311926451261491734513 48158483944838446118800885)
    ·
      refine ⟨4514857869828604323637583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48158483944838446118800885 4514857869828604323637583)
      ·
        refine ⟨6772286804742906485456375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514857869828604323637583 6772286804742906485456375)
        ·
          refine ⟨10158430207114359728184563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6772286804742906485456375 10158430207114359728184563)
          ·
            refine ⟨15237645310671539592276845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10158430207114359728184563 15237645310671539592276845)
            ·
              refine ⟨5714116991501827347103817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15237645310671539592276845 5714116991501827347103817)
              ·
                refine ⟨4285587743626370510327863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5714116991501827347103817 4285587743626370510327863)
                ·
                  refine ⟨6428381615439555765491795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285587743626370510327863 6428381615439555765491795)
                  ·
                    refine ⟨9642572423159333648237693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6428381615439555765491795 9642572423159333648237693)
                    ·
                      refine ⟨3615964658684750118089135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642572423159333648237693 3615964658684750118089135)
                      ·
                        rfl

theorem cell23_7042066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7042066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042066 prefixEnd_7042066 := by exact prefixLift 7042066
  have htrace : WordTrace (prefixWord ++ tailWord_7042066) baseStart_7042066 baseEnd_7042066 := by
    simpa [prefixWord, tailWord_7042066, baseEnd_7042066] using wordTrace_append hprefix tailTrace_7042066
  have hstable : (prefixWord ++ tailWord_7042066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042066).length < 2 ^ (prefixWord ++ tailWord_7042066).sum := by decide
  have hdescent : baseEnd_7042066 < baseStart_7042066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042067 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 5]
def baseStart_7042067 : Nat := 118140960795 + 7042067 * 2 ^ 59
def prefixEnd_7042067 : Nat := 4983230072969 + 3 ^ 40 * 7042067 * 2
def baseEnd_7042067 : Nat := 3615965172165404614176629

theorem tailTrace_7042067 : CollatzResearch.WordTrace tailWord_7042067 prefixEnd_7042067 3615965172165404614176629 := by
  unfold tailWord_7042067
  simp only [CollatzResearch.WordTrace]
  refine ⟨256845284178801423137724455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171230189452534282091816303 256845284178801423137724455)
  ·
    refine ⟨385267926268202134706586683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256845284178801423137724455 385267926268202134706586683)
    ·
      refine ⟨577901889402303202059880025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385267926268202134706586683 577901889402303202059880025)
      ·
        refine ⟨433426417051727401544910019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577901889402303202059880025 433426417051727401544910019)
        ·
          refine ⟨650139625577591102317365029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433426417051727401544910019 650139625577591102317365029)
          ·
            refine ⟨121901179795798331684505943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 650139625577591102317365029 121901179795798331684505943)
            ·
              refine ⟨182851769693697497526758915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121901179795798331684505943 182851769693697497526758915)
              ·
                refine ⟨274277654540546246290138373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182851769693697497526758915 274277654540546246290138373)
                ·
                  refine ⟨51427060226352421179400945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274277654540546246290138373 51427060226352421179400945)
                  ·
                    refine ⟨38570295169764315884550709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51427060226352421179400945 38570295169764315884550709)
                    ·
                      refine ⟨3615965172165404614176629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38570295169764315884550709 3615965172165404614176629)
                      ·
                        rfl

theorem cell23_7042067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_7042067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042067 prefixEnd_7042067 := by exact prefixLift 7042067
  have htrace : WordTrace (prefixWord ++ tailWord_7042067) baseStart_7042067 baseEnd_7042067 := by
    simpa [prefixWord, tailWord_7042067, baseEnd_7042067] using wordTrace_append hprefix tailTrace_7042067
  have hstable : (prefixWord ++ tailWord_7042067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042067).length < 2 ^ (prefixWord ++ tailWord_7042067).sum := by decide
  have hdescent : baseEnd_7042067 < baseStart_7042067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042072 : List Nat := [2, 1, 2, 3, 2, 3, 3, 2, 1, 2, 2]
def baseStart_7042072 : Nat := 118140960795 + 7042072 * 2 ^ 59
def prefixEnd_7042072 : Nat := 4983230072969 + 3 ^ 40 * 7042072 * 2
def baseEnd_7042072 : Nat := 3615967739568677094614107

theorem tailTrace_7042072 : CollatzResearch.WordTrace tailWord_7042072 prefixEnd_7042072 3615967739568677094614107 := by
  unfold tailWord_7042072
  simp only [CollatzResearch.WordTrace]
  refine ⟨128422733271891654495828235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171230311029188872661104313 128422733271891654495828235)
  ·
    refine ⟨192634099907837481743742353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128422733271891654495828235 192634099907837481743742353)
    ·
      refine ⟨144475574930878111307806765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192634099907837481743742353 144475574930878111307806765)
      ·
        refine ⟨54178340599079291740427537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144475574930878111307806765 54178340599079291740427537)
        ·
          refine ⟨40633755449309468805320653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54178340599079291740427537 40633755449309468805320653)
          ·
            refine ⟨15237658293491050801995245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40633755449309468805320653 15237658293491050801995245)
            ·
              refine ⟨5714121860059144050748217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15237658293491050801995245 5714121860059144050748217)
              ·
                refine ⟨4285591395044358038061163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5714121860059144050748217 4285591395044358038061163)
                ·
                  refine ⟨6428387092566537057091745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285591395044358038061163 6428387092566537057091745)
                  ·
                    refine ⟨4821290319424902792818809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6428387092566537057091745 4821290319424902792818809)
                    ·
                      refine ⟨3615967739568677094614107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4821290319424902792818809 3615967739568677094614107)
                      ·
                        rfl

theorem cell23_7042072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_7042072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042072 prefixEnd_7042072 := by exact prefixLift 7042072
  have htrace : WordTrace (prefixWord ++ tailWord_7042072) baseStart_7042072 baseEnd_7042072 := by
    simpa [prefixWord, tailWord_7042072, baseEnd_7042072] using wordTrace_append hprefix tailTrace_7042072
  have hstable : (prefixWord ++ tailWord_7042072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042072).length < 2 ^ (prefixWord ++ tailWord_7042072).sum := by decide
  have hdescent : baseEnd_7042072 < baseStart_7042072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042124 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7042124 : Nat := 118140960795 + 7042124 * 2 ^ 59
def prefixEnd_7042124 : Nat := 4983230072969 + 3 ^ 40 * 7042124 * 2
def baseEnd_7042124 : Nat := 3615994440562710891163867

theorem tailTrace_7042124 : CollatzResearch.WordTrace tailWord_7042124 prefixEnd_7042124 3615994440562710891163867 := by
  unfold tailWord_7042124
  simp only [CollatzResearch.WordTrace]
  refine ⟨128423681569797460936274713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171231575426396614581699617 128423681569797460936274713)
  ·
    refine ⟨96317761177348095702206035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128423681569797460936274713 96317761177348095702206035)
    ·
      refine ⟨144476641766022143553309053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96317761177348095702206035 144476641766022143553309053)
      ·
        refine ⟨54178740662258303832490895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144476641766022143553309053 54178740662258303832490895)
        ·
          refine ⟨81268110993387455748736343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54178740662258303832490895 81268110993387455748736343)
          ·
            refine ⟨121902166490081183623104515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81268110993387455748736343 121902166490081183623104515)
            ·
              refine ⟨182853249735121775434656773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121902166490081183623104515 182853249735121775434656773)
              ·
                refine ⟨34284984325335332893998145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182853249735121775434656773 34284984325335332893998145)
                ·
                  refine ⟨25713738244001499670498609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34284984325335332893998145 25713738244001499670498609)
                  ·
                    refine ⟨19285303683001124752873957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25713738244001499670498609 19285303683001124752873957)
                    ·
                      refine ⟨3615994440562710891163867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19285303683001124752873957 3615994440562710891163867)
                      ·
                        rfl

theorem cell23_7042124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7042124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042124 prefixEnd_7042124 := by exact prefixLift 7042124
  have htrace : WordTrace (prefixWord ++ tailWord_7042124) baseStart_7042124 baseEnd_7042124 := by
    simpa [prefixWord, tailWord_7042124, baseEnd_7042124] using wordTrace_append hprefix tailTrace_7042124
  have hstable : (prefixWord ++ tailWord_7042124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042124).length < 2 ^ (prefixWord ++ tailWord_7042124).sum := by decide
  have hdescent : baseEnd_7042124 < baseStart_7042124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042218 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7042218 : Nat := 118140960795 + 7042218 * 2 ^ 59
def prefixEnd_7042218 : Nat := 4983230072969 + 3 ^ 40 * 7042218 * 2
def baseEnd_7042218 : Nat := 3616042707744233523388435

theorem tailTrace_7042218 : CollatzResearch.WordTrace tailWord_7042218 prefixEnd_7042218 3616042707744233523388435 := by
  unfold tailWord_7042218
  simp only [CollatzResearch.WordTrace]
  refine ⟨64212697900313593981617827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171233861067502917284314205 64212697900313593981617827)
  ·
    refine ⟨96319046850470390972426741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64212697900313593981617827 96319046850470390972426741)
    ·
      refine ⟨9029910642231599153665007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96319046850470390972426741 9029910642231599153665007)
      ·
        refine ⟨13544865963347398730497511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9029910642231599153665007 13544865963347398730497511)
        ·
          refine ⟨20317298945021098095746267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13544865963347398730497511 20317298945021098095746267)
          ·
            refine ⟨30475948417531647143619401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20317298945021098095746267 30475948417531647143619401)
            ·
              refine ⟨22856961313148735357714551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30475948417531647143619401 22856961313148735357714551)
              ·
                refine ⟨34285441969723103036571827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22856961313148735357714551 34285441969723103036571827)
                ·
                  refine ⟨51428162954584654554857741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34285441969723103036571827 51428162954584654554857741)
                  ·
                    refine ⟨19285561107969245458071653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51428162954584654554857741 19285561107969245458071653)
                    ·
                      refine ⟨3616042707744233523388435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19285561107969245458071653 3616042707744233523388435)
                      ·
                        rfl

theorem cell23_7042218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7042218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042218 prefixEnd_7042218 := by exact prefixLift 7042218
  have htrace : WordTrace (prefixWord ++ tailWord_7042218) baseStart_7042218 baseEnd_7042218 := by
    simpa [prefixWord, tailWord_7042218, baseEnd_7042218] using wordTrace_append hprefix tailTrace_7042218
  have hstable : (prefixWord ++ tailWord_7042218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042218).length < 2 ^ (prefixWord ++ tailWord_7042218).sum := by decide
  have hdescent : baseEnd_7042218 < baseStart_7042218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042238 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_7042238 : Nat := 118140960795 + 7042238 * 2 ^ 59
def prefixEnd_7042238 : Nat := 4983230072969 + 3 ^ 40 * 7042238 * 2
def baseEnd_7042238 : Nat := 3616052977357323445138343

theorem tailTrace_7042238 : CollatzResearch.WordTrace tailWord_7042238 prefixEnd_7042238 3616052977357323445138343 := by
  unfold tailWord_7042238
  simp only [CollatzResearch.WordTrace]
  refine ⟨32106440132647739917774921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171234347374121279561466245 32106440132647739917774921)
  ·
    refine ⟨24079830099485804938331191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32106440132647739917774921 24079830099485804938331191)
    ·
      refine ⟨36119745149228707407496787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24079830099485804938331191 36119745149228707407496787)
      ·
        refine ⟨54179617723843061111245181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36119745149228707407496787 54179617723843061111245181)
        ·
          refine ⟨20317356646441147916716943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54179617723843061111245181 20317356646441147916716943)
          ·
            refine ⟨30476034969661721875075415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20317356646441147916716943 30476034969661721875075415)
            ·
              refine ⟨45714052454492582812613123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30476034969661721875075415 45714052454492582812613123)
              ·
                refine ⟨68571078681738874218919685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45714052454492582812613123 68571078681738874218919685)
                ·
                  refine ⟨12857077252826038916047441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68571078681738874218919685 12857077252826038916047441)
                  ·
                    refine ⟨9642807939619529187035581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12857077252826038916047441 9642807939619529187035581)
                    ·
                      refine ⟨3616052977357323445138343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642807939619529187035581 3616052977357323445138343)
                      ·
                        rfl

theorem cell23_7042238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_7042238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042238 prefixEnd_7042238 := by exact prefixLift 7042238
  have htrace : WordTrace (prefixWord ++ tailWord_7042238) baseStart_7042238 baseEnd_7042238 := by
    simpa [prefixWord, tailWord_7042238, baseEnd_7042238] using wordTrace_append hprefix tailTrace_7042238
  have hstable : (prefixWord ++ tailWord_7042238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042238).length < 2 ^ (prefixWord ++ tailWord_7042238).sum := by decide
  have hdescent : baseEnd_7042238 < baseStart_7042238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042308 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_7042308 : Nat := 118140960795 + 7042308 * 2 ^ 59
def prefixEnd_7042308 : Nat := 4983230072969 + 3 ^ 40 * 7042308 * 2
def baseEnd_7042308 : Nat := 3616088921003138171263021

theorem tailTrace_7042308 : CollatzResearch.WordTrace tailWord_7042308 prefixEnd_7042308 3616088921003138171263021 := by
  unfold tailWord_7042308
  simp only [CollatzResearch.WordTrace]
  refine ⟨128427037085464160648623789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171236049447285547531498385 128427037085464160648623789)
  ·
    refine ⟨48160138907049060243233921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128427037085464160648623789 48160138907049060243233921)
    ·
      refine ⟨36120104180286795182425441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48160138907049060243233921 36120104180286795182425441)
      ·
        refine ⟨27090078135215096386819081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36120104180286795182425441 27090078135215096386819081)
        ·
          refine ⟨20317558601411322290114311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27090078135215096386819081 20317558601411322290114311)
          ·
            refine ⟨30476337902116983435171467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20317558601411322290114311 30476337902116983435171467)
            ·
              refine ⟨45714506853175475152757201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30476337902116983435171467 45714506853175475152757201)
              ·
                refine ⟨34285880139881606364567901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45714506853175475152757201 34285880139881606364567901)
                ·
                  refine ⟨12857205052455602386712963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34285880139881606364567901 12857205052455602386712963)
                  ·
                    refine ⟨19285807578683403580069445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12857205052455602386712963 19285807578683403580069445)
                    ·
                      refine ⟨3616088921003138171263021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19285807578683403580069445 3616088921003138171263021)
                      ·
                        rfl

theorem cell23_7042308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_7042308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042308 prefixEnd_7042308 := by exact prefixLift 7042308
  have htrace : WordTrace (prefixWord ++ tailWord_7042308) baseStart_7042308 baseEnd_7042308 := by
    simpa [prefixWord, tailWord_7042308, baseEnd_7042308] using wordTrace_append hprefix tailTrace_7042308
  have hstable : (prefixWord ++ tailWord_7042308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042308).length < 2 ^ (prefixWord ++ tailWord_7042308).sum := by decide
  have hdescent : baseEnd_7042308 < baseStart_7042308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042318 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_7042318 : Nat := 118140960795 + 7042318 * 2 ^ 59
def prefixEnd_7042318 : Nat := 4983230072969 + 3 ^ 40 * 7042318 * 2
def baseEnd_7042318 : Nat := 1205364685269894377379325

theorem tailTrace_7042318 : CollatzResearch.WordTrace tailWord_7042318 prefixEnd_7042318 1205364685269894377379325 := by
  unfold tailWord_7042318
  simp only [CollatzResearch.WordTrace]
  refine ⟨32106804862611511625638951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171236292600594728670074405 32106804862611511625638951)
  ·
    refine ⟨48160207293917267438458427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32106804862611511625638951 48160207293917267438458427)
    ·
      refine ⟨72240310940875901157687641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48160207293917267438458427 72240310940875901157687641)
      ·
        refine ⟨54180233205656925868265731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72240310940875901157687641 54180233205656925868265731)
        ·
          refine ⟨81270349808485388802398597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54180233205656925868265731 81270349808485388802398597)
          ·
            refine ⟨15238190589091010400449737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81270349808485388802398597 15238190589091010400449737)
            ·
              refine ⟨11428642941818257800337303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15238190589091010400449737 11428642941818257800337303)
              ·
                refine ⟨17142964412727386700505955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11428642941818257800337303 17142964412727386700505955)
                ·
                  refine ⟨25714446619091080050758933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17142964412727386700505955 25714446619091080050758933)
                  ·
                    refine ⟨1205364685269894377379325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25714446619091080050758933 1205364685269894377379325)
                    ·
                      rfl

theorem cell23_7042318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_7042318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042318 prefixEnd_7042318 := by exact prefixLift 7042318
  have htrace : WordTrace (prefixWord ++ tailWord_7042318) baseStart_7042318 baseEnd_7042318 := by
    simpa [prefixWord, tailWord_7042318, baseEnd_7042318] using wordTrace_append hprefix tailTrace_7042318
  have hstable : (prefixWord ++ tailWord_7042318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042318).length < 2 ^ (prefixWord ++ tailWord_7042318).sum := by decide
  have hdescent : baseEnd_7042318 < baseStart_7042318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042328 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 3, 2, 3]
def baseStart_7042328 : Nat := 118140960795 + 7042328 * 2 ^ 59
def prefixEnd_7042328 : Nat := 4983230072969 + 3 ^ 40 * 7042328 * 2
def baseEnd_7042328 : Nat := 3616099190616228093012929

theorem tailTrace_7042328 : CollatzResearch.WordTrace tailWord_7042328 prefixEnd_7042328 3616099190616228093012929 := by
  unfold tailWord_7042328
  simp only [CollatzResearch.WordTrace]
  refine ⟨128427401815427932356487819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171236535753903909808650425 128427401815427932356487819)
  ·
    refine ⟨192641102723141898534731729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128427401815427932356487819 192641102723141898534731729)
    ·
      refine ⟨144480827042356423901048797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192641102723141898534731729 144480827042356423901048797)
      ·
        refine ⟨54180310140883658962893299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144480827042356423901048797 54180310140883658962893299)
        ·
          refine ⟨81270465211325488444339949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54180310140883658962893299 81270465211325488444339949)
          ·
            refine ⟨30476424454247058166627481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81270465211325488444339949 30476424454247058166627481)
            ·
              refine ⟨22857318340685293624970611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30476424454247058166627481 22857318340685293624970611)
              ·
                refine ⟨34285977511027940437455917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22857318340685293624970611 34285977511027940437455917)
                ·
                  refine ⟨12857241566635477664045969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34285977511027940437455917 12857241566635477664045969)
                  ·
                    refine ⟨9642931174976608248034477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12857241566635477664045969 9642931174976608248034477)
                    ·
                      refine ⟨3616099190616228093012929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642931174976608248034477 3616099190616228093012929)
                      ·
                        rfl

theorem cell23_7042328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_7042328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042328 prefixEnd_7042328 := by exact prefixLift 7042328
  have htrace : WordTrace (prefixWord ++ tailWord_7042328) baseStart_7042328 baseEnd_7042328 := by
    simpa [prefixWord, tailWord_7042328, baseEnd_7042328] using wordTrace_append hprefix tailTrace_7042328
  have hstable : (prefixWord ++ tailWord_7042328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042328).length < 2 ^ (prefixWord ++ tailWord_7042328).sum := by decide
  have hdescent : baseEnd_7042328 < baseStart_7042328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042372 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_7042372 : Nat := 118140960795 + 7042372 * 2 ^ 59
def prefixEnd_7042372 : Nat := 4983230072969 + 3 ^ 40 * 7042372 * 2
def baseEnd_7042372 : Nat := 3616121783765025920862727

theorem tailTrace_7042372 : CollatzResearch.WordTrace tailWord_7042372 prefixEnd_7042372 3616121783765025920862727 := by
  unfold tailWord_7042372
  simp only [CollatzResearch.WordTrace]
  refine ⟨128428204221348230113788685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171237605628464306818384913 128428204221348230113788685)
  ·
    refine ⟨48160576583005586292670757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128428204221348230113788685 48160576583005586292670757)
    ·
      refine ⟨9030108109313547429875767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48160576583005586292670757 9030108109313547429875767)
      ·
        refine ⟨13545162163970321144813651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9030108109313547429875767 13545162163970321144813651)
        ·
          refine ⟨20317743245955481717220477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13545162163970321144813651 20317743245955481717220477)
          ·
            refine ⟨7619153717233305643957679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20317743245955481717220477 7619153717233305643957679)
            ·
              refine ⟨11428730575849958465936519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7619153717233305643957679 11428730575849958465936519)
              ·
                refine ⟨17143095863774937698904779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11428730575849958465936519 17143095863774937698904779)
                ·
                  refine ⟨25714643795662406548357169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17143095863774937698904779 25714643795662406548357169)
                  ·
                    refine ⟨19285982846746804911267877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25714643795662406548357169 19285982846746804911267877)
                    ·
                      refine ⟨3616121783765025920862727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19285982846746804911267877 3616121783765025920862727)
                      ·
                        rfl

theorem cell23_7042372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_7042372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042372 prefixEnd_7042372 := by exact prefixLift 7042372
  have htrace : WordTrace (prefixWord ++ tailWord_7042372) baseStart_7042372 baseEnd_7042372 := by
    simpa [prefixWord, tailWord_7042372, baseEnd_7042372] using wordTrace_append hprefix tailTrace_7042372
  have hstable : (prefixWord ++ tailWord_7042372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042372).length < 2 ^ (prefixWord ++ tailWord_7042372).sum := by decide
  have hdescent : baseEnd_7042372 < baseStart_7042372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042375 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_7042375 : Nat := 118140960795 + 7042375 * 2 ^ 59
def prefixEnd_7042375 : Nat := 4983230072969 + 3 ^ 40 * 7042375 * 2
def baseEnd_7042375 : Nat := 3616123324206989409125213

theorem tailTrace_7042375 : CollatzResearch.WordTrace tailWord_7042375 prefixEnd_7042375 3616123324206989409125213 := by
  unfold tailWord_7042375
  simp only [CollatzResearch.WordTrace]
  refine ⟨256856517861685591739936579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171237678574457061159957719 256856517861685591739936579)
  ·
    refine ⟨385284776792528387609904869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256856517861685591739936579 385284776792528387609904869)
    ·
      refine ⟨72240895648599072676857163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385284776792528387609904869 72240895648599072676857163)
      ·
        refine ⟨108361343472898609015285745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72240895648599072676857163 108361343472898609015285745)
        ·
          refine ⟨81271007604673956761464309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108361343472898609015285745 81271007604673956761464309)
          ·
            refine ⟨7619156962938183446387279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81271007604673956761464309 7619156962938183446387279)
            ·
              refine ⟨11428735444407275169580919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7619156962938183446387279 11428735444407275169580919)
              ·
                refine ⟨17143103166610912754371379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11428735444407275169580919 17143103166610912754371379)
                ·
                  refine ⟨25714654749916369131557069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17143103166610912754371379 25714654749916369131557069)
                  ·
                    refine ⟨9642995531218638424333901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25714654749916369131557069 9642995531218638424333901)
                    ·
                      refine ⟨3616123324206989409125213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9642995531218638424333901 3616123324206989409125213)
                      ·
                        rfl

theorem cell23_7042375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_7042375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042375 prefixEnd_7042375 := by exact prefixLift 7042375
  have htrace : WordTrace (prefixWord ++ tailWord_7042375) baseStart_7042375 baseEnd_7042375 := by
    simpa [prefixWord, tailWord_7042375, baseEnd_7042375] using wordTrace_append hprefix tailTrace_7042375
  have hstable : (prefixWord ++ tailWord_7042375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042375).length < 2 ^ (prefixWord ++ tailWord_7042375).sum := by decide
  have hdescent : baseEnd_7042375 < baseStart_7042375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042402 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_7042402 : Nat := 118140960795 + 7042402 * 2 ^ 59
def prefixEnd_7042402 : Nat := 4983230072969 + 3 ^ 40 * 7042402 * 2
def baseEnd_7042402 : Nat := 3616137188184660803487589

theorem tailTrace_7042402 : CollatzResearch.WordTrace tailWord_7042402 prefixEnd_7042402 3616137188184660803487589 := by
  unfold tailWord_7042402
  simp only [CollatzResearch.WordTrace]
  refine ⟨64214375658146943837792365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171238335088391850234112973 64214375658146943837792365)
  ·
    refine ⟨24080390871805103939172137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64214375658146943837792365 24080390871805103939172137)
    ·
      refine ⟨18060293153853827954379103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24080390871805103939172137 18060293153853827954379103)
      ·
        refine ⟨27090439730780741931568655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18060293153853827954379103 27090439730780741931568655)
        ·
          refine ⟨40635659596171112897352983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27090439730780741931568655 40635659596171112897352983)
          ·
            refine ⟨60953489394256669346029475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40635659596171112897352983 60953489394256669346029475)
            ·
              refine ⟨91430234091385004019044213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60953489394256669346029475 91430234091385004019044213)
              ·
                refine ⟨8571584446067344126785395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91430234091385004019044213 8571584446067344126785395)
                ·
                  refine ⟨12857376669101016190178093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8571584446067344126785395 12857376669101016190178093)
                  ·
                    refine ⟨4821516250912881071316785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12857376669101016190178093 4821516250912881071316785)
                    ·
                      refine ⟨3616137188184660803487589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4821516250912881071316785 3616137188184660803487589)
                      ·
                        rfl

theorem cell23_7042402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_7042402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042402 prefixEnd_7042402 := by exact prefixLift 7042402
  have htrace : WordTrace (prefixWord ++ tailWord_7042402) baseStart_7042402 baseEnd_7042402 := by
    simpa [prefixWord, tailWord_7042402, baseEnd_7042402] using wordTrace_append hprefix tailTrace_7042402
  have hstable : (prefixWord ++ tailWord_7042402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042402).length < 2 ^ (prefixWord ++ tailWord_7042402).sum := by decide
  have hdescent : baseEnd_7042402 < baseStart_7042402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042415 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 4, 2, 2]
def baseStart_7042415 : Nat := 118140960795 + 7042415 * 2 ^ 59
def prefixEnd_7042415 : Nat := 4983230072969 + 3 ^ 40 * 7042415 * 2
def baseEnd_7042415 : Nat := 3616143863433169252625029

theorem tailTrace_7042415 : CollatzResearch.WordTrace tailWord_7042415 prefixEnd_7042415 3616143863433169252625029 := by
  unfold tailWord_7042415
  simp only [CollatzResearch.WordTrace]
  refine ⟨256857976781540678571392699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171238651187693785714261799 256857976781540678571392699)
  ·
    refine ⟨385286965172311017857089049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256857976781540678571392699 385286965172311017857089049)
    ·
      refine ⟨288965223879233263392816787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385286965172311017857089049 288965223879233263392816787)
      ·
        refine ⟨433447835818849895089225181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288965223879233263392816787 433447835818849895089225181)
        ·
          refine ⟨162542938432068710658459443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433447835818849895089225181 162542938432068710658459443)
          ·
            refine ⟨243814407648103065987689165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162542938432068710658459443 243814407648103065987689165)
            ·
              refine ⟨91430402868038649745383437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243814407648103065987689165 91430402868038649745383437)
              ·
                refine ⟨34286401075514493654518789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91430402868038649745383437 34286401075514493654518789)
                ·
                  refine ⟨6428700201658967560222273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34286401075514493654518789 6428700201658967560222273)
                  ·
                    refine ⟨4821525151244225670166705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6428700201658967560222273 4821525151244225670166705)
                    ·
                      refine ⟨3616143863433169252625029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4821525151244225670166705 3616143863433169252625029)
                      ·
                        rfl

theorem cell23_7042415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 2, 2].length) (baseStart_7042415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042415 prefixEnd_7042415 := by exact prefixLift 7042415
  have htrace : WordTrace (prefixWord ++ tailWord_7042415) baseStart_7042415 baseEnd_7042415 := by
    simpa [prefixWord, tailWord_7042415, baseEnd_7042415] using wordTrace_append hprefix tailTrace_7042415
  have hstable : (prefixWord ++ tailWord_7042415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042415).length < 2 ^ (prefixWord ++ tailWord_7042415).sum := by decide
  have hdescent : baseEnd_7042415 < baseStart_7042415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042418 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_7042418 : Nat := 118140960795 + 7042418 * 2 ^ 59
def prefixEnd_7042418 : Nat := 4983230072969 + 3 ^ 40 * 7042418 * 2
def baseEnd_7042418 : Nat := 3616145403875132740887515

theorem tailTrace_7042418 : CollatzResearch.WordTrace tailWord_7042418 prefixEnd_7042418 3616145403875132740887515 := by
  unfold tailWord_7042418
  simp only [CollatzResearch.WordTrace]
  refine ⟨64214521550132452520937977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171238724133686540055834605 64214521550132452520937977)
  ·
    refine ⟨48160891162599339390703483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64214521550132452520937977 48160891162599339390703483)
    ·
      refine ⟨72241336743899009086055225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48160891162599339390703483 72241336743899009086055225)
      ·
        refine ⟨54181002557924256814541419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72241336743899009086055225 54181002557924256814541419)
        ·
          refine ⟨81271503836886385221812129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54181002557924256814541419 81271503836886385221812129)
          ·
            refine ⟨60953627877664788916359097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81271503836886385221812129 60953627877664788916359097)
            ·
              refine ⟨45715220908248591687269323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60953627877664788916359097 45715220908248591687269323)
              ·
                refine ⟨68572831362372887530903985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45715220908248591687269323 68572831362372887530903985)
                ·
                  refine ⟨51429623521779665648177989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68572831362372887530903985 51429623521779665648177989)
                  ·
                    refine ⟨9643054410333687309033373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51429623521779665648177989 9643054410333687309033373)
                    ·
                      refine ⟨3616145403875132740887515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9643054410333687309033373 3616145403875132740887515)
                      ·
                        rfl

theorem cell23_7042418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_7042418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042418 prefixEnd_7042418 := by exact prefixLift 7042418
  have htrace : WordTrace (prefixWord ++ tailWord_7042418) baseStart_7042418 baseEnd_7042418 := by
    simpa [prefixWord, tailWord_7042418, baseEnd_7042418] using wordTrace_append hprefix tailTrace_7042418
  have hstable : (prefixWord ++ tailWord_7042418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042418).length < 2 ^ (prefixWord ++ tailWord_7042418).sum := by decide
  have hdescent : baseEnd_7042418 < baseStart_7042418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042488 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_7042488 : Nat := 118140960795 + 7042488 * 2 ^ 59
def prefixEnd_7042488 : Nat := 4983230072969 + 3 ^ 40 * 7042488 * 2
def baseEnd_7042488 : Nat := 3616181347520947467012193

theorem tailTrace_7042488 : CollatzResearch.WordTrace tailWord_7042488 prefixEnd_7042488 3616181347520947467012193 := by
  unfold tailWord_7042488
  simp only [CollatzResearch.WordTrace]
  refine ⟨128430319655138106019400059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171240426206850808025866745 128430319655138106019400059)
  ·
    refine ⟨192645479482707159029100089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128430319655138106019400059 192645479482707159029100089)
    ·
      refine ⟨144484109612030369271825067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192645479482707159029100089 144484109612030369271825067)
      ·
        refine ⟨216726164418045553907737601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144484109612030369271825067 216726164418045553907737601)
        ·
          refine ⟨162544623313534165430803201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216726164418045553907737601 162544623313534165430803201)
          ·
            refine ⟨121908467485150624073102401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162544623313534165430803201 121908467485150624073102401)
            ·
              refine ⟨91431350613862968054826801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121908467485150624073102401 91431350613862968054826801)
              ·
                refine ⟨68573512960397226041120101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91431350613862968054826801 68573512960397226041120101)
                ·
                  refine ⟨12857533680074479882710019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68573512960397226041120101 12857533680074479882710019)
                  ·
                    refine ⟨19286300520111719824065029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12857533680074479882710019 19286300520111719824065029)
                    ·
                      refine ⟨3616181347520947467012193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19286300520111719824065029 3616181347520947467012193)
                      ·
                        rfl

theorem cell23_7042488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_7042488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042488 prefixEnd_7042488 := by exact prefixLift 7042488
  have htrace : WordTrace (prefixWord ++ tailWord_7042488) baseStart_7042488 baseEnd_7042488 := by
    simpa [prefixWord, tailWord_7042488, baseEnd_7042488] using wordTrace_append hprefix tailTrace_7042488
  have hstable : (prefixWord ++ tailWord_7042488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042488).length < 2 ^ (prefixWord ++ tailWord_7042488).sum := by decide
  have hdescent : baseEnd_7042488 < baseStart_7042488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042528 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 6]
def baseStart_7042528 : Nat := 118140960795 + 7042528 * 2 ^ 59
def prefixEnd_7042528 : Nat := 4983230072969 + 3 ^ 40 * 7042528 * 2
def baseEnd_7042528 : Nat := 401800209638569701168001

theorem tailTrace_7042528 : CollatzResearch.WordTrace tailWord_7042528 prefixEnd_7042528 401800209638569701168001 := by
  unfold tailWord_7042528
  simp only [CollatzResearch.WordTrace]
  refine ⟨128431049115065649435128119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171241398820087532580170825 128431049115065649435128119)
  ·
    refine ⟨192646573672598474152692179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128431049115065649435128119 192646573672598474152692179)
    ·
      refine ⟨288969860508897711229038269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192646573672598474152692179 288969860508897711229038269)
      ·
        refine ⟨108363697690836641710889351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288969860508897711229038269 108363697690836641710889351)
        ·
          refine ⟨162545546536254962566334027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108363697690836641710889351 162545546536254962566334027)
          ·
            refine ⟨243818319804382443849501041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162545546536254962566334027 243818319804382443849501041)
            ·
              refine ⟨182863739853286832887125781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243818319804382443849501041 182863739853286832887125781)
              ·
                refine ⟨8571737805622820291584021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182863739853286832887125781 8571737805622820291584021)
                ·
                  refine ⟨401800209638569701168001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8571737805622820291584021 401800209638569701168001)
                  ·
                    rfl

theorem cell23_7042528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 6].length) (baseStart_7042528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042528 prefixEnd_7042528 := by exact prefixLift 7042528
  have htrace : WordTrace (prefixWord ++ tailWord_7042528) baseStart_7042528 baseEnd_7042528 := by
    simpa [prefixWord, tailWord_7042528, baseEnd_7042528] using wordTrace_append hprefix tailTrace_7042528
  have hstable : (prefixWord ++ tailWord_7042528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042528).length < 2 ^ (prefixWord ++ tailWord_7042528).sum := by decide
  have hdescent : baseEnd_7042528 < baseStart_7042528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042618 : List Nat := [3, 1, 1, 1, 3, 2, 1, 11]
def baseStart_7042618 : Nat := 118140960795 + 7042618 * 2 ^ 59
def prefixEnd_7042618 : Nat := 4983230072969 + 3 ^ 40 * 7042618 * 2
def baseEnd_7042618 : Nat := 133935114815038220680985

theorem tailTrace_7042618 : CollatzResearch.WordTrace tailWord_7042618 prefixEnd_7042618 133935114815038220680985 := by
  unfold tailWord_7042618
  simp only [CollatzResearch.WordTrace]
  refine ⟨64216345199951311060258127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171243587199870162827355005 64216345199951311060258127)
  ·
    refine ⟨96324517799926966590387191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64216345199951311060258127 96324517799926966590387191)
    ·
      refine ⟨144486776699890449885580787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96324517799926966590387191 144486776699890449885580787)
      ·
        refine ⟨216730165049835674828371181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144486776699890449885580787 216730165049835674828371181)
        ·
          refine ⟨81273811893688378060639193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216730165049835674828371181 81273811893688378060639193)
          ·
            refine ⟨60955358920266283545479395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81273811893688378060639193 60955358920266283545479395)
            ·
              refine ⟨91433038380399425318219093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60955358920266283545479395 91433038380399425318219093)
              ·
                refine ⟨133935114815038220680985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 91433038380399425318219093 133935114815038220680985)
                ·
                  rfl

theorem cell23_7042618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 11].length) (baseStart_7042618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042618 prefixEnd_7042618 := by exact prefixLift 7042618
  have htrace : WordTrace (prefixWord ++ tailWord_7042618) baseStart_7042618 baseEnd_7042618 := by
    simpa [prefixWord, tailWord_7042618, baseEnd_7042618] using wordTrace_append hprefix tailTrace_7042618
  have hstable : (prefixWord ++ tailWord_7042618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042618).length < 2 ^ (prefixWord ++ tailWord_7042618).sum := by decide
  have hdescent : baseEnd_7042618 < baseStart_7042618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042645 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_7042645 : Nat := 118140960795 + 7042645 * 2 ^ 59
def prefixEnd_7042645 : Nat := 4983230072969 + 3 ^ 40 * 7042645 * 2
def baseEnd_7042645 : Nat := 3616261963983703352748971

theorem tailTrace_7042645 : CollatzResearch.WordTrace tailWord_7042645 prefixEnd_7042645 3616261963983703352748971 := by
  unfold tailWord_7042645
  simp only [CollatzResearch.WordTrace]
  refine ⟨256866365570707427852265389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171244243713804951901510259 256866365570707427852265389)
  ·
    refine ⟨96324887089015285444599521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256866365570707427852265389 96324887089015285444599521)
    ·
      refine ⟨72243665316761464083449641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96324887089015285444599521 72243665316761464083449641)
      ·
        refine ⟨54182748987571098062587231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72243665316761464083449641 54182748987571098062587231)
        ·
          refine ⟨81274123481356647093880847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54182748987571098062587231 81274123481356647093880847)
          ·
            refine ⟨121911185222034970640821271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81274123481356647093880847 121911185222034970640821271)
            ·
              refine ⟨182866777833052455961231907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121911185222034970640821271 182866777833052455961231907)
              ·
                refine ⟨274300166749578683941847861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182866777833052455961231907 274300166749578683941847861)
                ·
                  refine ⟨25715640632773001619548237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274300166749578683941847861 25715640632773001619548237)
                  ·
                    refine ⟨9643365237289875607330589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25715640632773001619548237 9643365237289875607330589)
                    ·
                      refine ⟨3616261963983703352748971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9643365237289875607330589 3616261963983703352748971)
                      ·
                        rfl

theorem cell23_7042645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_7042645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042645 prefixEnd_7042645 := by exact prefixLift 7042645
  have htrace : WordTrace (prefixWord ++ tailWord_7042645) baseStart_7042645 baseEnd_7042645 := by
    simpa [prefixWord, tailWord_7042645, baseEnd_7042645] using wordTrace_append hprefix tailTrace_7042645
  have hstable : (prefixWord ++ tailWord_7042645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042645).length < 2 ^ (prefixWord ++ tailWord_7042645).sum := by decide
  have hdescent : baseEnd_7042645 < baseStart_7042645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042652 : List Nat := [2, 2, 4, 1, 2, 3, 1, 8]
def baseStart_7042652 : Nat := 118140960795 + 7042652 * 2 ^ 59
def prefixEnd_7042652 : Nat := 4983230072969 + 3 ^ 40 * 7042652 * 2
def baseEnd_7042652 : Nat := 133935761420306845383757

theorem tailTrace_7042652 : CollatzResearch.WordTrace tailWord_7042652 prefixEnd_7042652 133935761420306845383757 := by
  unfold tailWord_7042652
  simp only [CollatzResearch.WordTrace]
  refine ⟨128433310440841034023885105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171244413921121378698513473 128433310440841034023885105)
  ·
    refine ⟨96324982830630775517913829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128433310440841034023885105 96324982830630775517913829)
    ·
      refine ⟨18060934280743270409608843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96324982830630775517913829 18060934280743270409608843)
      ·
        refine ⟨27091401421114905614413265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18060934280743270409608843 27091401421114905614413265)
        ·
          refine ⟨20318551065836179210809949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27091401421114905614413265 20318551065836179210809949)
          ·
            refine ⟨7619456649688567204053731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20318551065836179210809949 7619456649688567204053731)
            ·
              refine ⟨11429184974532850806080597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7619456649688567204053731 11429184974532850806080597)
              ·
                refine ⟨133935761420306845383757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11429184974532850806080597 133935761420306845383757)
                ·
                  rfl

theorem cell23_7042652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 8].length) (baseStart_7042652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042652 prefixEnd_7042652 := by exact prefixLift 7042652
  have htrace : WordTrace (prefixWord ++ tailWord_7042652) baseStart_7042652 baseEnd_7042652 := by
    simpa [prefixWord, tailWord_7042652, baseEnd_7042652] using wordTrace_append hprefix tailTrace_7042652
  have hstable : (prefixWord ++ tailWord_7042652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042652).length < 2 ^ (prefixWord ++ tailWord_7042652).sum := by decide
  have hdescent : baseEnd_7042652 < baseStart_7042652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042695 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 2, 6]
def baseStart_7042695 : Nat := 118140960795 + 7042695 * 2 ^ 59
def prefixEnd_7042695 : Nat := 4983230072969 + 3 ^ 40 * 7042695 * 2
def baseEnd_7042695 : Nat := 1205429212672142719041247

theorem tailTrace_7042695 : CollatzResearch.WordTrace tailWord_7042695 prefixEnd_7042695 1205429212672142719041247 := by
  unfold tailWord_7042695
  simp only [CollatzResearch.WordTrace]
  refine ⟨256868189220526286391585539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171245459480350857594390359 256868189220526286391585539)
  ·
    refine ⟨385302283830789429587378309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256868189220526286391585539 385302283830789429587378309)
    ·
      refine ⟨72244178218273018047633433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385302283830789429587378309 72244178218273018047633433)
      ·
        refine ⟨54183133663704763535725075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72244178218273018047633433 54183133663704763535725075)
        ·
          refine ⟨81274700495557145303587613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54183133663704763535725075 81274700495557145303587613)
          ·
            refine ⟨30478012685833929488845355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81274700495557145303587613 30478012685833929488845355)
            ·
              refine ⟨45717019028750894233268033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30478012685833929488845355 45717019028750894233268033)
              ·
                refine ⟨34287764271563170674951025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45717019028750894233268033 34287764271563170674951025)
                ·
                  refine ⟨25715823203672378006213269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34287764271563170674951025 25715823203672378006213269)
                  ·
                    refine ⟨1205429212672142719041247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25715823203672378006213269 1205429212672142719041247)
                    ·
                      rfl

theorem cell23_7042695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_7042695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042695 prefixEnd_7042695 := by exact prefixLift 7042695
  have htrace : WordTrace (prefixWord ++ tailWord_7042695) baseStart_7042695 baseEnd_7042695 := by
    simpa [prefixWord, tailWord_7042695, baseEnd_7042695] using wordTrace_append hprefix tailTrace_7042695
  have hstable : (prefixWord ++ tailWord_7042695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042695).length < 2 ^ (prefixWord ++ tailWord_7042695).sum := by decide
  have hdescent : baseEnd_7042695 < baseStart_7042695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042696 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7042696 : Nat := 118140960795 + 7042696 * 2 ^ 59
def prefixEnd_7042696 : Nat := 4983230072969 + 3 ^ 40 * 7042696 * 2
def baseEnd_7042696 : Nat := 3616288151497082653211237

theorem tailTrace_7042696 : CollatzResearch.WordTrace tailWord_7042696 prefixEnd_7042696 3616288151497082653211237 := by
  unfold tailWord_7042696
  simp only [CollatzResearch.WordTrace]
  refine ⟨128434112846761331781185971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171245483795681775708247961 128434112846761331781185971)
  ·
    refine ⟨192651169270141997671778957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128434112846761331781185971 192651169270141997671778957)
    ·
      refine ⟨72244188476303249126917109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192651169270141997671778957 72244188476303249126917109)
      ·
        refine ⟨6772892669653429605648479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72244188476303249126917109 6772892669653429605648479)
        ·
          refine ⟨10159339004480144408472719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6772892669653429605648479 10159339004480144408472719)
          ·
            refine ⟨15239008506720216612709079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159339004480144408472719 15239008506720216612709079)
            ·
              refine ⟨22858512760080324919063619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15239008506720216612709079 22858512760080324919063619)
              ·
                refine ⟨34287769140120487378595429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22858512760080324919063619 34287769140120487378595429)
                ·
                  refine ⟨6428956713772591383486643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34287769140120487378595429 6428956713772591383486643)
                  ·
                    refine ⟨9643435070658887075229965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6428956713772591383486643 9643435070658887075229965)
                    ·
                      refine ⟨3616288151497082653211237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9643435070658887075229965 3616288151497082653211237)
                      ·
                        rfl

theorem cell23_7042696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7042696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042696 prefixEnd_7042696 := by exact prefixLift 7042696
  have htrace : WordTrace (prefixWord ++ tailWord_7042696) baseStart_7042696 baseEnd_7042696 := by
    simpa [prefixWord, tailWord_7042696, baseEnd_7042696] using wordTrace_append hprefix tailTrace_7042696
  have hstable : (prefixWord ++ tailWord_7042696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042696).length < 2 ^ (prefixWord ++ tailWord_7042696).sum := by decide
  have hdescent : baseEnd_7042696 < baseStart_7042696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042705 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 3]
def baseStart_7042705 : Nat := 118140960795 + 7042705 * 2 ^ 59
def prefixEnd_7042705 : Nat := 4983230072969 + 3 ^ 40 * 7042705 * 2
def baseEnd_7042705 : Nat := 3616292772822973117998695

theorem tailTrace_7042705 : CollatzResearch.WordTrace tailWord_7042705 prefixEnd_7042705 3616292772822973117998695 := by
  unfold tailWord_7042705
  simp only [CollatzResearch.WordTrace]
  refine ⟨256868553950490058099449569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171245702633660038732966379 256868553950490058099449569)
  ·
    refine ⟨192651415462867543574587177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256868553950490058099449569 192651415462867543574587177)
    ·
      refine ⟨144488561597150657680940383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192651415462867543574587177 144488561597150657680940383)
      ·
        refine ⟨216732842395725986521410575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144488561597150657680940383 216732842395725986521410575)
        ·
          refine ⟨325099263593588979782115863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216732842395725986521410575 325099263593588979782115863)
          ·
            refine ⟨487648895390383469673173795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325099263593588979782115863 487648895390383469673173795)
            ·
              refine ⟨731473343085575204509760693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487648895390383469673173795 731473343085575204509760693)
              ·
                refine ⟨68575625914272675422790065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731473343085575204509760693 68575625914272675422790065)
                ·
                  refine ⟨51431719435704506567092549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68575625914272675422790065 51431719435704506567092549)
                  ·
                    refine ⟨9643447394194594981329853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51431719435704506567092549 9643447394194594981329853)
                    ·
                      refine ⟨3616292772822973117998695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9643447394194594981329853 3616292772822973117998695)
                      ·
                        rfl

theorem cell23_7042705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_7042705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042705 prefixEnd_7042705 := by exact prefixLift 7042705
  have htrace : WordTrace (prefixWord ++ tailWord_7042705) baseStart_7042705 baseEnd_7042705 := by
    simpa [prefixWord, tailWord_7042705, baseEnd_7042705] using wordTrace_append hprefix tailTrace_7042705
  have hstable : (prefixWord ++ tailWord_7042705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042705).length < 2 ^ (prefixWord ++ tailWord_7042705).sum := by decide
  have hdescent : baseEnd_7042705 < baseStart_7042705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042725 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 7]
def baseStart_7042725 : Nat := 118140960795 + 7042725 * 2 ^ 59
def prefixEnd_7042725 : Nat := 4983230072969 + 3 ^ 40 * 7042725 * 2
def baseEnd_7042725 : Nat := 401811449159562559972067

theorem tailTrace_7042725 : CollatzResearch.WordTrace tailWord_7042725 prefixEnd_7042725 401811449159562559972067 := by
  unfold tailWord_7042725
  simp only [CollatzResearch.WordTrace]
  refine ⟨256869283410417601515177629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171246188940278401010118419 256869283410417601515177629)
  ·
    refine ⟨96325981278906600568191611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256869283410417601515177629 96325981278906600568191611)
    ·
      refine ⟨144488971918359900852287417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96325981278906600568191611 144488971918359900852287417)
      ·
        refine ⟨108366728938769925639215563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144488971918359900852287417 108366728938769925639215563)
        ·
          refine ⟨162550093408154888458823345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108366728938769925639215563 162550093408154888458823345)
          ·
            refine ⟨121912570056116166344117509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162550093408154888458823345 121912570056116166344117509)
            ·
              refine ⟨22858606885521781189522033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121912570056116166344117509 22858606885521781189522033)
              ·
                refine ⟨17143955164141335892141525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22858606885521781189522033 17143955164141335892141525)
                ·
                  refine ⟨401811449159562559972067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17143955164141335892141525 401811449159562559972067)
                  ·
                    rfl

theorem cell23_7042725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_7042725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042725 prefixEnd_7042725 := by exact prefixLift 7042725
  have htrace : WordTrace (prefixWord ++ tailWord_7042725) baseStart_7042725 baseEnd_7042725 := by
    simpa [prefixWord, tailWord_7042725, baseEnd_7042725] using wordTrace_append hprefix tailTrace_7042725
  have hstable : (prefixWord ++ tailWord_7042725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042725).length < 2 ^ (prefixWord ++ tailWord_7042725).sum := by decide
  have hdescent : baseEnd_7042725 < baseStart_7042725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042759 : List Nat := [1, 1, 4, 1, 1, 1, 7, 2, 5]
def baseStart_7042759 : Nat := 118140960795 + 7042759 * 2 ^ 59
def prefixEnd_7042759 : Nat := 4983230072969 + 3 ^ 40 * 7042759 * 2
def baseEnd_7042759 : Nat := 401813388975368434080383

theorem tailTrace_7042759 : CollatzResearch.WordTrace tailWord_7042759 prefixEnd_7042759 401813388975368434080383 := by
  unfold tailWord_7042759
  simp only [CollatzResearch.WordTrace]
  refine ⟨256870523492294425321915331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171247015661529616881276887 256870523492294425321915331)
  ·
    refine ⟨385305785238441637982872997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256870523492294425321915331 385305785238441637982872997)
    ·
      refine ⟨72244834732207807121788687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385305785238441637982872997 72244834732207807121788687)
      ·
        refine ⟨108367252098311710682683031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72244834732207807121788687 108367252098311710682683031)
        ·
          refine ⟨162550878147467566024024547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108367252098311710682683031 162550878147467566024024547)
          ·
            refine ⟨243826317221201349036036821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162550878147467566024024547 243826317221201349036036821)
            ·
              refine ⟨5714679309871906618032113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 243826317221201349036036821 5714679309871906618032113)
              ·
                refine ⟨4286009482403929963524085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5714679309871906618032113 4286009482403929963524085)
                ·
                  refine ⟨401813388975368434080383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4286009482403929963524085 401813388975368434080383)
                  ·
                    rfl

theorem cell23_7042759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 5].length) (baseStart_7042759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042759 prefixEnd_7042759 := by exact prefixLift 7042759
  have htrace : WordTrace (prefixWord ++ tailWord_7042759) baseStart_7042759 baseEnd_7042759 := by
    simpa [prefixWord, tailWord_7042759, baseEnd_7042759] using wordTrace_append hprefix tailTrace_7042759
  have hstable : (prefixWord ++ tailWord_7042759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042759).length < 2 ^ (prefixWord ++ tailWord_7042759).sum := by decide
  have hdescent : baseEnd_7042759 < baseStart_7042759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042770 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_7042770 : Nat := 118140960795 + 7042770 * 2 ^ 59
def prefixEnd_7042770 : Nat := 4983230072969 + 3 ^ 40 * 7042770 * 2
def baseEnd_7042770 : Nat := 3616326149065515363685897

theorem tailTrace_7042770 : CollatzResearch.WordTrace tailWord_7042770 prefixEnd_7042770 3616326149065515363685897 := by
  unfold tailWord_7042770
  simp only [CollatzResearch.WordTrace]
  refine ⟨64217731173813643550141441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171247283130169716133710509 64217731173813643550141441)
  ·
    refine ⟨48163298380360232662606081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64217731173813643550141441 48163298380360232662606081)
    ·
      refine ⟨36122473785270174496954561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48163298380360232662606081 36122473785270174496954561)
      ·
        refine ⟨27091855338952630872715921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36122473785270174496954561 27091855338952630872715921)
        ·
          refine ⟨20318891504214473154536941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27091855338952630872715921 20318891504214473154536941)
          ·
            refine ⟨7619584314080427432951353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20318891504214473154536941 7619584314080427432951353)
            ·
              refine ⟨5714688235560320574713515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7619584314080427432951353 5714688235560320574713515)
              ·
                refine ⟨8572032353340480862070273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714688235560320574713515 8572032353340480862070273)
                ·
                  refine ⟨6429024265005360646552705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8572032353340480862070273 6429024265005360646552705)
                  ·
                    refine ⟨4821768198754020484914529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6429024265005360646552705 4821768198754020484914529)
                    ·
                      refine ⟨3616326149065515363685897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4821768198754020484914529 3616326149065515363685897)
                      ·
                        rfl

theorem cell23_7042770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_7042770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042770 prefixEnd_7042770 := by exact prefixLift 7042770
  have htrace : WordTrace (prefixWord ++ tailWord_7042770) baseStart_7042770 baseEnd_7042770 := by
    simpa [prefixWord, tailWord_7042770, baseEnd_7042770] using wordTrace_append hprefix tailTrace_7042770
  have hstable : (prefixWord ++ tailWord_7042770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042770).length < 2 ^ (prefixWord ++ tailWord_7042770).sum := by decide
  have hdescent : baseEnd_7042770 < baseStart_7042770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042815 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 8]
def baseStart_7042815 : Nat := 118140960795 + 7042815 * 2 ^ 59
def prefixEnd_7042815 : Nat := 4983230072969 + 3 ^ 40 * 7042815 * 2
def baseEnd_7042815 : Nat := 401816583966107520847021

theorem tailTrace_7042815 : CollatzResearch.WordTrace tailWord_7042815 prefixEnd_7042815 401816583966107520847021 := by
  unfold tailWord_7042815
  simp only [CollatzResearch.WordTrace]
  refine ⟨256872565980091546885953899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171248377320061031257302599 256872565980091546885953899)
  ·
    refine ⟨385308848970137320328930849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256872565980091546885953899 385308848970137320328930849)
    ·
      refine ⟨288981636727602990246698137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385308848970137320328930849 288981636727602990246698137)
      ·
        refine ⟨216736227545702242685023603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288981636727602990246698137 216736227545702242685023603)
        ·
          refine ⟨325104341318553364027535405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216736227545702242685023603 325104341318553364027535405)
          ·
            refine ⟨121914127994457511510325777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325104341318553364027535405 121914127994457511510325777)
            ·
              refine ⟨91435595995843133632744333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121914127994457511510325777 91435595995843133632744333)
              ·
                refine ⟨34288348498441175112279125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91435595995843133632744333 34288348498441175112279125)
                ·
                  refine ⟨401816583966107520847021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34288348498441175112279125 401816583966107520847021)
                  ·
                    rfl

theorem cell23_7042815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 8].length) (baseStart_7042815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042815 prefixEnd_7042815 := by exact prefixLift 7042815
  have htrace : WordTrace (prefixWord ++ tailWord_7042815) baseStart_7042815 baseEnd_7042815 := by
    simpa [prefixWord, tailWord_7042815, baseEnd_7042815] using wordTrace_append hprefix tailTrace_7042815
  have hstable : (prefixWord ++ tailWord_7042815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042815).length < 2 ^ (prefixWord ++ tailWord_7042815).sum := by decide
  have hdescent : baseEnd_7042815 < baseStart_7042815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042835 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 6]
def baseStart_7042835 : Nat := 118140960795 + 7042835 * 2 ^ 59
def prefixEnd_7042835 : Nat := 4983230072969 + 3 ^ 40 * 7042835 * 2
def baseEnd_7042835 : Nat := 3616359525308057609373097

theorem tailTrace_7042835 : CollatzResearch.WordTrace tailWord_7042835 prefixEnd_7042835 3616359525308057609373097 := by
  unfold tailWord_7042835
  simp only [CollatzResearch.WordTrace]
  refine ⟨256873295440019090301681959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171248863626679393534454639 256873295440019090301681959)
  ·
    refine ⟨385309943160028635452522939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256873295440019090301681959 385309943160028635452522939)
    ·
      refine ⟨577964914740042953178784409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385309943160028635452522939 577964914740042953178784409)
      ·
        refine ⟨433473686055032214884088307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577964914740042953178784409 433473686055032214884088307)
        ·
          refine ⟨650210529082548322326132461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433473686055032214884088307 650210529082548322326132461)
          ·
            refine ⟨243828948405955620872299673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 650210529082548322326132461 243828948405955620872299673)
            ·
              refine ⟨182871711304466715654224755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243828948405955620872299673 182871711304466715654224755)
              ·
                refine ⟨274307566956700073481337133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182871711304466715654224755 274307566956700073481337133)
                ·
                  refine ⟨102865337608762527555501425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274307566956700073481337133 102865337608762527555501425)
                  ·
                    refine ⟨77149003206571895666626069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102865337608762527555501425 77149003206571895666626069)
                    ·
                      refine ⟨3616359525308057609373097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77149003206571895666626069 3616359525308057609373097)
                      ·
                        rfl

theorem cell23_7042835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_7042835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042835 prefixEnd_7042835 := by exact prefixLift 7042835
  have htrace : WordTrace (prefixWord ++ tailWord_7042835) baseStart_7042835 baseEnd_7042835 := by
    simpa [prefixWord, tailWord_7042835, baseEnd_7042835] using wordTrace_append hprefix tailTrace_7042835
  have hstable : (prefixWord ++ tailWord_7042835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042835).length < 2 ^ (prefixWord ++ tailWord_7042835).sum := by decide
  have hdescent : baseEnd_7042835 < baseStart_7042835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042893 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_7042893 : Nat := 118140960795 + 7042893 * 2 ^ 59
def prefixEnd_7042893 : Nat := 4983230072969 + 3 ^ 40 * 7042893 * 2
def baseEnd_7042893 : Nat := 3616389307186018382447831

theorem tailTrace_7042893 : CollatzResearch.WordTrace tailWord_7042893 prefixEnd_7042893 3616389307186018382447831 := by
  unfold tailWord_7042893
  simp only [CollatzResearch.WordTrace]
  refine ⟨256875410873808966207293333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171250273915872644138195555 256875410873808966207293333)
  ·
    refine ⟨12041034884709795290966875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 256875410873808966207293333 12041034884709795290966875)
    ·
      refine ⟨18061552327064692936450313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12041034884709795290966875 18061552327064692936450313)
      ·
        refine ⟨13546164245298519702337735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18061552327064692936450313 13546164245298519702337735)
        ·
          refine ⟨20319246367947779553506603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13546164245298519702337735 20319246367947779553506603)
          ·
            refine ⟨30478869551921669330259905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20319246367947779553506603 30478869551921669330259905)
            ·
              refine ⟨22859152163941251997694929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30478869551921669330259905 22859152163941251997694929)
              ·
                refine ⟨17144364122955938998271197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22859152163941251997694929 17144364122955938998271197)
                ·
                  refine ⟨6429136546108477124351699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17144364122955938998271197 6429136546108477124351699)
                  ·
                    refine ⟨9643704819162715686527549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6429136546108477124351699 9643704819162715686527549)
                    ·
                      refine ⟨3616389307186018382447831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9643704819162715686527549 3616389307186018382447831)
                      ·
                        rfl

theorem cell23_7042893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_7042893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042893 prefixEnd_7042893 := by exact prefixLift 7042893
  have htrace : WordTrace (prefixWord ++ tailWord_7042893) baseStart_7042893 baseEnd_7042893 := by
    simpa [prefixWord, tailWord_7042893, baseEnd_7042893] using wordTrace_append hprefix tailTrace_7042893
  have hstable : (prefixWord ++ tailWord_7042893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042893).length < 2 ^ (prefixWord ++ tailWord_7042893).sum := by decide
  have hdescent : baseEnd_7042893 < baseStart_7042893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042919 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_7042919 : Nat := 118140960795 + 7042919 * 2 ^ 59
def prefixEnd_7042919 : Nat := 4983230072969 + 3 ^ 40 * 7042919 * 2
def baseEnd_7042919 : Nat := 3616402657683035280722711

theorem tailTrace_7042919 : CollatzResearch.WordTrace tailWord_7042919 prefixEnd_7042919 3616402657683035280722711 := by
  unfold tailWord_7042919
  simp only [CollatzResearch.WordTrace]
  refine ⟨256876359171714772647739811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171250906114476515098493207 256876359171714772647739811)
  ·
    refine ⟨385314538757572158971609717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256876359171714772647739811 385314538757572158971609717)
    ·
      refine ⟨36123238008522389903588411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 385314538757572158971609717 36123238008522389903588411)
      ·
        refine ⟨54184857012783584855382617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36123238008522389903588411 54184857012783584855382617)
        ·
          refine ⟨40638642759587688641536963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54184857012783584855382617 40638642759587688641536963)
          ·
            refine ⟨60957964139381532962305445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40638642759587688641536963 60957964139381532962305445)
            ·
              refine ⟨11429618276134037430432271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60957964139381532962305445 11429618276134037430432271)
              ·
                refine ⟨17144427414201056145648407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11429618276134037430432271 17144427414201056145648407)
                ·
                  refine ⟨25716641121301584218472611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17144427414201056145648407 25716641121301584218472611)
                  ·
                    refine ⟨38574961681952376327708917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25716641121301584218472611 38574961681952376327708917)
                    ·
                      refine ⟨3616402657683035280722711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38574961681952376327708917 3616402657683035280722711)
                      ·
                        rfl

theorem cell23_7042919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_7042919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042919 prefixEnd_7042919 := by exact prefixLift 7042919
  have htrace : WordTrace (prefixWord ++ tailWord_7042919) baseStart_7042919 baseEnd_7042919 := by
    simpa [prefixWord, tailWord_7042919, baseEnd_7042919] using wordTrace_append hprefix tailTrace_7042919
  have hstable : (prefixWord ++ tailWord_7042919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042919).length < 2 ^ (prefixWord ++ tailWord_7042919).sum := by decide
  have hdescent : baseEnd_7042919 < baseStart_7042919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042926 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_7042926 : Nat := 118140960795 + 7042926 * 2 ^ 59
def prefixEnd_7042926 : Nat := 4983230072969 + 3 ^ 40 * 7042926 * 2
def baseEnd_7042926 : Nat := 1205468750682538917778393

theorem tailTrace_7042926 : CollatzResearch.WordTrace tailWord_7042926 prefixEnd_7042926 1205468750682538917778393 := by
  unfold tailWord_7042926
  simp only [CollatzResearch.WordTrace]
  refine ⟨32109576810336176605405579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171251076321792941895496421 32109576810336176605405579)
  ·
    refine ⟨48164365215504264908108369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32109576810336176605405579 48164365215504264908108369)
    ·
      refine ⟨36123273911628198681081277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48164365215504264908108369 36123273911628198681081277)
      ·
        refine ⟨13546227716860574505405479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36123273911628198681081277 13546227716860574505405479)
        ·
          refine ⟨20319341575290861758108219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13546227716860574505405479 20319341575290861758108219)
          ·
            refine ⟨30479012362936292637162329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20319341575290861758108219 30479012362936292637162329)
            ·
              refine ⟨22859259272202219477871747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30479012362936292637162329 22859259272202219477871747)
              ·
                refine ⟨34288888908303329216807621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22859259272202219477871747 34288888908303329216807621)
                ·
                  refine ⟨6429166670306874228151429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34288888908303329216807621 6429166670306874228151429)
                  ·
                    refine ⟨1205468750682538917778393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6429166670306874228151429 1205468750682538917778393)
                    ·
                      rfl

theorem cell23_7042926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_7042926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042926 prefixEnd_7042926 := by exact prefixLift 7042926
  have htrace : WordTrace (prefixWord ++ tailWord_7042926) baseStart_7042926 baseEnd_7042926 := by
    simpa [prefixWord, tailWord_7042926, baseEnd_7042926] using wordTrace_append hprefix tailTrace_7042926
  have hstable : (prefixWord ++ tailWord_7042926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042926).length < 2 ^ (prefixWord ++ tailWord_7042926).sum := by decide
  have hdescent : baseEnd_7042926 < baseStart_7042926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042949 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 1, 3, 3]
def baseStart_7042949 : Nat := 118140960795 + 7042949 * 2 ^ 59
def prefixEnd_7042949 : Nat := 4983230072969 + 3 ^ 40 * 7042949 * 2
def baseEnd_7042949 : Nat := 3616418062102670163347573

theorem tailTrace_7042949 : CollatzResearch.WordTrace tailWord_7042949 prefixEnd_7042949 3616418062102670163347573 := by
  unfold tailWord_7042949
  simp only [CollatzResearch.WordTrace]
  refine ⟨256877453361606087771331901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171251635574404058514221267 256877453361606087771331901)
  ·
    refine ⟨96329045010602282914249463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256877453361606087771331901 96329045010602282914249463)
    ·
      refine ⟨144493567515903424371374195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96329045010602282914249463 144493567515903424371374195)
      ·
        refine ⟨216740351273855136557061293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144493567515903424371374195 216740351273855136557061293)
        ·
          refine ⟨81277631727695676208897985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216740351273855136557061293 81277631727695676208897985)
          ·
            refine ⟨60958223795771757156673489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81277631727695676208897985 60958223795771757156673489)
            ·
              refine ⟨45718667846828817867505117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60958223795771757156673489 45718667846828817867505117)
              ·
                refine ⟨17144500442560806700314419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45718667846828817867505117 17144500442560806700314419)
                ·
                  refine ⟨25716750663841210050471629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17144500442560806700314419 25716750663841210050471629)
                  ·
                    refine ⟨9643781498940453768926861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25716750663841210050471629 9643781498940453768926861)
                    ·
                      refine ⟨3616418062102670163347573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9643781498940453768926861 3616418062102670163347573)
                      ·
                        rfl

theorem cell23_7042949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_7042949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042949 prefixEnd_7042949 := by exact prefixLift 7042949
  have htrace : WordTrace (prefixWord ++ tailWord_7042949) baseStart_7042949 baseEnd_7042949 := by
    simpa [prefixWord, tailWord_7042949, baseEnd_7042949] using wordTrace_append hprefix tailTrace_7042949
  have hstable : (prefixWord ++ tailWord_7042949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042949).length < 2 ^ (prefixWord ++ tailWord_7042949).sum := by decide
  have hdescent : baseEnd_7042949 < baseStart_7042949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042983 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_7042983 : Nat := 118140960795 + 7042983 * 2 ^ 59
def prefixEnd_7042983 : Nat := 4983230072969 + 3 ^ 40 * 7042983 * 2
def baseEnd_7042983 : Nat := 3616435520444923030322417

theorem tailTrace_7042983 : CollatzResearch.WordTrace tailWord_7042983 prefixEnd_7042983 3616435520444923030322417 := by
  unfold tailWord_7042983
  simp only [CollatzResearch.WordTrace]
  refine ⟨256878693443482911578069603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171252462295655274385379735 256878693443482911578069603)
  ·
    refine ⟨385318040165224367367104405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256878693443482911578069603 385318040165224367367104405)
    ·
      refine ⟨18061783132744892220333019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 385318040165224367367104405 18061783132744892220333019)
      ·
        refine ⟨27092674699117338330499529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18061783132744892220333019 27092674699117338330499529)
        ·
          refine ⟨20319506024338003747874647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27092674699117338330499529 20319506024338003747874647)
          ·
            refine ⟨30479259036507005621811971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20319506024338003747874647 30479259036507005621811971)
            ·
              refine ⟨45718888554760508432717957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30479259036507005621811971 45718888554760508432717957)
              ·
                refine ⟨8572291604017595331134617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45718888554760508432717957 8572291604017595331134617)
                ·
                  refine ⟨6429218703013196498350963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8572291604017595331134617 6429218703013196498350963)
                  ·
                    refine ⟨9643828054519794747526445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6429218703013196498350963 9643828054519794747526445)
                    ·
                      refine ⟨3616435520444923030322417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9643828054519794747526445 3616435520444923030322417)
                      ·
                        rfl

theorem cell23_7042983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_7042983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042983 prefixEnd_7042983 := by exact prefixLift 7042983
  have htrace : WordTrace (prefixWord ++ tailWord_7042983) baseStart_7042983 baseEnd_7042983 := by
    simpa [prefixWord, tailWord_7042983, baseEnd_7042983] using wordTrace_append hprefix tailTrace_7042983
  have hstable : (prefixWord ++ tailWord_7042983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042983).length < 2 ^ (prefixWord ++ tailWord_7042983).sum := by decide
  have hdescent : baseEnd_7042983 < baseStart_7042983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042984 : List Nat := [2, 1, 6, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7042984 : Nat := 118140960795 + 7042984 * 2 ^ 59
def prefixEnd_7042984 : Nat := 4983230072969 + 3 ^ 40 * 7042984 * 2
def baseEnd_7042984 : Nat := 3616436033925577526409913

theorem tailTrace_7042984 : CollatzResearch.WordTrace tailWord_7042984 prefixEnd_7042984 3616436033925577526409913 := by
  unfold tailWord_7042984
  simp only [CollatzResearch.WordTrace]
  refine ⟨128439364958239644374428003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171252486610986192499237337 128439364958239644374428003)
  ·
    refine ⟨192659047437359466561642005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128439364958239644374428003 192659047437359466561642005)
    ·
      refine ⟨9030892848626224995076969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192659047437359466561642005 9030892848626224995076969)
      ·
        refine ⟨6773169636469668746307727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9030892848626224995076969 6773169636469668746307727)
        ·
          refine ⟨10159754454704503119461591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773169636469668746307727 10159754454704503119461591)
          ·
            refine ⟨15239631682056754679192387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159754454704503119461591 15239631682056754679192387)
            ·
              refine ⟨22859447523085132018788581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15239631682056754679192387 22859447523085132018788581)
              ·
                refine ⟨4286146410578462253522859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22859447523085132018788581 4286146410578462253522859)
                ·
                  refine ⟨6429219615867693380284289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286146410578462253522859 6429219615867693380284289)
                  ·
                    refine ⟨4821914711900770035213217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6429219615867693380284289 4821914711900770035213217)
                    ·
                      refine ⟨3616436033925577526409913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4821914711900770035213217 3616436033925577526409913)
                      ·
                        rfl

theorem cell23_7042984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7042984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042984 prefixEnd_7042984 := by exact prefixLift 7042984
  have htrace : WordTrace (prefixWord ++ tailWord_7042984) baseStart_7042984 baseEnd_7042984 := by
    simpa [prefixWord, tailWord_7042984, baseEnd_7042984] using wordTrace_append hprefix tailTrace_7042984
  have hstable : (prefixWord ++ tailWord_7042984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042984).length < 2 ^ (prefixWord ++ tailWord_7042984).sum := by decide
  have hdescent : baseEnd_7042984 < baseStart_7042984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042990 : List Nat := [4, 1, 5, 1, 1, 2, 1, 8]
def baseStart_7042990 : Nat := 118140960795 + 7042990 * 2 ^ 59
def prefixEnd_7042990 : Nat := 4983230072969 + 3 ^ 40 * 7042990 * 2
def baseEnd_7042990 : Nat := 133942189437389055664255

theorem tailTrace_7042990 : CollatzResearch.WordTrace tailWord_7042990 prefixEnd_7042990 133942189437389055664255 := by
  unfold tailWord_7042990
  simp only [CollatzResearch.WordTrace]
  refine ⟨32109868594307193971696803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171252632502971701182382949 32109868594307193971696803)
  ·
    refine ⟨48164802891460790957545205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32109868594307193971696803 48164802891460790957545205)
    ·
      refine ⟨4515450271074449152269863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48164802891460790957545205 4515450271074449152269863)
      ·
        refine ⟨6773175406611673728404795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515450271074449152269863 6773175406611673728404795)
        ·
          refine ⟨10159763109917510592607193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773175406611673728404795 10159763109917510592607193)
          ·
            refine ⟨7619822332438132944455395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10159763109917510592607193 7619822332438132944455395)
            ·
              refine ⟨11429733498657199416683093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7619822332438132944455395 11429733498657199416683093)
              ·
                refine ⟨133942189437389055664255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11429733498657199416683093 133942189437389055664255)
                ·
                  rfl

theorem cell23_7042990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_7042990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042990 prefixEnd_7042990 := by exact prefixLift 7042990
  have htrace : WordTrace (prefixWord ++ tailWord_7042990) baseStart_7042990 baseEnd_7042990 := by
    simpa [prefixWord, tailWord_7042990, baseEnd_7042990] using wordTrace_append hprefix tailTrace_7042990
  have hstable : (prefixWord ++ tailWord_7042990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042990).length < 2 ^ (prefixWord ++ tailWord_7042990).sum := by decide
  have hdescent : baseEnd_7042990 < baseStart_7042990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043057 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 2, 2, 2]
def baseStart_7043057 : Nat := 118140960795 + 7043057 * 2 ^ 59
def prefixEnd_7043057 : Nat := 4983230072969 + 3 ^ 40 * 7043057 * 2
def baseEnd_7043057 : Nat := 3616473518013355740797077

theorem tailTrace_7043057 : CollatzResearch.WordTrace tailWord_7043057 prefixEnd_7043057 3616473518013355740797077 := by
  unfold tailWord_7043057
  simp only [CollatzResearch.WordTrace]
  refine ⟨256881392445214822216263425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171254261630143214810842283 256881392445214822216263425)
  ·
    refine ⟨192661044333911116662197569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256881392445214822216263425 192661044333911116662197569)
    ·
      refine ⟨144495783250433337496648177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192661044333911116662197569 144495783250433337496648177)
      ·
        refine ⟨108371837437825003122486133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144495783250433337496648177 108371837437825003122486133)
        ·
          refine ⟨10159859759796094042733075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108371837437825003122486133 10159859759796094042733075)
          ·
            refine ⟨15239789639694141064099613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159859759796094042733075 15239789639694141064099613)
            ·
              refine ⟨5714921114885302899037355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15239789639694141064099613 5714921114885302899037355)
              ·
                refine ⟨8572381672327954348556033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714921114885302899037355 8572381672327954348556033)
                ·
                  refine ⟨6429286254245965761417025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8572381672327954348556033 6429286254245965761417025)
                  ·
                    refine ⟨4821964690684474321062769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6429286254245965761417025 4821964690684474321062769)
                    ·
                      refine ⟨3616473518013355740797077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4821964690684474321062769 3616473518013355740797077)
                      ·
                        rfl

theorem cell23_7043057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_7043057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043057 prefixEnd_7043057 := by exact prefixLift 7043057
  have htrace : WordTrace (prefixWord ++ tailWord_7043057) baseStart_7043057 baseEnd_7043057 := by
    simpa [prefixWord, tailWord_7043057, baseEnd_7043057] using wordTrace_append hprefix tailTrace_7043057
  have hstable : (prefixWord ++ tailWord_7043057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043057).length < 2 ^ (prefixWord ++ tailWord_7043057).sum := by decide
  have hdescent : baseEnd_7043057 < baseStart_7043057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043096 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7043096 : Nat := 118140960795 + 7043096 * 2 ^ 59
def prefixEnd_7043096 : Nat := 4983230072969 + 3 ^ 40 * 7043096 * 2
def baseEnd_7043096 : Nat := 3616493543758881088209397

theorem tailTrace_7043096 : CollatzResearch.WordTrace tailWord_7043096 prefixEnd_7043096 3616493543758881088209397 := by
  unfold tailWord_7043096
  simp only [CollatzResearch.WordTrace]
  refine ⟨128441407446036765938466571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171255209928049021251288761 128441407446036765938466571)
  ·
    refine ⟨192662111169055148907699857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128441407446036765938466571 192662111169055148907699857)
    ·
      refine ⟨144496583376791361680774893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192662111169055148907699857 144496583376791361680774893)
      ·
        refine ⟨54186218766296760630290585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144496583376791361680774893 54186218766296760630290585)
        ·
          refine ⟨40639664074722570472717939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54186218766296760630290585 40639664074722570472717939)
          ·
            refine ⟨60959496112083855709076909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40639664074722570472717939 60959496112083855709076909)
            ·
              refine ⟨22859811042031445890903841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60959496112083855709076909 22859811042031445890903841)
              ·
                refine ⟨17144858281523584418177881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22859811042031445890903841 17144858281523584418177881)
                ·
                  refine ⟨12858643711142688313633411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17144858281523584418177881 12858643711142688313633411)
                  ·
                    refine ⟨19287965566714032470450117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12858643711142688313633411 19287965566714032470450117)
                    ·
                      refine ⟨3616493543758881088209397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19287965566714032470450117 3616493543758881088209397)
                      ·
                        rfl

theorem cell23_7043096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7043096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043096 prefixEnd_7043096 := by exact prefixLift 7043096
  have htrace : WordTrace (prefixWord ++ tailWord_7043096) baseStart_7043096 baseEnd_7043096 := by
    simpa [prefixWord, tailWord_7043096, baseEnd_7043096] using wordTrace_append hprefix tailTrace_7043096
  have hstable : (prefixWord ++ tailWord_7043096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043096).length < 2 ^ (prefixWord ++ tailWord_7043096).sum := by decide
  have hdescent : baseEnd_7043096 < baseStart_7043096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043099 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 3]
def baseStart_7043099 : Nat := 118140960795 + 7043099 * 2 ^ 59
def prefixEnd_7043099 : Nat := 4983230072969 + 3 ^ 40 * 7043099 * 2
def baseEnd_7043099 : Nat := 3616495084200844576471883

theorem tailTrace_7043099 : CollatzResearch.WordTrace tailWord_7043099 prefixEnd_7043099 3616495084200844576471883 := by
  unfold tailWord_7043099
  simp only [CollatzResearch.WordTrace]
  refine ⟨256882924311062663389292351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171255282874041775592861567 256882924311062663389292351)
  ·
    refine ⟨385324386466593995083938527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256882924311062663389292351 385324386466593995083938527)
    ·
      refine ⟨577986579699890992625907791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385324386466593995083938527 577986579699890992625907791)
      ·
        refine ⟨866979869549836488938861687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577986579699890992625907791 866979869549836488938861687)
        ·
          refine ⟨1300469804324754733408292531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866979869549836488938861687 1300469804324754733408292531)
          ·
            refine ⟨1950704706487132100112438797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300469804324754733408292531 1950704706487132100112438797)
            ·
              refine ⟨731514264932674537542164549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1950704706487132100112438797 731514264932674537542164549)
              ·
                refine ⟨137158924674876475789155853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 731514264932674537542164549 137158924674876475789155853)
                ·
                  refine ⟨51434596753078678420933445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137158924674876475789155853 51434596753078678420933445)
                  ·
                    refine ⟨9643986891202252203925021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51434596753078678420933445 9643986891202252203925021)
                    ·
                      refine ⟨3616495084200844576471883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9643986891202252203925021 3616495084200844576471883)
                      ·
                        rfl

theorem cell23_7043099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 3].length) (baseStart_7043099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043099 prefixEnd_7043099 := by exact prefixLift 7043099
  have htrace : WordTrace (prefixWord ++ tailWord_7043099) baseStart_7043099 baseEnd_7043099 := by
    simpa [prefixWord, tailWord_7043099, baseEnd_7043099] using wordTrace_append hprefix tailTrace_7043099
  have hstable : (prefixWord ++ tailWord_7043099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043099).length < 2 ^ (prefixWord ++ tailWord_7043099).sum := by decide
  have hdescent : baseEnd_7043099 < baseStart_7043099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043133 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_7043133 : Nat := 118140960795 + 7043133 * 2 ^ 59
def prefixEnd_7043133 : Nat := 4983230072969 + 3 ^ 40 * 7043133 * 2
def baseEnd_7043133 : Nat := 3616512542543097443446727

theorem tailTrace_7043133 : CollatzResearch.WordTrace tailWord_7043133 prefixEnd_7043133 3616512542543097443446727 := by
  unfold tailWord_7043133
  simp only [CollatzResearch.WordTrace]
  refine ⟨256884164392939487196030053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171256109595292991464020035 256884164392939487196030053)
  ·
    refine ⟨48165780823676153849255635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256884164392939487196030053 48165780823676153849255635)
    ·
      refine ⟨72248671235514230773883453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48165780823676153849255635 72248671235514230773883453)
      ·
        refine ⟨27093251713317836540206295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72248671235514230773883453 27093251713317836540206295)
        ·
          refine ⟨40639877569976754810309443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27093251713317836540206295 40639877569976754810309443)
          ·
            refine ⟨60959816354965132215464165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40639877569976754810309443 60959816354965132215464165)
            ·
              refine ⟨11429965566555962290399531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60959816354965132215464165 11429965566555962290399531)
              ·
                refine ⟨17144948349833943435599297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11429965566555962290399531 17144948349833943435599297)
                ·
                  refine ⟨12858711262375457576699473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17144948349833943435599297 12858711262375457576699473)
                  ·
                    refine ⟨9644033446781593182524605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12858711262375457576699473 9644033446781593182524605)
                    ·
                      refine ⟨3616512542543097443446727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9644033446781593182524605 3616512542543097443446727)
                      ·
                        rfl

theorem cell23_7043133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_7043133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043133 prefixEnd_7043133 := by exact prefixLift 7043133
  have htrace : WordTrace (prefixWord ++ tailWord_7043133) baseStart_7043133 baseEnd_7043133 := by
    simpa [prefixWord, tailWord_7043133, baseEnd_7043133] using wordTrace_append hprefix tailTrace_7043133
  have hstable : (prefixWord ++ tailWord_7043133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043133).length < 2 ^ (prefixWord ++ tailWord_7043133).sum := by decide
  have hdescent : baseEnd_7043133 < baseStart_7043133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043157 : List Nat := [1, 3, 2, 2, 1, 5, 2, 2, 1, 4]
def baseStart_7043157 : Nat := 118140960795 + 7043157 * 2 ^ 59
def prefixEnd_7043157 : Nat := 4983230072969 + 3 ^ 40 * 7043157 * 2
def baseEnd_7043157 : Nat := 1205508288692935116515539

theorem tailTrace_7043157 : CollatzResearch.WordTrace tailWord_7043157 prefixEnd_7043157 1205508288692935116515539 := by
  unfold tailWord_7043157
  simp only [CollatzResearch.WordTrace]
  refine ⟨256885039744852539294903725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171256693163235026196602483 256885039744852539294903725)
  ·
    refine ⟨96331889904319702235588897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256885039744852539294903725 96331889904319702235588897)
    ·
      refine ⟨72248917428239776676691673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96331889904319702235588897 72248917428239776676691673)
      ·
        refine ⟨54186688071179832507518755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72248917428239776676691673 54186688071179832507518755)
        ·
          refine ⟨81280032106769748761278133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54186688071179832507518755 81280032106769748761278133)
          ·
            refine ⟨7620003010009663946369825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81280032106769748761278133 7620003010009663946369825)
            ·
              refine ⟨5715002257507247959777369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7620003010009663946369825 5715002257507247959777369)
              ·
                refine ⟨4286251693130435969833027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5715002257507247959777369 4286251693130435969833027)
                ·
                  refine ⟨6429377539695653954749541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286251693130435969833027 6429377539695653954749541)
                  ·
                    refine ⟨1205508288692935116515539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6429377539695653954749541 1205508288692935116515539)
                    ·
                      rfl

theorem cell23_7043157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_7043157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043157 prefixEnd_7043157 := by exact prefixLift 7043157
  have htrace : WordTrace (prefixWord ++ tailWord_7043157) baseStart_7043157 baseEnd_7043157 := by
    simpa [prefixWord, tailWord_7043157, baseEnd_7043157] using wordTrace_append hprefix tailTrace_7043157
  have hstable : (prefixWord ++ tailWord_7043157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043157).length < 2 ^ (prefixWord ++ tailWord_7043157).sum := by decide
  have hdescent : baseEnd_7043157 < baseStart_7043157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043190 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_7043190 : Nat := 118140960795 + 7043190 * 2 ^ 59
def prefixEnd_7043190 : Nat := 4983230072969 + 3 ^ 40 * 7043190 * 2
def baseEnd_7043190 : Nat := 3616541810940403720433965

theorem tailTrace_7043190 : CollatzResearch.WordTrace tailWord_7043190 prefixEnd_7043190 3616541810940403720433965 := by
  unfold tailWord_7043190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16055390209608311620678439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171257495569155323953903349 16055390209608311620678439)
  ·
    refine ⟨24083085314412467431017659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16055390209608311620678439 24083085314412467431017659)
    ·
      refine ⟨36124627971618701146526489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24083085314412467431017659 36124627971618701146526489)
      ·
        refine ⟨27093470978714025859894867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36124627971618701146526489 27093470978714025859894867)
        ·
          refine ⟨40640206468071038789842301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27093470978714025859894867 40640206468071038789842301)
          ·
            refine ⟨15240077425526639546190863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40640206468071038789842301 15240077425526639546190863)
            ·
              refine ⟨22860116138289959319286295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15240077425526639546190863 22860116138289959319286295)
              ·
                refine ⟨34290174207434938978929443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22860116138289959319286295 34290174207434938978929443)
                ·
                  refine ⟨51435261311152408468394165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34290174207434938978929443 51435261311152408468394165)
                  ·
                    refine ⟨4822055747920538293911953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51435261311152408468394165 4822055747920538293911953)
                    ·
                      refine ⟨3616541810940403720433965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822055747920538293911953 3616541810940403720433965)
                      ·
                        rfl

theorem cell23_7043190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_7043190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043190 prefixEnd_7043190 := by exact prefixLift 7043190
  have htrace : WordTrace (prefixWord ++ tailWord_7043190) baseStart_7043190 baseEnd_7043190 := by
    simpa [prefixWord, tailWord_7043190, baseEnd_7043190] using wordTrace_append hprefix tailTrace_7043190
  have hstable : (prefixWord ++ tailWord_7043190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043190).length < 2 ^ (prefixWord ++ tailWord_7043190).sum := by decide
  have hdescent : baseEnd_7043190 < baseStart_7043190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043196 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_7043196 : Nat := 118140960795 + 7043196 * 2 ^ 59
def prefixEnd_7043196 : Nat := 4983230072969 + 3 ^ 40 * 7043196 * 2
def baseEnd_7043196 : Nat := 1205514963941443565652979

theorem tailTrace_7043196 : CollatzResearch.WordTrace tailWord_7043196 prefixEnd_7043196 1205514963941443565652979 := by
  unfold tailWord_7043196
  simp only [CollatzResearch.WordTrace]
  refine ⟨128443231095855624477786721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171257641461140832637048961 128443231095855624477786721)
  ·
    refine ⟨96332423321891718358340041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128443231095855624477786721 96332423321891718358340041)
    ·
      refine ⟨72249317491418788768755031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96332423321891718358340041 72249317491418788768755031)
      ·
        refine ⟨108373976237128183153132547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72249317491418788768755031 108373976237128183153132547)
        ·
          refine ⟨162560964355692274729698821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108373976237128183153132547 162560964355692274729698821)
          ·
            refine ⟨30480180816692301511818529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162560964355692274729698821 30480180816692301511818529)
            ·
              refine ⟨22860135612519226133863897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30480180816692301511818529 22860135612519226133863897)
              ·
                refine ⟨17145101709389419600397923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22860135612519226133863897 17145101709389419600397923)
                ·
                  refine ⟨25717652564084129400596885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17145101709389419600397923 25717652564084129400596885)
                  ·
                    refine ⟨1205514963941443565652979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25717652564084129400596885 1205514963941443565652979)
                    ·
                      rfl

theorem cell23_7043196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_7043196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043196 prefixEnd_7043196 := by exact prefixLift 7043196
  have htrace : WordTrace (prefixWord ++ tailWord_7043196) baseStart_7043196 baseEnd_7043196 := by
    simpa [prefixWord, tailWord_7043196, baseEnd_7043196] using wordTrace_append hprefix tailTrace_7043196
  have hstable : (prefixWord ++ tailWord_7043196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043196).length < 2 ^ (prefixWord ++ tailWord_7043196).sum := by decide
  have hdescent : baseEnd_7043196 < baseStart_7043196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043197 : List Nat := [1, 4, 1, 1, 3, 3, 2, 3, 1, 1, 3]
def baseStart_7043197 : Nat := 118140960795 + 7043197 * 2 ^ 59
def prefixEnd_7043197 : Nat := 4983230072969 + 3 ^ 40 * 7043197 * 2
def baseEnd_7043197 : Nat := 3616545405304985193046433

theorem tailTrace_7043197 : CollatzResearch.WordTrace tailWord_7043197 prefixEnd_7043197 3616545405304985193046433 := by
  unfold tailWord_7043197
  simp only [CollatzResearch.WordTrace]
  refine ⟨256886498664707626126359845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171257665776471750750906563 256886498664707626126359845)
  ·
    refine ⟨48166218499632679898692471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256886498664707626126359845 48166218499632679898692471)
    ·
      refine ⟨72249327749449019848038707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48166218499632679898692471 72249327749449019848038707)
      ·
        refine ⟨108373991624173529772058061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72249327749449019848038707 108373991624173529772058061)
        ·
          refine ⟨40640246859065073664521773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108373991624173529772058061 40640246859065073664521773)
          ·
            refine ⟨15240092572149402624195665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40640246859065073664521773 15240092572149402624195665)
            ·
              refine ⟨11430069429112051968146749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15240092572149402624195665 11430069429112051968146749)
              ·
                refine ⟨4286276035917019488055031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11430069429112051968146749 4286276035917019488055031)
                ·
                  refine ⟨6429414053875529232082547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286276035917019488055031 6429414053875529232082547)
                  ·
                    refine ⟨9644121080813293848123821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6429414053875529232082547 9644121080813293848123821)
                    ·
                      refine ⟨3616545405304985193046433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9644121080813293848123821 3616545405304985193046433)
                      ·
                        rfl

theorem cell23_7043197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_7043197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043197 prefixEnd_7043197 := by exact prefixLift 7043197
  have htrace : WordTrace (prefixWord ++ tailWord_7043197) baseStart_7043197 baseEnd_7043197 := by
    simpa [prefixWord, tailWord_7043197, baseEnd_7043197] using wordTrace_append hprefix tailTrace_7043197
  have hstable : (prefixWord ++ tailWord_7043197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043197).length < 2 ^ (prefixWord ++ tailWord_7043197).sum := by decide
  have hdescent : baseEnd_7043197 < baseStart_7043197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043203 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 4]
def baseStart_7043203 : Nat := 118140960795 + 7043203 * 2 ^ 59
def prefixEnd_7043203 : Nat := 4983230072969 + 3 ^ 40 * 7043203 * 2
def baseEnd_7043203 : Nat := 3616548486188912169571405

theorem tailTrace_7043203 : CollatzResearch.WordTrace tailWord_7043203 prefixEnd_7043203 3616548486188912169571405 := by
  unfold tailWord_7043203
  simp only [CollatzResearch.WordTrace]
  refine ⟨256886717502685889151078263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171257811668457259434052175 256886717502685889151078263)
  ·
    refine ⟨385330076254028833726617395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256886717502685889151078263 385330076254028833726617395)
    ·
      refine ⟨577995114381043250589926093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385330076254028833726617395 577995114381043250589926093)
      ·
        refine ⟨216748167892891218971222285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577995114381043250589926093 216748167892891218971222285)
        ·
          refine ⟨81280562959834207114208357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216748167892891218971222285 81280562959834207114208357)
          ·
            refine ⟨15240105554968913833914067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81280562959834207114208357 15240105554968913833914067)
            ·
              refine ⟨22860158332453370750871101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15240105554968913833914067 22860158332453370750871101)
              ·
                refine ⟨8572559374670014031576663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22860158332453370750871101 8572559374670014031576663)
                ·
                  refine ⟨12858839062005021047364995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8572559374670014031576663 12858839062005021047364995)
                  ·
                    refine ⟨19288258593007531571047493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12858839062005021047364995 19288258593007531571047493)
                    ·
                      refine ⟨3616548486188912169571405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19288258593007531571047493 3616548486188912169571405)
                      ·
                        rfl

theorem cell23_7043203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_7043203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043203 prefixEnd_7043203 := by exact prefixLift 7043203
  have htrace : WordTrace (prefixWord ++ tailWord_7043203) baseStart_7043203 baseEnd_7043203 := by
    simpa [prefixWord, tailWord_7043203, baseEnd_7043203] using wordTrace_append hprefix tailTrace_7043203
  have hstable : (prefixWord ++ tailWord_7043203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043203).length < 2 ^ (prefixWord ++ tailWord_7043203).sum := by decide
  have hdescent : baseEnd_7043203 < baseStart_7043203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043209 : List Nat := [1, 2, 1, 1, 4, 2, 12]
def baseStart_7043209 : Nat := 118140960795 + 7043209 * 2 ^ 59
def prefixEnd_7043209 : Nat := 4983230072969 + 3 ^ 40 * 7043209 * 2
def baseEnd_7043209 : Nat := 44648784778677026495017

theorem tailTrace_7043209 : CollatzResearch.WordTrace tailWord_7043209 prefixEnd_7043209 44648784778677026495017 := by
  unfold tailWord_7043209
  simp only [CollatzResearch.WordTrace]
  refine ⟨256886936340664152175796681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171257957560442768117197787 256886936340664152175796681)
  ·
    refine ⟨192665202255498114131847511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256886936340664152175796681 192665202255498114131847511)
    ·
      refine ⟨288997803383247171197771267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192665202255498114131847511 288997803383247171197771267)
      ·
        refine ⟨433496705074870756796656901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288997803383247171197771267 433496705074870756796656901)
        ·
          refine ⟨81280632201538266899373169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 433496705074870756796656901 81280632201538266899373169)
          ·
            refine ⟨60960474151153700174529877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81280632201538266899373169 60960474151153700174529877)
            ·
              refine ⟨44648784778677026495017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 60960474151153700174529877 44648784778677026495017)
              ·
                rfl

theorem cell23_7043209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 12].length) (baseStart_7043209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043209 prefixEnd_7043209 := by exact prefixLift 7043209
  have htrace : WordTrace (prefixWord ++ tailWord_7043209) baseStart_7043209 baseEnd_7043209 := by
    simpa [prefixWord, tailWord_7043209, baseEnd_7043209] using wordTrace_append hprefix tailTrace_7043209
  have hstable : (prefixWord ++ tailWord_7043209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043209).length < 2 ^ (prefixWord ++ tailWord_7043209).sum := by decide
  have hdescent : baseEnd_7043209 < baseStart_7043209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043219 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 7]
def baseStart_7043219 : Nat := 118140960795 + 7043219 * 2 ^ 59
def prefixEnd_7043219 : Nat := 4983230072969 + 3 ^ 40 * 7043219 * 2
def baseEnd_7043219 : Nat := 3616556701879384106971331

theorem tailTrace_7043219 : CollatzResearch.WordTrace tailWord_7043219 prefixEnd_7043219 3616556701879384106971331 := by
  unfold tailWord_7043219
  simp only [CollatzResearch.WordTrace]
  refine ⟨256887301070627923883660711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171258200713751949255773807 256887301070627923883660711)
  ·
    refine ⟨385330951605941885825491067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256887301070627923883660711 385330951605941885825491067)
    ·
      refine ⟨577996427408912828738236601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385330951605941885825491067 577996427408912828738236601)
      ·
        refine ⟨433497320556684621553677451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577996427408912828738236601 433497320556684621553677451)
        ·
          refine ⟨650245980835026932330516177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433497320556684621553677451 650245980835026932330516177)
          ·
            refine ⟨487684485626270199247887133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650245980835026932330516177 487684485626270199247887133)
            ·
              refine ⟨182881682109851324717957675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 487684485626270199247887133 182881682109851324717957675)
              ·
                refine ⟨274322523164776987076936513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182881682109851324717957675 274322523164776987076936513)
                ·
                  refine ⟨205741892373582740307702385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274322523164776987076936513 205741892373582740307702385)
                  ·
                    refine ⟨154306419280187055230776789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205741892373582740307702385 154306419280187055230776789)
                    ·
                      refine ⟨3616556701879384106971331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154306419280187055230776789 3616556701879384106971331)
                      ·
                        rfl

theorem cell23_7043219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_7043219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043219 prefixEnd_7043219 := by exact prefixLift 7043219
  have htrace : WordTrace (prefixWord ++ tailWord_7043219) baseStart_7043219 baseEnd_7043219 := by
    simpa [prefixWord, tailWord_7043219, baseEnd_7043219] using wordTrace_append hprefix tailTrace_7043219
  have hstable : (prefixWord ++ tailWord_7043219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043219).length < 2 ^ (prefixWord ++ tailWord_7043219).sum := by decide
  have hdescent : baseEnd_7043219 < baseStart_7043219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043223 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 5]
def baseStart_7043223 : Nat := 118140960795 + 7043223 * 2 ^ 59
def prefixEnd_7043223 : Nat := 4983230072969 + 3 ^ 40 * 7043223 * 2
def baseEnd_7043223 : Nat := 3616558755802002091321313

theorem tailTrace_7043223 : CollatzResearch.WordTrace tailWord_7043223 prefixEnd_7043223 3616558755802002091321313 := by
  unfold tailWord_7043223
  simp only [CollatzResearch.WordTrace]
  refine ⟨256887446962613432566806323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171258297975075621711204215 256887446962613432566806323)
  ·
    refine ⟨385331170443920148850209485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256887446962613432566806323 385331170443920148850209485)
    ·
      refine ⟨144499188916470055818828557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385331170443920148850209485 144499188916470055818828557)
      ·
        refine ⟨54187195843676270932060709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144499188916470055818828557 54187195843676270932060709)
        ·
          refine ⟨10160099220689300799761383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54187195843676270932060709 10160099220689300799761383)
          ·
            refine ⟨15240148831033951199642075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10160099220689300799761383 15240148831033951199642075)
            ·
              refine ⟨22860223246550926799463113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15240148831033951199642075 22860223246550926799463113)
              ·
                refine ⟨17145167434913195099597335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22860223246550926799463113 17145167434913195099597335)
                ·
                  refine ⟨25717751152369792649396003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17145167434913195099597335 25717751152369792649396003)
                  ·
                    refine ⟨38576626728554688974094005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25717751152369792649396003 38576626728554688974094005)
                    ·
                      refine ⟨3616558755802002091321313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38576626728554688974094005 3616558755802002091321313)
                      ·
                        rfl

theorem cell23_7043223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_7043223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043223 prefixEnd_7043223 := by exact prefixLift 7043223
  have htrace : WordTrace (prefixWord ++ tailWord_7043223) baseStart_7043223 baseEnd_7043223 := by
    simpa [prefixWord, tailWord_7043223, baseEnd_7043223] using wordTrace_append hprefix tailTrace_7043223
  have hstable : (prefixWord ++ tailWord_7043223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043223).length < 2 ^ (prefixWord ++ tailWord_7043223).sum := by decide
  have hdescent : baseEnd_7043223 < baseStart_7043223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043233 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_7043233 : Nat := 118140960795 + 7043233 * 2 ^ 59
def prefixEnd_7043233 : Nat := 4983230072969 + 3 ^ 40 * 7043233 * 2
def baseEnd_7043233 : Nat := 3616563890608547052196267

theorem tailTrace_7043233 : CollatzResearch.WordTrace tailWord_7043233 prefixEnd_7043233 3616563890608547052196267 := by
  unfold tailWord_7043233
  simp only [CollatzResearch.WordTrace]
  refine ⟨256887811692577204274670353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171258541128384802849780235 256887811692577204274670353)
  ·
    refine ⟨192665858769432903206002765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256887811692577204274670353 192665858769432903206002765)
    ·
      refine ⟨72249697038537338702251037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192665858769432903206002765 72249697038537338702251037)
      ·
        refine ⟨27093636389451502013344139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72249697038537338702251037 27093636389451502013344139)
        ·
          refine ⟨40640454584177253020016209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27093636389451502013344139 40640454584177253020016209)
          ·
            refine ⟨30480340938132939765012157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40640454584177253020016209 30480340938132939765012157)
            ·
              refine ⟨11430127851799852411879559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30480340938132939765012157 11430127851799852411879559)
              ·
                refine ⟨17145191777699778617819339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11430127851799852411879559 17145191777699778617819339)
                ·
                  refine ⟨25717787666549667926729009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17145191777699778617819339 25717787666549667926729009)
                  ·
                    refine ⟨19288340749912250945046757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25717787666549667926729009 19288340749912250945046757)
                    ·
                      refine ⟨3616563890608547052196267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19288340749912250945046757 3616563890608547052196267)
                      ·
                        rfl

theorem cell23_7043233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_7043233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043233 prefixEnd_7043233 := by exact prefixLift 7043233
  have htrace : WordTrace (prefixWord ++ tailWord_7043233) baseStart_7043233 baseEnd_7043233 := by
    simpa [prefixWord, tailWord_7043233, baseEnd_7043233] using wordTrace_append hprefix tailTrace_7043233
  have hstable : (prefixWord ++ tailWord_7043233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043233).length < 2 ^ (prefixWord ++ tailWord_7043233).sum := by decide
  have hdescent : baseEnd_7043233 < baseStart_7043233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043263 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 5, 3, 2]
def baseStart_7043263 : Nat := 118140960795 + 7043263 * 2 ^ 59
def prefixEnd_7043263 : Nat := 4983230072969 + 3 ^ 40 * 7043263 * 2
def baseEnd_7043263 : Nat := 3616579295028181934821129

theorem tailTrace_7043263 : CollatzResearch.WordTrace tailWord_7043263 prefixEnd_7043263 3616579295028181934821129 := by
  unfold tailWord_7043263
  simp only [CollatzResearch.WordTrace]
  refine ⟨256888905882468519398262443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171259270588312346265508295 256888905882468519398262443)
  ·
    refine ⟨385333358823702779097393665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256888905882468519398262443 385333358823702779097393665)
    ·
      refine ⟨289000019117777084323045249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385333358823702779097393665 289000019117777084323045249)
      ·
        refine ⟨216750014338332813242283937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289000019117777084323045249 216750014338332813242283937)
        ·
          refine ⟨162562510753749609931712953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216750014338332813242283937 162562510753749609931712953)
          ·
            refine ⟨121921883065312207448784715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162562510753749609931712953 121921883065312207448784715)
            ·
              refine ⟨182882824597968311173177073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121921883065312207448784715 182882824597968311173177073)
              ·
                refine ⟨137162118448476233379882805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182882824597968311173177073 137162118448476233379882805)
                ·
                  refine ⟨12858948604544646879364013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137162118448476233379882805 12858948604544646879364013)
                  ·
                    refine ⟨4822105726704242579761505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12858948604544646879364013 4822105726704242579761505)
                    ·
                      refine ⟨3616579295028181934821129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822105726704242579761505 3616579295028181934821129)
                      ·
                        rfl

theorem cell23_7043263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_7043263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043263 prefixEnd_7043263 := by exact prefixLift 7043263
  have htrace : WordTrace (prefixWord ++ tailWord_7043263) baseStart_7043263 baseEnd_7043263 := by
    simpa [prefixWord, tailWord_7043263, baseEnd_7043263] using wordTrace_append hprefix tailTrace_7043263
  have hstable : (prefixWord ++ tailWord_7043263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043263).length < 2 ^ (prefixWord ++ tailWord_7043263).sum := by decide
  have hdescent : baseEnd_7043263 < baseStart_7043263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043296 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_7043296 : Nat := 118140960795 + 7043296 * 2 ^ 59
def prefixEnd_7043296 : Nat := 4983230072969 + 3 ^ 40 * 7043296 * 2
def baseEnd_7043296 : Nat := 3616596239889780305708477

theorem tailTrace_7043296 : CollatzResearch.WordTrace tailWord_7043296 prefixEnd_7043296 3616596239889780305708477 := by
  unfold tailWord_7043296
  simp only [CollatzResearch.WordTrace]
  refine ⟨128445054745674483017106871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171260072994232644022809161 128445054745674483017106871)
  ·
    refine ⟨192667582118511724525660307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128445054745674483017106871 192667582118511724525660307)
    ·
      refine ⟨289001373177767586788490461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192667582118511724525660307 289001373177767586788490461)
      ·
        refine ⟨108375514941662845045683923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289001373177767586788490461 108375514941662845045683923)
        ·
          refine ⟨162563272412494267568525885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108375514941662845045683923 162563272412494267568525885)
          ·
            refine ⟨60961227154685350338197207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162563272412494267568525885 60961227154685350338197207)
            ·
              refine ⟨91441840732028025507295811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60961227154685350338197207 91441840732028025507295811)
              ·
                refine ⟨137162761098042038260943717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91441840732028025507295811 137162761098042038260943717)
                ·
                  refine ⟨25718017705882882173926947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137162761098042038260943717 25718017705882882173926947)
                  ·
                    refine ⟨38577026558824323260890421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25718017705882882173926947 38577026558824323260890421)
                    ·
                      refine ⟨3616596239889780305708477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38577026558824323260890421 3616596239889780305708477)
                      ·
                        rfl

theorem cell23_7043296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_7043296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043296 prefixEnd_7043296 := by exact prefixLift 7043296
  have htrace : WordTrace (prefixWord ++ tailWord_7043296) baseStart_7043296 baseEnd_7043296 := by
    simpa [prefixWord, tailWord_7043296, baseEnd_7043296] using wordTrace_append hprefix tailTrace_7043296
  have hstable : (prefixWord ++ tailWord_7043296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043296).length < 2 ^ (prefixWord ++ tailWord_7043296).sum := by decide
  have hdescent : baseEnd_7043296 < baseStart_7043296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043314 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 1, 3, 2]
def baseStart_7043314 : Nat := 118140960795 + 7043314 * 2 ^ 59
def prefixEnd_7043314 : Nat := 4983230072969 + 3 ^ 40 * 7043314 * 2
def baseEnd_7043314 : Nat := 3616605482541561235283395

theorem tailTrace_7043314 : CollatzResearch.WordTrace tailWord_7043314 prefixEnd_7043314 3616605482541561235283395 := by
  unfold tailWord_7043314
  simp only [CollatzResearch.WordTrace]
  refine ⟨64222691501320938777092249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171260510670189170072245997 64222691501320938777092249)
  ·
    refine ⟨48167018625990704082819187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64222691501320938777092249 48167018625990704082819187)
    ·
      refine ⟨72250527938986056124228781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48167018625990704082819187 72250527938986056124228781)
      ·
        refine ⟨27093947977119771046585793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72250527938986056124228781 27093947977119771046585793)
        ·
          refine ⟨20320460982839828284939345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27093947977119771046585793 20320460982839828284939345)
          ·
            refine ⟨15240345737129871213704509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20320460982839828284939345 15240345737129871213704509)
            ·
              refine ⟨5715129651423701705139191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15240345737129871213704509 5715129651423701705139191)
              ·
                refine ⟨8572694477135552557708787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5715129651423701705139191 8572694477135552557708787)
                ·
                  refine ⟨12859041715703328836563181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8572694477135552557708787 12859041715703328836563181)
                  ·
                    refine ⟨4822140643388748313711193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12859041715703328836563181 4822140643388748313711193)
                    ·
                      refine ⟨3616605482541561235283395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822140643388748313711193 3616605482541561235283395)
                      ·
                        rfl

theorem cell23_7043314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_7043314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043314 prefixEnd_7043314 := by exact prefixLift 7043314
  have htrace : WordTrace (prefixWord ++ tailWord_7043314) baseStart_7043314 baseEnd_7043314 := by
    simpa [prefixWord, tailWord_7043314, baseEnd_7043314] using wordTrace_append hprefix tailTrace_7043314
  have hstable : (prefixWord ++ tailWord_7043314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043314).length < 2 ^ (prefixWord ++ tailWord_7043314).sum := by decide
  have hdescent : baseEnd_7043314 < baseStart_7043314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043327 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 2, 2, 2]
def baseStart_7043327 : Nat := 118140960795 + 7043327 * 2 ^ 59
def prefixEnd_7043327 : Nat := 4983230072969 + 3 ^ 40 * 7043327 * 2
def baseEnd_7043327 : Nat := 3616612157790069684420835

theorem tailTrace_7043327 : CollatzResearch.WordTrace tailWord_7043327 prefixEnd_7043327 3616612157790069684420835 := by
  unfold tailWord_7043327
  simp only [CollatzResearch.WordTrace]
  refine ⟨256891240154236658328592235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171260826769491105552394823 256891240154236658328592235)
  ·
    refine ⟨385336860231354987492888353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256891240154236658328592235 385336860231354987492888353)
    ·
      refine ⟨289002645173516240619666265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385336860231354987492888353 289002645173516240619666265)
      ·
        refine ⟨216751983880137180464749699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289002645173516240619666265 216751983880137180464749699)
        ·
          refine ⟨325127975820205770697124549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216751983880137180464749699 325127975820205770697124549)
          ·
            refine ⟨60961495466288582005710853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 325127975820205770697124549 60961495466288582005710853)
            ·
              refine ⟨11430280399929109126070785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60961495466288582005710853 11430280399929109126070785)
              ·
                refine ⟨8572710299946831844553089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11430280399929109126070785 8572710299946831844553089)
                ·
                  refine ⟨6429532724960123883414817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8572710299946831844553089 6429532724960123883414817)
                  ·
                    refine ⟨4822149543720092912561113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6429532724960123883414817 4822149543720092912561113)
                    ·
                      refine ⟨3616612157790069684420835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822149543720092912561113 3616612157790069684420835)
                      ·
                        rfl

theorem cell23_7043327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_7043327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043327 prefixEnd_7043327 := by exact prefixLift 7043327
  have htrace : WordTrace (prefixWord ++ tailWord_7043327) baseStart_7043327 baseEnd_7043327 := by
    simpa [prefixWord, tailWord_7043327, baseEnd_7043327] using wordTrace_append hprefix tailTrace_7043327
  have hstable : (prefixWord ++ tailWord_7043327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043327).length < 2 ^ (prefixWord ++ tailWord_7043327).sum := by decide
  have hdescent : baseEnd_7043327 < baseStart_7043327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043330 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_7043330 : Nat := 118140960795 + 7043330 * 2 ^ 59
def prefixEnd_7043330 : Nat := 4983230072969 + 3 ^ 40 * 7043330 * 2
def baseEnd_7043330 : Nat := 3616613698232033172683321

theorem tailTrace_7043330 : CollatzResearch.WordTrace tailWord_7043330 prefixEnd_7043330 3616613698232033172683321 := by
  unfold tailWord_7043330
  simp only [CollatzResearch.WordTrace]
  refine ⟨64222837393306447460237861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171260899715483859893967629 64222837393306447460237861)
  ·
    refine ⟨12041782011244958898794599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64222837393306447460237861 12041782011244958898794599)
    ·
      refine ⟨18062673016867438348191899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12041782011244958898794599 18062673016867438348191899)
      ·
        refine ⟨27094009525301157522287849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18062673016867438348191899 27094009525301157522287849)
        ·
          refine ⟨20320507143975868141715887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27094009525301157522287849 20320507143975868141715887)
          ·
            refine ⟨30480760715963802212573831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20320507143975868141715887 30480760715963802212573831)
            ·
              refine ⟨45721141073945703318860747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30480760715963802212573831 45721141073945703318860747)
              ·
                refine ⟨68581711610918554978291121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45721141073945703318860747 68581711610918554978291121)
                ·
                  refine ⟨51436283708188916233718341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68581711610918554978291121 51436283708188916233718341)
                  ·
                    refine ⟨9644303195285421793822189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51436283708188916233718341 9644303195285421793822189)
                    ·
                      refine ⟨3616613698232033172683321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9644303195285421793822189 3616613698232033172683321)
                      ·
                        rfl

theorem cell23_7043330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_7043330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043330 prefixEnd_7043330 := by exact prefixLift 7043330
  have htrace : WordTrace (prefixWord ++ tailWord_7043330) baseStart_7043330 baseEnd_7043330 := by
    simpa [prefixWord, tailWord_7043330, baseEnd_7043330] using wordTrace_append hprefix tailTrace_7043330
  have hstable : (prefixWord ++ tailWord_7043330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043330).length < 2 ^ (prefixWord ++ tailWord_7043330).sum := by decide
  have hdescent : baseEnd_7043330 < baseStart_7043330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043383 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_7043383 : Nat := 118140960795 + 7043383 * 2 ^ 59
def prefixEnd_7043383 : Nat := 4983230072969 + 3 ^ 40 * 7043383 * 2
def baseEnd_7043383 : Nat := 3616640912706721465320577

theorem tailTrace_7043383 : CollatzResearch.WordTrace tailWord_7043383 prefixEnd_7043383 3616640912706721465320577 := by
  unfold tailWord_7043383
  simp only [CollatzResearch.WordTrace]
  refine ⟨256893282642033779892630803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171262188428022519928420535 256893282642033779892630803)
  ·
    refine ⟨385339923963050669838946205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256893282642033779892630803 385339923963050669838946205)
    ·
      refine ⟨144502471486144001189604827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385339923963050669838946205 144502471486144001189604827)
      ·
        refine ⟨216753707229216001784407241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144502471486144001189604827 216753707229216001784407241)
        ·
          refine ⟨162565280421912001338305431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216753707229216001784407241 162565280421912001338305431)
          ·
            refine ⟨243847920632868002007458147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162565280421912001338305431 243847920632868002007458147)
            ·
              refine ⟨365771880949302003011187221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243847920632868002007458147 365771880949302003011187221)
              ·
                refine ⟨17145556919498531391149401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 365771880949302003011187221 17145556919498531391149401)
                ·
                  refine ⟨12859167689623898543362051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17145556919498531391149401 12859167689623898543362051)
                  ·
                    refine ⟨19288751534435847815043077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12859167689623898543362051 19288751534435847815043077)
                    ·
                      refine ⟨3616640912706721465320577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19288751534435847815043077 3616640912706721465320577)
                      ·
                        rfl

theorem cell23_7043383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_7043383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043383 prefixEnd_7043383 := by exact prefixLift 7043383
  have htrace : WordTrace (prefixWord ++ tailWord_7043383) baseStart_7043383 baseEnd_7043383 := by
    simpa [prefixWord, tailWord_7043383, baseEnd_7043383] using wordTrace_append hprefix tailTrace_7043383
  have hstable : (prefixWord ++ tailWord_7043383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043383).length < 2 ^ (prefixWord ++ tailWord_7043383).sum := by decide
  have hdescent : baseEnd_7043383 < baseStart_7043383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043400 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 2, 4, 2]
def baseStart_7043400 : Nat := 118140960795 + 7043400 * 2 ^ 59
def prefixEnd_7043400 : Nat := 4983230072969 + 3 ^ 40 * 7043400 * 2
def baseEnd_7043400 : Nat := 3616649641877847898807999

theorem tailTrace_7043400 : CollatzResearch.WordTrace tailWord_7043400 prefixEnd_7043400 3616649641877847898807999 := by
  unfold tailWord_7043400
  simp only [CollatzResearch.WordTrace]
  refine ⟨128446951341486095897999827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171262601788648127863999769 128446951341486095897999827)
  ·
    refine ⟨192670427012229143846999741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128446951341486095897999827 192670427012229143846999741)
    ·
      refine ⟨72251410129585928942624903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192670427012229143846999741 72251410129585928942624903)
      ·
        refine ⟨108377115194378893413937355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72251410129585928942624903 108377115194378893413937355)
        ·
          refine ⟨162565672791568340120906033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108377115194378893413937355 162565672791568340120906033)
          ·
            refine ⟨121924254593676255090679525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162565672791568340120906033 121924254593676255090679525)
            ·
              refine ⟨22860797736314297829502411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121924254593676255090679525 22860797736314297829502411)
              ·
                refine ⟨34291196604471446744253617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22860797736314297829502411 34291196604471446744253617)
                ·
                  refine ⟨25718397453353585058190213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34291196604471446744253617 25718397453353585058190213)
                  ·
                    refine ⟨4822199522503797198410665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25718397453353585058190213 4822199522503797198410665)
                    ·
                      refine ⟨3616649641877847898807999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822199522503797198410665 3616649641877847898807999)
                      ·
                        rfl

theorem cell23_7043400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_7043400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043400 prefixEnd_7043400 := by exact prefixLift 7043400
  have htrace : WordTrace (prefixWord ++ tailWord_7043400) baseStart_7043400 baseEnd_7043400 := by
    simpa [prefixWord, tailWord_7043400, baseEnd_7043400] using wordTrace_append hprefix tailTrace_7043400
  have hstable : (prefixWord ++ tailWord_7043400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043400).length < 2 ^ (prefixWord ++ tailWord_7043400).sum := by decide
  have hdescent : baseEnd_7043400 < baseStart_7043400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043403 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 3]
def baseStart_7043403 : Nat := 118140960795 + 7043403 * 2 ^ 59
def prefixEnd_7043403 : Nat := 4983230072969 + 3 ^ 40 * 7043403 * 2
def baseEnd_7043403 : Nat := 3616651182319811387070485

theorem tailTrace_7043403 : CollatzResearch.WordTrace tailWord_7043403 prefixEnd_7043403 3616651182319811387070485 := by
  unfold tailWord_7043403
  simp only [CollatzResearch.WordTrace]
  refine ⟨256894012101961323308358863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171262674734640882205572575 256894012101961323308358863)
  ·
    refine ⟨385341018152941984962538295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256894012101961323308358863 385341018152941984962538295)
    ·
      refine ⟨578011527229412977443807443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385341018152941984962538295 578011527229412977443807443)
      ·
        refine ⟨867017290844119466165711165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578011527229412977443807443 867017290844119466165711165)
        ·
          refine ⟨325131484066544799812141687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 867017290844119466165711165 325131484066544799812141687)
          ·
            refine ⟨487697226099817199718212531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325131484066544799812141687 487697226099817199718212531)
            ·
              refine ⟨731545839149725799577318797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487697226099817199718212531 731545839149725799577318797)
              ·
                refine ⟨274329689681147174841494549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 731545839149725799577318797 274329689681147174841494549)
                ·
                  refine ⟨12859204203803773820695057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 274329689681147174841494549 12859204203803773820695057)
                  ·
                    refine ⟨9644403152852830365521293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12859204203803773820695057 9644403152852830365521293)
                    ·
                      refine ⟨3616651182319811387070485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9644403152852830365521293 3616651182319811387070485)
                      ·
                        rfl

theorem cell23_7043403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 3].length) (baseStart_7043403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043403 prefixEnd_7043403 := by exact prefixLift 7043403
  have htrace : WordTrace (prefixWord ++ tailWord_7043403) baseStart_7043403 baseEnd_7043403 := by
    simpa [prefixWord, tailWord_7043403, baseEnd_7043403] using wordTrace_append hprefix tailTrace_7043403
  have hstable : (prefixWord ++ tailWord_7043403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043403).length < 2 ^ (prefixWord ++ tailWord_7043403).sum := by decide
  have hdescent : baseEnd_7043403 < baseStart_7043403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043410 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_7043410 : Nat := 118140960795 + 7043410 * 2 ^ 59
def prefixEnd_7043410 : Nat := 4983230072969 + 3 ^ 40 * 7043410 * 2
def baseEnd_7043410 : Nat := 1205551592228130953227651

theorem tailTrace_7043410 : CollatzResearch.WordTrace tailWord_7043410 prefixEnd_7043410 1205551592228130953227651 := by
  unfold tailWord_7043410
  simp only [CollatzResearch.WordTrace]
  refine ⟨64223566853233990875965921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171262844941957309002575789 64223566853233990875965921)
  ·
    refine ⟨48167675139925493156974441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64223566853233990875965921 48167675139925493156974441)
    ·
      refine ⟨36125756354944119867730831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48167675139925493156974441 36125756354944119867730831)
      ·
        refine ⟨54188634532416179801596247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36125756354944119867730831 54188634532416179801596247)
        ·
          refine ⟨81282951798624269702394371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54188634532416179801596247 81282951798624269702394371)
          ·
            refine ⟨121924427697936404553591557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81282951798624269702394371 121924427697936404553591557)
            ·
              refine ⟨22860830193363075853798417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121924427697936404553591557 22860830193363075853798417)
              ·
                refine ⟨17145622645022306890348813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22860830193363075853798417 17145622645022306890348813)
                ·
                  refine ⟨6429608491883365083880805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17145622645022306890348813 6429608491883365083880805)
                  ·
                    refine ⟨1205551592228130953227651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6429608491883365083880805 1205551592228130953227651)
                    ·
                      rfl

theorem cell23_7043410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_7043410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043410 prefixEnd_7043410 := by exact prefixLift 7043410
  have htrace : WordTrace (prefixWord ++ tailWord_7043410) baseStart_7043410 baseEnd_7043410 := by
    simpa [prefixWord, tailWord_7043410, baseEnd_7043410] using wordTrace_append hprefix tailTrace_7043410
  have hstable : (prefixWord ++ tailWord_7043410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043410).length < 2 ^ (prefixWord ++ tailWord_7043410).sum := by decide
  have hdescent : baseEnd_7043410 < baseStart_7043410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043457 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 6]
def baseStart_7043457 : Nat := 118140960795 + 7043457 * 2 ^ 59
def prefixEnd_7043457 : Nat := 4983230072969 + 3 ^ 40 * 7043457 * 2
def baseEnd_7043457 : Nat := 401853212252794908421693

theorem tailTrace_7043457 : CollatzResearch.WordTrace tailWord_7043457 prefixEnd_7043457 401853212252794908421693 := by
  unfold tailWord_7043457
  simp only [CollatzResearch.WordTrace]
  refine ⟨256895981643765690530824625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171263987762510460353883083 256895981643765690530824625)
  ·
    refine ⟨192671986232824267898118469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256895981643765690530824625 192671986232824267898118469)
    ·
      refine ⟨36125997418654550230897213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192671986232824267898118469 36125997418654550230897213)
      ·
        refine ⟨13547249031995456336586455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36125997418654550230897213 13547249031995456336586455)
        ·
          refine ⟨20320873547993184504879683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13547249031995456336586455 20320873547993184504879683)
          ·
            refine ⟨30481310321989776757319525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20320873547993184504879683 30481310321989776757319525)
            ·
              refine ⟨5715245685373083141997411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30481310321989776757319525 5715245685373083141997411)
              ·
                refine ⟨8572868528059624712996117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5715245685373083141997411 8572868528059624712996117)
                ·
                  refine ⟨401853212252794908421693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8572868528059624712996117 401853212252794908421693)
                  ·
                    rfl

theorem cell23_7043457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 6].length) (baseStart_7043457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043457 prefixEnd_7043457 := by exact prefixLift 7043457
  have htrace : WordTrace (prefixWord ++ tailWord_7043457) baseStart_7043457 baseEnd_7043457 := by
    simpa [prefixWord, tailWord_7043457, baseEnd_7043457] using wordTrace_append hprefix tailTrace_7043457
  have hstable : (prefixWord ++ tailWord_7043457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043457).length < 2 ^ (prefixWord ++ tailWord_7043457).sum := by decide
  have hdescent : baseEnd_7043457 < baseStart_7043457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043487 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 1, 5]
def baseStart_7043487 : Nat := 118140960795 + 7043487 * 2 ^ 59
def prefixEnd_7043487 : Nat := 4983230072969 + 3 ^ 40 * 7043487 * 2
def baseEnd_7043487 : Nat := 1205564771564929686140033

theorem tailTrace_7043487 : CollatzResearch.WordTrace tailWord_7043487 prefixEnd_7043487 1205564771564929686140033 := by
  unfold tailWord_7043487
  simp only [CollatzResearch.WordTrace]
  refine ⟨256897075833657005654416715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171264717222438003769611143 256897075833657005654416715)
  ·
    refine ⟨385345613750485508481625073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256897075833657005654416715 385345613750485508481625073)
    ·
      refine ⟨289009210312864131361218805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385345613750485508481625073 289009210312864131361218805)
      ·
        refine ⟨27094613466831012315114263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289009210312864131361218805 27094613466831012315114263)
        ·
          refine ⟨40641920200246518472671395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27094613466831012315114263 40641920200246518472671395)
          ·
            refine ⟨60962880300369777709007093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40641920200246518472671395 60962880300369777709007093)
            ·
              refine ⟨5715270028159666660219415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60962880300369777709007093 5715270028159666660219415)
              ·
                refine ⟨8572905042239499990329123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5715270028159666660219415 8572905042239499990329123)
                ·
                  refine ⟨12859357563359249985493685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8572905042239499990329123 12859357563359249985493685)
                  ·
                    refine ⟨1205564771564929686140033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12859357563359249985493685 1205564771564929686140033)
                    ·
                      rfl

theorem cell23_7043487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 5].length) (baseStart_7043487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043487 prefixEnd_7043487 := by exact prefixLift 7043487
  have htrace : WordTrace (prefixWord ++ tailWord_7043487) baseStart_7043487 baseEnd_7043487 := by
    simpa [prefixWord, tailWord_7043487, baseEnd_7043487] using wordTrace_append hprefix tailTrace_7043487
  have hstable : (prefixWord ++ tailWord_7043487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043487).length < 2 ^ (prefixWord ++ tailWord_7043487).sum := by decide
  have hdescent : baseEnd_7043487 < baseStart_7043487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043517 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_7043517 : Nat := 118140960795 + 7043517 * 2 ^ 59
def prefixEnd_7043517 : Nat := 4983230072969 + 3 ^ 40 * 7043517 * 2
def baseEnd_7043517 : Nat := 1205569906371474647014987

theorem tailTrace_7043517 : CollatzResearch.WordTrace tailWord_7043517 prefixEnd_7043517 1205569906371474647014987 := by
  unfold tailWord_7043517
  simp only [CollatzResearch.WordTrace]
  refine ⟨256898170023548320778008805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171265446682365547185339203 256898170023548320778008805)
  ·
    refine ⟨48168406879415310145876651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256898170023548320778008805 48168406879415310145876651)
    ·
      refine ⟨72252610319122965218814977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48168406879415310145876651 72252610319122965218814977)
      ·
        refine ⟨54189457739342223914111233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72252610319122965218814977 54189457739342223914111233)
        ·
          refine ⟨40642093304506667935583425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54189457739342223914111233 40642093304506667935583425)
          ·
            refine ⟨30481569978380000951687569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40642093304506667935583425 30481569978380000951687569)
            ·
              refine ⟨22861177483785000713765677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30481569978380000951687569 22861177483785000713765677)
              ·
                refine ⟨8572941556419375267662129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22861177483785000713765677 8572941556419375267662129)
                ·
                  refine ⟨6429706167314531450746597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8572941556419375267662129 6429706167314531450746597)
                  ·
                    refine ⟨1205569906371474647014987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6429706167314531450746597 1205569906371474647014987)
                    ·
                      rfl

theorem cell23_7043517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_7043517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043517 prefixEnd_7043517 := by exact prefixLift 7043517
  have htrace : WordTrace (prefixWord ++ tailWord_7043517) baseStart_7043517 baseEnd_7043517 := by
    simpa [prefixWord, tailWord_7043517, baseEnd_7043517] using wordTrace_append hprefix tailTrace_7043517
  have hstable : (prefixWord ++ tailWord_7043517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043517).length < 2 ^ (prefixWord ++ tailWord_7043517).sum := by decide
  have hdescent : baseEnd_7043517 < baseStart_7043517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043530 : List Nat := [3, 1, 2, 1, 2, 2, 5, 7]
def baseStart_7043530 : Nat := 118140960795 + 7043530 * 2 ^ 59
def prefixEnd_7043530 : Nat := 4983230072969 + 3 ^ 40 * 7043530 * 2
def baseEnd_7043530 : Nat := 133952459050478977414163

theorem tailTrace_7043530 : CollatzResearch.WordTrace tailWord_7043530 prefixEnd_7043530 133952459050478977414163 := by
  unfold tailWord_7043530
  simp only [CollatzResearch.WordTrace]
  refine ⟨64224661043125305999558011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171265762781667482665488029 64224661043125305999558011)
  ·
    refine ⟨96336991564687958999337017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64224661043125305999558011 96336991564687958999337017)
    ·
      refine ⟨72252743673515969249502763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96336991564687958999337017 72252743673515969249502763)
      ·
        refine ⟨108379115510273953874254145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72252743673515969249502763 108379115510273953874254145)
        ·
          refine ⟨81284336632705465405690609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108379115510273953874254145 81284336632705465405690609)
          ·
            refine ⟨60963252474529099054267957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81284336632705465405690609 60963252474529099054267957)
            ·
              refine ⟨5715304919487103036337621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60963252474529099054267957 5715304919487103036337621)
              ·
                refine ⟨133952459050478977414163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5715304919487103036337621 133952459050478977414163)
                ·
                  rfl

theorem cell23_7043530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 7].length) (baseStart_7043530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043530 prefixEnd_7043530 := by exact prefixLift 7043530
  have htrace : WordTrace (prefixWord ++ tailWord_7043530) baseStart_7043530 baseEnd_7043530 := by
    simpa [prefixWord, tailWord_7043530, baseEnd_7043530] using wordTrace_append hprefix tailTrace_7043530
  have hstable : (prefixWord ++ tailWord_7043530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043530).length < 2 ^ (prefixWord ++ tailWord_7043530).sum := by decide
  have hdescent : baseEnd_7043530 < baseStart_7043530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043538 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_7043538 : Nat := 118140960795 + 7043538 * 2 ^ 59
def prefixEnd_7043538 : Nat := 4983230072969 + 3 ^ 40 * 7043538 * 2
def baseEnd_7043538 : Nat := 1205573500736056119627455

theorem tailTrace_7043538 : CollatzResearch.WordTrace tailWord_7043538 prefixEnd_7043538 1205573500736056119627455 := by
  unfold tailWord_7043538
  simp only [CollatzResearch.WordTrace]
  refine ⟨64224733989118060341130817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171265957304314827576348845 64224733989118060341130817)
  ·
    refine ⟨48168550491838545255848113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64224733989118060341130817 48168550491838545255848113)
    ·
      refine ⟨36126412868878908941886085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48168550491838545255848113 36126412868878908941886085)
      ·
        refine ⟨6773702412914795426603641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36126412868878908941886085 6773702412914795426603641)
        ·
          refine ⟨5080276809686096569952731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6773702412914795426603641 5080276809686096569952731)
          ·
            refine ⟨7620415214529144854929097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080276809686096569952731 7620415214529144854929097)
            ·
              refine ⟨5715311410896858641196823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7620415214529144854929097 5715311410896858641196823)
              ·
                refine ⟨8572967116345287961795235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5715311410896858641196823 8572967116345287961795235)
                ·
                  refine ⟨12859450674517931942692853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8572967116345287961795235 12859450674517931942692853)
                  ·
                    refine ⟨1205573500736056119627455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12859450674517931942692853 1205573500736056119627455)
                    ·
                      rfl

theorem cell23_7043538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_7043538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043538 prefixEnd_7043538 := by exact prefixLift 7043538
  have htrace : WordTrace (prefixWord ++ tailWord_7043538) baseStart_7043538 baseEnd_7043538 := by
    simpa [prefixWord, tailWord_7043538, baseEnd_7043538] using wordTrace_append hprefix tailTrace_7043538
  have hstable : (prefixWord ++ tailWord_7043538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043538).length < 2 ^ (prefixWord ++ tailWord_7043538).sum := by decide
  have hdescent : baseEnd_7043538 < baseStart_7043538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043541 : List Nat := [1, 3, 2, 3, 1, 2, 1, 5, 1, 2, 2]
def baseStart_7043541 : Nat := 118140960795 + 7043541 * 2 ^ 59
def prefixEnd_7043541 : Nat := 4983230072969 + 3 ^ 40 * 7043541 * 2
def baseEnd_7043541 : Nat := 3616722042650131847144851

theorem tailTrace_7043541 : CollatzResearch.WordTrace tailWord_7043541 prefixEnd_7043541 3616722042650131847144851 := by
  unfold tailWord_7043541
  simp only [CollatzResearch.WordTrace]
  refine ⟨256899045375461372876882477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171266030250307581917921651 256899045375461372876882477)
  ·
    refine ⟨96337142015798014828830929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256899045375461372876882477 96337142015798014828830929)
    ·
      refine ⟨72252856511848511121623197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96337142015798014828830929 72252856511848511121623197)
      ·
        refine ⟨27094821191943191670608699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72252856511848511121623197 27094821191943191670608699)
        ·
          refine ⟨40642231787914787505913049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27094821191943191670608699 40642231787914787505913049)
          ·
            refine ⟨30481673840936090629434787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40642231787914787505913049 30481673840936090629434787)
            ·
              refine ⟨45722510761404135944152181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30481673840936090629434787 45722510761404135944152181)
              ·
                refine ⟨4286485383881637744764267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45722510761404135944152181 4286485383881637744764267)
                ·
                  refine ⟨6429728075822456617146401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286485383881637744764267 6429728075822456617146401)
                  ·
                    refine ⟨4822296056866842462859801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6429728075822456617146401 4822296056866842462859801)
                    ·
                      refine ⟨3616722042650131847144851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822296056866842462859801 3616722042650131847144851)
                      ·
                        rfl

theorem cell23_7043541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_7043541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043541 prefixEnd_7043541 := by exact prefixLift 7043541
  have htrace : WordTrace (prefixWord ++ tailWord_7043541) baseStart_7043541 baseEnd_7043541 := by
    simpa [prefixWord, tailWord_7043541, baseEnd_7043541] using wordTrace_append hprefix tailTrace_7043541
  have hstable : (prefixWord ++ tailWord_7043541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043541).length < 2 ^ (prefixWord ++ tailWord_7043541).sum := by decide
  have hdescent : baseEnd_7043541 < baseStart_7043541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043610 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_7043610 : Nat := 118140960795 + 7043610 * 2 ^ 59
def prefixEnd_7043610 : Nat := 4983230072969 + 3 ^ 40 * 7043610 * 2
def baseEnd_7043610 : Nat := 3616757472815292077182033

theorem tailTrace_7043610 : CollatzResearch.WordTrace tailWord_7043610 prefixEnd_7043610 3616757472815292077182033 := by
  unfold tailWord_7043610
  simp only [CollatzResearch.WordTrace]
  refine ⟨64225390503052849415286071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171267708008140931774096189 64225390503052849415286071)
  ·
    refine ⟨96338085754579274122929107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64225390503052849415286071 96338085754579274122929107)
    ·
      refine ⟨144507128631868911184393661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96338085754579274122929107 144507128631868911184393661)
      ·
        refine ⟨54190173236950841694147623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144507128631868911184393661 54190173236950841694147623)
        ·
          refine ⟨81285259855426262541221435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54190173236950841694147623 81285259855426262541221435)
          ·
            refine ⟨121927889783139393811832153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81285259855426262541221435 121927889783139393811832153)
            ·
              refine ⟨91445917337354545358874115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121927889783139393811832153 91445917337354545358874115)
              ·
                refine ⟨137168876006031818038311173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91445917337354545358874115 137168876006031818038311173)
                ·
                  refine ⟨25719164251130965882183345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137168876006031818038311173 25719164251130965882183345)
                  ·
                    refine ⟨19289373188348224411637509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25719164251130965882183345 19289373188348224411637509)
                    ·
                      refine ⟨3616757472815292077182033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19289373188348224411637509 3616757472815292077182033)
                      ·
                        rfl

theorem cell23_7043610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_7043610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043610 prefixEnd_7043610 := by exact prefixLift 7043610
  have htrace : WordTrace (prefixWord ++ tailWord_7043610) baseStart_7043610 baseEnd_7043610 := by
    simpa [prefixWord, tailWord_7043610, baseEnd_7043610] using wordTrace_append hprefix tailTrace_7043610
  have hstable : (prefixWord ++ tailWord_7043610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043610).length < 2 ^ (prefixWord ++ tailWord_7043610).sum := by decide
  have hdescent : baseEnd_7043610 < baseStart_7043610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043652 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7043652 : Nat := 118140960795 + 7043652 * 2 ^ 59
def prefixEnd_7043652 : Nat := 4983230072969 + 3 ^ 40 * 7043652 * 2
def baseEnd_7043652 : Nat := 3616779039002780912856841

theorem tailTrace_7043652 : CollatzResearch.WordTrace tailWord_7043652 prefixEnd_7043652 3616779039002780912856841 := by
  unfold tailWord_7043652
  simp only [CollatzResearch.WordTrace]
  refine ⟨128451546939029619417086605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171268729252039492556115473 128451546939029619417086605)
  ·
    refine ⟨48169330102136107281407477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128451546939029619417086605 48169330102136107281407477)
    ·
      refine ⟨4515874697075260057631951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48169330102136107281407477 4515874697075260057631951)
      ·
        refine ⟨6773812045612890086447927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515874697075260057631951 6773812045612890086447927)
        ·
          refine ⟨10160718068419335129671891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773812045612890086447927 10160718068419335129671891)
          ·
            refine ⟨15241077102629002694507837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10160718068419335129671891 15241077102629002694507837)
            ·
              refine ⟨5715403913485876010440439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15241077102629002694507837 5715403913485876010440439)
              ·
                refine ⟨8573105870228814015660659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5715403913485876010440439 8573105870228814015660659)
                ·
                  refine ⟨12859658805343221023490989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8573105870228814015660659 12859658805343221023490989)
                  ·
                    refine ⟨4822372052003707883809121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12859658805343221023490989 4822372052003707883809121)
                    ·
                      refine ⟨3616779039002780912856841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822372052003707883809121 3616779039002780912856841)
                      ·
                        rfl

theorem cell23_7043652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7043652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043652 prefixEnd_7043652 := by exact prefixLift 7043652
  have htrace : WordTrace (prefixWord ++ tailWord_7043652) baseStart_7043652 baseEnd_7043652 := by
    simpa [prefixWord, tailWord_7043652, baseEnd_7043652] using wordTrace_append hprefix tailTrace_7043652
  have hstable : (prefixWord ++ tailWord_7043652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043652).length < 2 ^ (prefixWord ++ tailWord_7043652).sum := by decide
  have hdescent : baseEnd_7043652 < baseStart_7043652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043660 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7043660 : Nat := 118140960795 + 7043660 * 2 ^ 59
def prefixEnd_7043660 : Nat := 4983230072969 + 3 ^ 40 * 7043660 * 2
def baseEnd_7043660 : Nat := 3616783146848016881556803

theorem tailTrace_7043660 : CollatzResearch.WordTrace tailWord_7043660 prefixEnd_7043660 3616783146848016881556803 := by
  unfold tailWord_7043660
  simp only [CollatzResearch.WordTrace]
  refine ⟨128451692831015128100232217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171268923774686837466976289 128451692831015128100232217)
  ·
    refine ⟨96338769623261346075174163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128451692831015128100232217 96338769623261346075174163)
    ·
      refine ⟨144508154434892019112761245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96338769623261346075174163 144508154434892019112761245)
      ·
        refine ⟨54190557913084507167285467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144508154434892019112761245 54190557913084507167285467)
        ·
          refine ⟨81285836869626760750928201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54190557913084507167285467 81285836869626760750928201)
          ·
            refine ⟨60964377652220070563196151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81285836869626760750928201 60964377652220070563196151)
            ·
              refine ⟨91446566478330105844794227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60964377652220070563196151 91446566478330105844794227)
              ·
                refine ⟨137169849717495158767191341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91446566478330105844794227 137169849717495158767191341)
                ·
                  refine ⟨51438693644060684537696753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137169849717495158767191341 51438693644060684537696753)
                  ·
                    refine ⟨38579020233045513403272565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51438693644060684537696753 38579020233045513403272565)
                    ·
                      refine ⟨3616783146848016881556803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38579020233045513403272565 3616783146848016881556803)
                      ·
                        rfl

theorem cell23_7043660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7043660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043660 prefixEnd_7043660 := by exact prefixLift 7043660
  have htrace : WordTrace (prefixWord ++ tailWord_7043660) baseStart_7043660 baseEnd_7043660 := by
    simpa [prefixWord, tailWord_7043660, baseEnd_7043660] using wordTrace_append hprefix tailTrace_7043660
  have hstable : (prefixWord ++ tailWord_7043660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043660).length < 2 ^ (prefixWord ++ tailWord_7043660).sum := by decide
  have hdescent : baseEnd_7043660 < baseStart_7043660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043678 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7043678 : Nat := 118140960795 + 7043678 * 2 ^ 59
def prefixEnd_7043678 : Nat := 4983230072969 + 3 ^ 40 * 7043678 * 2
def baseEnd_7043678 : Nat := 3616792389499797811131721

theorem tailTrace_7043678 : CollatzResearch.WordTrace tailWord_7043678 prefixEnd_7043678 3616792389499797811131721 := by
  unfold tailWord_7043678
  simp only [CollatzResearch.WordTrace]
  refine ⟨32113005271995630659327461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171269361450643363516413125 32113005271995630659327461)
  ·
    refine ⟨6021188488499180748623899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32113005271995630659327461 6021188488499180748623899)
    ·
      refine ⟨9031782732748771122935849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6021188488499180748623899 9031782732748771122935849)
      ·
        refine ⟨6773837049561578342201887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9031782732748771122935849 6773837049561578342201887)
        ·
          refine ⟨10160755574342367513302831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773837049561578342201887 10160755574342367513302831)
          ·
            refine ⟨15241133361513551269954247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10160755574342367513302831 15241133361513551269954247)
            ·
              refine ⟨22861700042270326904931371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15241133361513551269954247 22861700042270326904931371)
              ·
                refine ⟨34292550063405490357397057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22861700042270326904931371 34292550063405490357397057)
                ·
                  refine ⟨25719412547554117768047793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34292550063405490357397057 25719412547554117768047793)
                  ·
                    refine ⟨19289559410665588326035845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25719412547554117768047793 19289559410665588326035845)
                    ·
                      refine ⟨3616792389499797811131721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19289559410665588326035845 3616792389499797811131721)
                      ·
                        rfl

theorem cell23_7043678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7043678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043678 prefixEnd_7043678 := by exact prefixLift 7043678
  have htrace : WordTrace (prefixWord ++ tailWord_7043678) baseStart_7043678 baseEnd_7043678 := by
    simpa [prefixWord, tailWord_7043678, baseEnd_7043678] using wordTrace_append hprefix tailTrace_7043678
  have hstable : (prefixWord ++ tailWord_7043678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043678).length < 2 ^ (prefixWord ++ tailWord_7043678).sum := by decide
  have hdescent : baseEnd_7043678 < baseStart_7043678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043701 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_7043701 : Nat := 118140960795 + 7043701 * 2 ^ 59
def prefixEnd_7043701 : Nat := 4983230072969 + 3 ^ 40 * 7043701 * 2
def baseEnd_7043701 : Nat := 1205601399851617073714705

theorem tailTrace_7043701 : CollatzResearch.WordTrace tailWord_7043701 prefixEnd_7043701 1205601399851617073714705 := by
  unfold tailWord_7043701
  simp only [CollatzResearch.WordTrace]
  refine ⟨256904881054881720202706957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171269920703254480135137971 256904881054881720202706957)
  ·
    refine ⟨96339330395580645076015109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256904881054881720202706957 96339330395580645076015109)
    ·
      refine ⟨18063624449171370951752833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96339330395580645076015109 18063624449171370951752833)
      ·
        refine ⟨13547718336878528213814625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18063624449171370951752833 13547718336878528213814625)
        ·
          refine ⟨10160788752658896160360969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13547718336878528213814625 10160788752658896160360969)
          ·
            refine ⟨7620591564494172120270727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10160788752658896160360969 7620591564494172120270727)
            ·
              refine ⟨11430887346741258180406091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7620591564494172120270727 11430887346741258180406091)
              ·
                refine ⟨17146331020111887270609137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11430887346741258180406091 17146331020111887270609137)
                ·
                  refine ⟨12859748265083915452956853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17146331020111887270609137 12859748265083915452956853)
                  ·
                    refine ⟨1205601399851617073714705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12859748265083915452956853 1205601399851617073714705)
                    ·
                      rfl

theorem cell23_7043701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_7043701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043701 prefixEnd_7043701 := by exact prefixLift 7043701
  have htrace : WordTrace (prefixWord ++ tailWord_7043701) baseStart_7043701 baseEnd_7043701 := by
    simpa [prefixWord, tailWord_7043701, baseEnd_7043701] using wordTrace_append hprefix tailTrace_7043701
  have hstable : (prefixWord ++ tailWord_7043701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043701).length < 2 ^ (prefixWord ++ tailWord_7043701).sum := by decide
  have hdescent : baseEnd_7043701 < baseStart_7043701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043707 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 3]
def baseStart_7043707 : Nat := 118140960795 + 7043707 * 2 ^ 59
def prefixEnd_7043707 : Nat := 4983230072969 + 3 ^ 40 * 7043707 * 2
def baseEnd_7043707 : Nat := 3616807280438778197669087

theorem tailTrace_7043707 : CollatzResearch.WordTrace tailWord_7043707 prefixEnd_7043707 3616807280438778197669087 := by
  unfold tailWord_7043707
  simp only [CollatzResearch.WordTrace]
  refine ⟨256905099892859983227425375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171270066595239988818283583 256905099892859983227425375)
  ·
    refine ⟨385357649839289974841138063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256905099892859983227425375 385357649839289974841138063)
    ·
      refine ⟨578036474758934962261707095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385357649839289974841138063 578036474758934962261707095)
      ·
        refine ⟨867054712138402443392560643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578036474758934962261707095 867054712138402443392560643)
        ·
          refine ⟨1300582068207603665088840965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867054712138402443392560643 1300582068207603665088840965)
          ·
            refine ⟨243859137788925687204157681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1300582068207603665088840965 243859137788925687204157681)
            ·
              refine ⟨182894353341694265403118261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243859137788925687204157681 182894353341694265403118261)
              ·
                refine ⟨17146345625783837381542337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182894353341694265403118261 17146345625783837381542337)
                ·
                  refine ⟨12859759219337878036156753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17146345625783837381542337 12859759219337878036156753)
                  ·
                    refine ⟨9644819414503408527117565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12859759219337878036156753 9644819414503408527117565)
                    ·
                      refine ⟨3616807280438778197669087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9644819414503408527117565 3616807280438778197669087)
                      ·
                        rfl

theorem cell23_7043707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 3].length) (baseStart_7043707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043707 prefixEnd_7043707 := by exact prefixLift 7043707
  have htrace : WordTrace (prefixWord ++ tailWord_7043707) baseStart_7043707 baseEnd_7043707 := by
    simpa [prefixWord, tailWord_7043707, baseEnd_7043707] using wordTrace_append hprefix tailTrace_7043707
  have hstable : (prefixWord ++ tailWord_7043707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043707).length < 2 ^ (prefixWord ++ tailWord_7043707).sum := by decide
  have hdescent : baseEnd_7043707 < baseStart_7043707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043774 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_7043774 : Nat := 118140960795 + 7043774 * 2 ^ 59
def prefixEnd_7043774 : Nat := 4983230072969 + 3 ^ 40 * 7043774 * 2
def baseEnd_7043774 : Nat := 1205613894547543145177093

theorem tailTrace_7043774 : CollatzResearch.WordTrace tailWord_7043774 prefixEnd_7043774 1205613894547543145177093 := by
  unfold tailWord_7043774
  simp only [CollatzResearch.WordTrace]
  refine ⟨32113442947952156708764297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171271695722411502446742917 32113442947952156708764297)
  ·
    refine ⟨24085082210964117531573223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32113442947952156708764297 24085082210964117531573223)
    ·
      refine ⟨36127623316446176297359835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24085082210964117531573223 36127623316446176297359835)
      ·
        refine ⟨54191434974669264446039753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36127623316446176297359835 54191434974669264446039753)
        ·
          refine ⟨40643576231001948334529815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54191434974669264446039753 40643576231001948334529815)
          ·
            refine ⟨60965364346502922501794723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40643576231001948334529815 60965364346502922501794723)
            ·
              refine ⟨91448046519754383752692085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60965364346502922501794723 91448046519754383752692085)
              ·
                refine ⟨8573254361226973476814883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91448046519754383752692085 8573254361226973476814883)
                ·
                  refine ⟨12859881541840460215222325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8573254361226973476814883 12859881541840460215222325)
                  ·
                    refine ⟨1205613894547543145177093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12859881541840460215222325 1205613894547543145177093)
                    ·
                      rfl

theorem cell23_7043774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_7043774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043774 prefixEnd_7043774 := by exact prefixLift 7043774
  have htrace : WordTrace (prefixWord ++ tailWord_7043774) baseStart_7043774 baseEnd_7043774 := by
    simpa [prefixWord, tailWord_7043774, baseEnd_7043774] using wordTrace_append hprefix tailTrace_7043774
  have hstable : (prefixWord ++ tailWord_7043774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043774).length < 2 ^ (prefixWord ++ tailWord_7043774).sum := by decide
  have hdescent : baseEnd_7043774 < baseStart_7043774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043782 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7043782 : Nat := 118140960795 + 7043782 * 2 ^ 59
def prefixEnd_7043782 : Nat := 4983230072969 + 3 ^ 40 * 7043782 * 2
def baseEnd_7043782 : Nat := 1205615263829288468077081

theorem tailTrace_7043782 : CollatzResearch.WordTrace tailWord_7043782 prefixEnd_7043782 1205615263829288468077081 := by
  unfold tailWord_7043782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8028369855237133469887675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 171271890245058847357603733 8028369855237133469887675)
  ·
    refine ⟨12042554782855700204831513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8028369855237133469887675 12042554782855700204831513)
    ·
      refine ⟨9031916087141775153623635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12042554782855700204831513 9031916087141775153623635)
      ·
        refine ⟨13547874130712662730435453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9031916087141775153623635 13547874130712662730435453)
        ·
          refine ⟨5080452799017248523913295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13547874130712662730435453 5080452799017248523913295)
          ·
            refine ⟨7620679198525872785869943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080452799017248523913295 7620679198525872785869943)
            ·
              refine ⟨11431018797788809178804915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7620679198525872785869943 11431018797788809178804915)
              ·
                refine ⟨17146528196683213768207373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11431018797788809178804915 17146528196683213768207373)
                ·
                  refine ⟨6429948073756205163077765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17146528196683213768207373 6429948073756205163077765)
                  ·
                    refine ⟨1205615263829288468077081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6429948073756205163077765 1205615263829288468077081)
                    ·
                      rfl

theorem cell23_7043782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7043782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043782 prefixEnd_7043782 := by exact prefixLift 7043782
  have htrace : WordTrace (prefixWord ++ tailWord_7043782) baseStart_7043782 baseEnd_7043782 := by
    simpa [prefixWord, tailWord_7043782, baseEnd_7043782] using wordTrace_append hprefix tailTrace_7043782
  have hstable : (prefixWord ++ tailWord_7043782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043782).length < 2 ^ (prefixWord ++ tailWord_7043782).sum := by decide
  have hdescent : baseEnd_7043782 < baseStart_7043782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043788 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7043788 : Nat := 118140960795 + 7043788 * 2 ^ 59
def prefixEnd_7043788 : Nat := 4983230072969 + 3 ^ 40 * 7043788 * 2
def baseEnd_7043788 : Nat := 3616848872371792380756215

theorem tailTrace_7043788 : CollatzResearch.WordTrace tailWord_7043788 prefixEnd_7043788 3616848872371792380756215 := by
  unfold tailWord_7043788
  simp only [CollatzResearch.WordTrace]
  refine ⟨128454027102783267030562009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171272036137044356040749345 128454027102783267030562009)
  ·
    refine ⟨96340520327087450272921507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128454027102783267030562009 96340520327087450272921507)
    ·
      refine ⟨144510780490631175409382261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96340520327087450272921507 144510780490631175409382261)
      ·
        refine ⟨13547885670996672694629587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144510780490631175409382261 13547885670996672694629587)
        ·
          refine ⟨20321828506495009041944381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13547885670996672694629587 20321828506495009041944381)
          ·
            refine ⟨7620685689935628390729143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20321828506495009041944381 7620685689935628390729143)
            ·
              refine ⟨11431028534903442586093715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7620685689935628390729143 11431028534903442586093715)
              ·
                refine ⟨17146542802355163879140573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11431028534903442586093715 17146542802355163879140573)
                ·
                  refine ⟨6429953550883186454677715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17146542802355163879140573 6429953550883186454677715)
                  ·
                    refine ⟨9644930326324779682016573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6429953550883186454677715 9644930326324779682016573)
                    ·
                      refine ⟨3616848872371792380756215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9644930326324779682016573 3616848872371792380756215)
                      ·
                        rfl

theorem cell23_7043788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7043788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043788 prefixEnd_7043788 := by exact prefixLift 7043788
  have htrace : WordTrace (prefixWord ++ tailWord_7043788) baseStart_7043788 baseEnd_7043788 := by
    simpa [prefixWord, tailWord_7043788, baseEnd_7043788] using wordTrace_append hprefix tailTrace_7043788
  have hstable : (prefixWord ++ tailWord_7043788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043788).length < 2 ^ (prefixWord ++ tailWord_7043788).sum := by decide
  have hdescent : baseEnd_7043788 < baseStart_7043788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043807 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_7043807 : Nat := 118140960795 + 7043807 * 2 ^ 59
def prefixEnd_7043807 : Nat := 4983230072969 + 3 ^ 40 * 7043807 * 2
def baseEnd_7043807 : Nat := 3616858628504227806418627

theorem tailTrace_7043807 : CollatzResearch.WordTrace tailWord_7043807 prefixEnd_7043807 3616858628504227806418627 := by
  unfold tailWord_7043807
  simp only [CollatzResearch.WordTrace]
  refine ⟨256908747192497700306065675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171272498128331800204043783 256908747192497700306065675)
  ·
    refine ⟨385363120788746550459098513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256908747192497700306065675 385363120788746550459098513)
    ·
      refine ⟨289022340591559912844323885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385363120788746550459098513 289022340591559912844323885)
      ·
        refine ⟨108383377721834967316621457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289022340591559912844323885 108383377721834967316621457)
        ·
          refine ⟨81287533291376225487466093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108383377721834967316621457 81287533291376225487466093)
          ·
            refine ⟨30482824984266084557799785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81287533291376225487466093 30482824984266084557799785)
            ·
              refine ⟨22862118738199563418349839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30482824984266084557799785 22862118738199563418349839)
              ·
                refine ⟨34293178107299345127524759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22862118738199563418349839 34293178107299345127524759)
                ·
                  refine ⟨51439767160949017691287139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34293178107299345127524759 51439767160949017691287139)
                  ·
                    refine ⟨77159650741423526536930709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51439767160949017691287139 77159650741423526536930709)
                    ·
                      refine ⟨3616858628504227806418627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77159650741423526536930709 3616858628504227806418627)
                      ·
                        rfl

theorem cell23_7043807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_7043807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043807 prefixEnd_7043807 := by exact prefixLift 7043807
  have htrace : WordTrace (prefixWord ++ tailWord_7043807) baseStart_7043807 baseEnd_7043807 := by
    simpa [prefixWord, tailWord_7043807, baseEnd_7043807] using wordTrace_append hprefix tailTrace_7043807
  have hstable : (prefixWord ++ tailWord_7043807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043807).length < 2 ^ (prefixWord ++ tailWord_7043807).sum := by decide
  have hdescent : baseEnd_7043807 < baseStart_7043807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043811 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 4]
def baseStart_7043811 : Nat := 118140960795 + 7043811 * 2 ^ 59
def prefixEnd_7043811 : Nat := 4983230072969 + 3 ^ 40 * 7043811 * 2
def baseEnd_7043811 : Nat := 3616860682426845790768609

theorem tailTrace_7043811 : CollatzResearch.WordTrace tailWord_7043811 prefixEnd_7043811 3616860682426845790768609 := by
  unfold tailWord_7043811
  simp only [CollatzResearch.WordTrace]
  refine ⟨256908893084483208989211287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171272595389655472659474191 256908893084483208989211287)
  ·
    refine ⟨385363339626724813483816931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256908893084483208989211287 385363339626724813483816931)
    ·
      refine ⟨578045009440087220225725397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385363339626724813483816931 578045009440087220225725397)
      ·
        refine ⟨13547929908752044224040439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 578045009440087220225725397 13547929908752044224040439)
        ·
          refine ⟨20321894863128066336060659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13547929908752044224040439 20321894863128066336060659)
          ·
            refine ⟨30482842294692099504090989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20321894863128066336060659 30482842294692099504090989)
            ·
              refine ⟨11431065860509537314034121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30482842294692099504090989 11431065860509537314034121)
              ·
                refine ⟨8573299395382152985525591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11431065860509537314034121 8573299395382152985525591)
                ·
                  refine ⟨12859949093073229478288387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8573299395382152985525591 12859949093073229478288387)
                  ·
                    refine ⟨19289923639609844217432581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12859949093073229478288387 19289923639609844217432581)
                    ·
                      refine ⟨3616860682426845790768609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19289923639609844217432581 3616860682426845790768609)
                      ·
                        rfl

theorem cell23_7043811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_7043811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043811 prefixEnd_7043811 := by exact prefixLift 7043811
  have htrace : WordTrace (prefixWord ++ tailWord_7043811) baseStart_7043811 baseEnd_7043811 := by
    simpa [prefixWord, tailWord_7043811, baseEnd_7043811] using wordTrace_append hprefix tailTrace_7043811
  have hstable : (prefixWord ++ tailWord_7043811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043811).length < 2 ^ (prefixWord ++ tailWord_7043811).sum := by decide
  have hdescent : baseEnd_7043811 < baseStart_7043811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043838 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_7043838 : Nat := 118140960795 + 7043838 * 2 ^ 59
def prefixEnd_7043838 : Nat := 4983230072969 + 3 ^ 40 * 7043838 * 2
def baseEnd_7043838 : Nat := 1205624848801505728376995

theorem tailTrace_7043838 : CollatzResearch.WordTrace tailWord_7043838 prefixEnd_7043838 1205624848801505728376995 := by
  unfold tailWord_7043838
  simp only [CollatzResearch.WordTrace]
  refine ⟨32113734731923174075055521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171273251903590261733629445 32113734731923174075055521)
  ·
    refine ⟨24085301048942380556291641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32113734731923174075055521 24085301048942380556291641)
    ·
      refine ⟨18063975786706785417218731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24085301048942380556291641 18063975786706785417218731)
      ·
        refine ⟨27095963680060178125828097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18063975786706785417218731 27095963680060178125828097)
        ·
          refine ⟨20321972760045133594371073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27095963680060178125828097 20321972760045133594371073)
          ·
            refine ⟨15241479570033850195778305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20321972760045133594371073 15241479570033850195778305)
            ·
              refine ⟨11431109677525387646833729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15241479570033850195778305 11431109677525387646833729)
              ·
                refine ⟨8573332258144040735125297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11431109677525387646833729 8573332258144040735125297)
                ·
                  refine ⟨6429999193608030551343973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8573332258144040735125297 6429999193608030551343973)
                  ·
                    refine ⟨1205624848801505728376995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6429999193608030551343973 1205624848801505728376995)
                    ·
                      rfl

theorem cell23_7043838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_7043838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043838 prefixEnd_7043838 := by exact prefixLift 7043838
  have htrace : WordTrace (prefixWord ++ tailWord_7043838) baseStart_7043838 baseEnd_7043838 := by
    simpa [prefixWord, tailWord_7043838, baseEnd_7043838] using wordTrace_append hprefix tailTrace_7043838
  have hstable : (prefixWord ++ tailWord_7043838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043838).length < 2 ^ (prefixWord ++ tailWord_7043838).sum := by decide
  have hdescent : baseEnd_7043838 < baseStart_7043838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043844 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_7043844 : Nat := 118140960795 + 7043844 * 2 ^ 59
def prefixEnd_7043844 : Nat := 4983230072969 + 3 ^ 40 * 7043844 * 2
def baseEnd_7043844 : Nat := 3616877627288444161655957

theorem tailTrace_7043844 : CollatzResearch.WordTrace tailWord_7043844 prefixEnd_7043844 3616877627288444161655957 := by
  unfold tailWord_7043844
  simp only [CollatzResearch.WordTrace]
  refine ⟨128455048346681827812581293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171273397795575770416775057 128455048346681827812581293)
  ·
    refine ⟨48170643130005685429717985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128455048346681827812581293 48170643130005685429717985)
    ·
      refine ⟨36127982347504264072288489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48170643130005685429717985 36127982347504264072288489)
      ·
        refine ⟨27095986760628198054216367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36127982347504264072288489 27095986760628198054216367)
        ·
          refine ⟨40643980140942297081324551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27095986760628198054216367 40643980140942297081324551)
          ·
            refine ⟨60965970211413445621986827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40643980140942297081324551 60965970211413445621986827)
            ·
              refine ⟨91448955317120168432980241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60965970211413445621986827 91448955317120168432980241)
              ·
                refine ⟨68586716487840126324735181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91448955317120168432980241 68586716487840126324735181)
                ·
                  refine ⟨25720018682940047371775693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68586716487840126324735181 25720018682940047371775693)
                  ·
                    refine ⟨9645007006102517764415885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25720018682940047371775693 9645007006102517764415885)
                    ·
                      refine ⟨3616877627288444161655957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9645007006102517764415885 3616877627288444161655957)
                      ·
                        rfl

theorem cell23_7043844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_7043844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043844 prefixEnd_7043844 := by exact prefixLift 7043844
  have htrace : WordTrace (prefixWord ++ tailWord_7043844) baseStart_7043844 baseEnd_7043844 := by
    simpa [prefixWord, tailWord_7043844, baseEnd_7043844] using wordTrace_append hprefix tailTrace_7043844
  have hstable : (prefixWord ++ tailWord_7043844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043844).length < 2 ^ (prefixWord ++ tailWord_7043844).sum := by decide
  have hdescent : baseEnd_7043844 < baseStart_7043844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043858 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_7043858 : Nat := 118140960795 + 7043858 * 2 ^ 59
def prefixEnd_7043858 : Nat := 4983230072969 + 3 ^ 40 * 7043858 * 2
def baseEnd_7043858 : Nat := 3616884816017607106880893

theorem tailTrace_7043858 : CollatzResearch.WordTrace tailWord_7043858 prefixEnd_7043858 3616884816017607106880893 := by
  unfold tailWord_7043858
  simp only [CollatzResearch.WordTrace]
  refine ⟨64227651828828234004043057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171273738210208624010781485 64227651828828234004043057)
  ·
    refine ⟨48170738871621175503032293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64227651828828234004043057 48170738871621175503032293)
    ·
      refine ⟨9032013538428970406818555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48170738871621175503032293 9032013538428970406818555)
      ·
        refine ⟨13548020307643455610227833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9032013538428970406818555 13548020307643455610227833)
        ·
          refine ⟨10161015230732591707670875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13548020307643455610227833 10161015230732591707670875)
          ·
            refine ⟨15241522846098887561506313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10161015230732591707670875 15241522846098887561506313)
            ·
              refine ⟨11431142134574165671129735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15241522846098887561506313 11431142134574165671129735)
              ·
                refine ⟨17146713201861248506694603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11431142134574165671129735 17146713201861248506694603)
                ·
                  refine ⟨25720069802791872760041905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17146713201861248506694603 25720069802791872760041905)
                  ·
                    refine ⟨19290052352093904570031429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25720069802791872760041905 19290052352093904570031429)
                    ·
                      refine ⟨3616884816017607106880893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19290052352093904570031429 3616884816017607106880893)
                      ·
                        rfl

theorem cell23_7043858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_7043858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043858 prefixEnd_7043858 := by exact prefixLift 7043858
  have htrace : WordTrace (prefixWord ++ tailWord_7043858) baseStart_7043858 baseEnd_7043858 := by
    simpa [prefixWord, tailWord_7043858, baseEnd_7043858] using wordTrace_append hprefix tailTrace_7043858
  have hstable : (prefixWord ++ tailWord_7043858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043858).length < 2 ^ (prefixWord ++ tailWord_7043858).sum := by decide
  have hdescent : baseEnd_7043858 < baseStart_7043858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043861 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_7043861 : Nat := 118140960795 + 7043861 * 2 ^ 59
def prefixEnd_7043861 : Nat := 4983230072969 + 3 ^ 40 * 7043861 * 2
def baseEnd_7043861 : Nat := 3616886356459570595143379

theorem tailTrace_7043861 : CollatzResearch.WordTrace tailWord_7043861 prefixEnd_7043861 3616886356459570595143379 := by
  unfold tailWord_7043861
  simp only [CollatzResearch.WordTrace]
  refine ⟨256910716734302067528531437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171273811156201378352354291 256910716734302067528531437)
  ·
    refine ⟨96341518775363275323199289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256910716734302067528531437 96341518775363275323199289)
    ·
      refine ⟨72256139081522456492399467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96341518775363275323199289 72256139081522456492399467)
      ·
        refine ⟨108384208622283684738599201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72256139081522456492399467 108384208622283684738599201)
        ·
          refine ⟨81288156466712763553949401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108384208622283684738599201 81288156466712763553949401)
          ·
            refine ⟨60966117350034572665462051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81288156466712763553949401 60966117350034572665462051)
            ·
              refine ⟨91449176025051858998193077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60966117350034572665462051 91449176025051858998193077)
              ·
                refine ⟨8573360252348611781080601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91449176025051858998193077 8573360252348611781080601)
                ·
                  refine ⟨6430020189261458835810451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8573360252348611781080601 6430020189261458835810451)
                  ·
                    refine ⟨9645030283892188253715677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6430020189261458835810451 9645030283892188253715677)
                    ·
                      refine ⟨3616886356459570595143379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9645030283892188253715677 3616886356459570595143379)
                      ·
                        rfl

theorem cell23_7043861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_7043861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043861 prefixEnd_7043861 := by exact prefixLift 7043861
  have htrace : WordTrace (prefixWord ++ tailWord_7043861) baseStart_7043861 baseEnd_7043861 := by
    simpa [prefixWord, tailWord_7043861, baseEnd_7043861] using wordTrace_append hprefix tailTrace_7043861
  have hstable : (prefixWord ++ tailWord_7043861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043861).length < 2 ^ (prefixWord ++ tailWord_7043861).sum := by decide
  have hdescent : baseEnd_7043861 < baseStart_7043861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043871 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 3, 3, 2]
def baseStart_7043871 : Nat := 118140960795 + 7043871 * 2 ^ 59
def prefixEnd_7043871 : Nat := 4983230072969 + 3 ^ 40 * 7043871 * 2
def baseEnd_7043871 : Nat := 3616891491266115556018333

theorem tailTrace_7043871 : CollatzResearch.WordTrace tailWord_7043871 prefixEnd_7043871 3616891491266115556018333 := by
  unfold tailWord_7043871
  simp only [CollatzResearch.WordTrace]
  refine ⟨256911081464265839236395467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171274054309510559490930311 256911081464265839236395467)
  ·
    refine ⟨385366622196398758854593201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256911081464265839236395467 385366622196398758854593201)
    ·
      refine ⟨289024966647299069140944901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385366622196398758854593201 289024966647299069140944901)
      ·
        refine ⟨54192181246368575463927169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289024966647299069140944901 54192181246368575463927169)
        ·
          refine ⟨40644135934776431597945377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54192181246368575463927169 40644135934776431597945377)
          ·
            refine ⟨30483101951082323698459033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40644135934776431597945377 30483101951082323698459033)
            ·
              refine ⟨22862326463311742773844275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30483101951082323698459033 22862326463311742773844275)
              ·
                refine ⟨34293489694967614160766413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22862326463311742773844275 34293489694967614160766413)
                ·
                  refine ⟨12860058635612855310287405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34293489694967614160766413 12860058635612855310287405)
                  ·
                    refine ⟨4822521988354820741357777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12860058635612855310287405 4822521988354820741357777)
                    ·
                      refine ⟨3616891491266115556018333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822521988354820741357777 3616891491266115556018333)
                      ·
                        rfl

theorem cell23_7043871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_7043871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043871 prefixEnd_7043871 := by exact prefixLift 7043871
  have htrace : WordTrace (prefixWord ++ tailWord_7043871) baseStart_7043871 baseEnd_7043871 := by
    simpa [prefixWord, tailWord_7043871, baseEnd_7043871] using wordTrace_append hprefix tailTrace_7043871
  have hstable : (prefixWord ++ tailWord_7043871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043871).length < 2 ^ (prefixWord ++ tailWord_7043871).sum := by decide
  have hdescent : baseEnd_7043871 < baseStart_7043871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043877 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_7043877 : Nat := 118140960795 + 7043877 * 2 ^ 59
def prefixEnd_7043877 : Nat := 4983230072969 + 3 ^ 40 * 7043877 * 2
def baseEnd_7043877 : Nat := 1205631524050014177514435

theorem tailTrace_7043877 : CollatzResearch.WordTrace tailWord_7043877 prefixEnd_7043877 1205631524050014177514435 := by
  unfold tailWord_7043877
  simp only [CollatzResearch.WordTrace]
  refine ⟨256911300302244102261113885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171274200201496068174075923 256911300302244102261113885)
  ·
    refine ⟨96341737613341538347917707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256911300302244102261113885 96341737613341538347917707)
    ·
      refine ⟨144512606420012307521876561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96341737613341538347917707 144512606420012307521876561)
      ·
        refine ⟨108384454815009230641407421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144512606420012307521876561 108384454815009230641407421)
        ·
          refine ⟨40644170555628461490527783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108384454815009230641407421 40644170555628461490527783)
          ·
            refine ⟨60966255833442692235791675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40644170555628461490527783 60966255833442692235791675)
            ·
              refine ⟨91449383750164038353687513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60966255833442692235791675 91449383750164038353687513)
              ·
                refine ⟨68587037812623028765265635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91449383750164038353687513 68587037812623028765265635)
                ·
                  refine ⟨102880556718934543147898453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68587037812623028765265635 102880556718934543147898453)
                  ·
                    refine ⟨1205631524050014177514435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102880556718934543147898453 1205631524050014177514435)
                    ·
                      rfl

theorem cell23_7043877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_7043877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043877 prefixEnd_7043877 := by exact prefixLift 7043877
  have htrace : WordTrace (prefixWord ++ tailWord_7043877) baseStart_7043877 baseEnd_7043877 := by
    simpa [prefixWord, tailWord_7043877, baseEnd_7043877] using wordTrace_append hprefix tailTrace_7043877
  have hstable : (prefixWord ++ tailWord_7043877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043877).length < 2 ^ (prefixWord ++ tailWord_7043877).sum := by decide
  have hdescent : baseEnd_7043877 < baseStart_7043877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043882 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7043882 : Nat := 118140960795 + 7043882 * 2 ^ 59
def prefixEnd_7043882 : Nat := 4983230072969 + 3 ^ 40 * 7043882 * 2
def baseEnd_7043882 : Nat := 3616897139553315012980783

theorem tailTrace_7043882 : CollatzResearch.WordTrace tailWord_7043882 prefixEnd_7043882 3616897139553315012980783 := by
  unfold tailWord_7043882
  simp only [CollatzResearch.WordTrace]
  refine ⟨64227870666806497028761475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171274321778150658743363933 64227870666806497028761475)
  ·
    refine ⟨96341806000209745543142213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64227870666806497028761475 96341806000209745543142213)
    ·
      refine ⟨18064088625039327289339165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96341806000209745543142213 18064088625039327289339165)
      ·
        refine ⟨6774033234389747733502187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18064088625039327289339165 6774033234389747733502187)
        ·
          refine ⟨10161049851584621600253281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6774033234389747733502187 10161049851584621600253281)
          ·
            refine ⟨7620787388688466200189961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10161049851584621600253281 7620787388688466200189961)
            ·
              refine ⟨5715590541516349650142471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7620787388688466200189961 5715590541516349650142471)
              ·
                refine ⟨8573385812274524475213707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5715590541516349650142471 8573385812274524475213707)
                ·
                  refine ⟨12860078718411786712820561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8573385812274524475213707 12860078718411786712820561)
                  ·
                    refine ⟨9645059038808840034615421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12860078718411786712820561 9645059038808840034615421)
                    ·
                      refine ⟨3616897139553315012980783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9645059038808840034615421 3616897139553315012980783)
                      ·
                        rfl

theorem cell23_7043882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7043882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043882 prefixEnd_7043882 := by exact prefixLift 7043882
  have htrace : WordTrace (prefixWord ++ tailWord_7043882) baseStart_7043882 baseEnd_7043882 := by
    simpa [prefixWord, tailWord_7043882, baseEnd_7043882] using wordTrace_append hprefix tailTrace_7043882
  have hstable : (prefixWord ++ tailWord_7043882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043882).length < 2 ^ (prefixWord ++ tailWord_7043882).sum := by decide
  have hdescent : baseEnd_7043882 < baseStart_7043882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043918 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2]
def baseStart_7043918 : Nat := 118140960795 + 7043918 * 2 ^ 59
def prefixEnd_7043918 : Nat := 4983230072969 + 3 ^ 40 * 7043918 * 2
def baseEnd_7043918 : Nat := 3616915624856876872130617

theorem tailTrace_7043918 : CollatzResearch.WordTrace tailWord_7043918 prefixEnd_7043918 3616915624856876872130617 := by
  unfold tailWord_7043918
  simp only [CollatzResearch.WordTrace]
  refine ⟨32114099461886945782919551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171275197130063710842237605 32114099461886945782919551)
  ·
    refine ⟨48171149192830418674379327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32114099461886945782919551 48171149192830418674379327)
    ·
      refine ⟨72256723789245628011568991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48171149192830418674379327 72256723789245628011568991)
      ·
        refine ⟨108385085683868442017353487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72256723789245628011568991 108385085683868442017353487)
        ·
          refine ⟨162577628525802663026030231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108385085683868442017353487 162577628525802663026030231)
          ·
            refine ⟨243866442788703994539045347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162577628525802663026030231 243866442788703994539045347)
            ·
              refine ⟨365799664183055991808568021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243866442788703994539045347 365799664183055991808568021)
              ·
                refine ⟨8573429629290374808013313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 365799664183055991808568021 8573429629290374808013313)
                ·
                  refine ⟨6430072221967781106009985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8573429629290374808013313 6430072221967781106009985)
                  ·
                    refine ⟨4822554166475835829507489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6430072221967781106009985 4822554166475835829507489)
                    ·
                      refine ⟨3616915624856876872130617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822554166475835829507489 3616915624856876872130617)
                      ·
                        rfl

theorem cell23_7043918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_7043918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043918 prefixEnd_7043918 := by exact prefixLift 7043918
  have htrace : WordTrace (prefixWord ++ tailWord_7043918) baseStart_7043918 baseEnd_7043918 := by
    simpa [prefixWord, tailWord_7043918, baseEnd_7043918] using wordTrace_append hprefix tailTrace_7043918
  have hstable : (prefixWord ++ tailWord_7043918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043918).length < 2 ^ (prefixWord ++ tailWord_7043918).sum := by decide
  have hdescent : baseEnd_7043918 < baseStart_7043918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043941 : List Nat := [1, 3, 1, 3, 1, 1, 5, 3, 5]
def baseStart_7043941 : Nat := 118140960795 + 7043941 * 2 ^ 59
def prefixEnd_7043941 : Nat := 4983230072969 + 3 ^ 40 * 7043941 * 2
def baseEnd_7043941 : Nat := 401880826101325586904779

theorem tailTrace_7043941 : CollatzResearch.WordTrace tailWord_7043941 prefixEnd_7043941 401880826101325586904779 := by
  unfold tailWord_7043941
  simp only [CollatzResearch.WordTrace]
  refine ⟨256913634574012241191443677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171275756382674827460962451 256913634574012241191443677)
  ·
    refine ⟨96342612965254590446791379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256913634574012241191443677 96342612965254590446791379)
    ·
      refine ⟨144513919447881885670187069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96342612965254590446791379 144513919447881885670187069)
      ·
        refine ⟨54192719792955707126320151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144513919447881885670187069 54192719792955707126320151)
        ·
          refine ⟨81289079689433560689480227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54192719792955707126320151 81289079689433560689480227)
          ·
            refine ⟨121933619534150341034220341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81289079689433560689480227 121933619534150341034220341)
            ·
              refine ⟨11431276831326594471958157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121933619534150341034220341 11431276831326594471958157)
              ·
                refine ⟨4286728811747472926984309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11431276831326594471958157 4286728811747472926984309)
                ·
                  refine ⟨401880826101325586904779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4286728811747472926984309 401880826101325586904779)
                  ·
                    rfl

theorem cell23_7043941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_7043941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043941 prefixEnd_7043941 := by exact prefixLift 7043941
  have htrace : WordTrace (prefixWord ++ tailWord_7043941) baseStart_7043941 baseEnd_7043941 := by
    simpa [prefixWord, tailWord_7043941, baseEnd_7043941] using wordTrace_append hprefix tailTrace_7043941
  have hstable : (prefixWord ++ tailWord_7043941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043941).length < 2 ^ (prefixWord ++ tailWord_7043941).sum := by decide
  have hdescent : baseEnd_7043941 < baseStart_7043941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043954 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_7043954 : Nat := 118140960795 + 7043954 * 2 ^ 59
def prefixEnd_7043954 : Nat := 4983230072969 + 3 ^ 40 * 7043954 * 2
def baseEnd_7043954 : Nat := 1205644703386812910426817

theorem tailTrace_7043954 : CollatzResearch.WordTrace tailWord_7043954 prefixEnd_7043954 1205644703386812910426817 := by
  unfold tailWord_7043954
  simp only [CollatzResearch.WordTrace]
  refine ⟨64228527180741286102916729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171276072481976762941111277 64228527180741286102916729)
  ·
    refine ⟨48171395385555964577187547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64228527180741286102916729 48171395385555964577187547)
    ·
      refine ⟨72257093078333946865781321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48171395385555964577187547 72257093078333946865781321)
      ·
        refine ⟨54192819808750460149335991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72257093078333946865781321 54192819808750460149335991)
        ·
          refine ⟨81289229713125690224003987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54192819808750460149335991 81289229713125690224003987)
          ·
            refine ⟨121933844569688535336005981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81289229713125690224003987 121933844569688535336005981)
            ·
              refine ⟨45725191713633200751002243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121933844569688535336005981 45725191713633200751002243)
              ·
                refine ⟨68587787570449801126503365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45725191713633200751002243 68587787570449801126503365)
                ·
                  refine ⟨12860210169459337711219381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68587787570449801126503365 12860210169459337711219381)
                  ·
                    refine ⟨1205644703386812910426817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12860210169459337711219381 1205644703386812910426817)
                    ·
                      rfl

theorem cell23_7043954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_7043954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043954 prefixEnd_7043954 := by exact prefixLift 7043954
  have htrace : WordTrace (prefixWord ++ tailWord_7043954) baseStart_7043954 baseEnd_7043954 := by
    simpa [prefixWord, tailWord_7043954, baseEnd_7043954] using wordTrace_append hprefix tailTrace_7043954
  have hstable : (prefixWord ++ tailWord_7043954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043954).length < 2 ^ (prefixWord ++ tailWord_7043954).sum := by decide
  have hdescent : baseEnd_7043954 < baseStart_7043954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043958 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_7043958 : Nat := 118140960795 + 7043958 * 2 ^ 59
def prefixEnd_7043958 : Nat := 4983230072969 + 3 ^ 40 * 7043958 * 2
def baseEnd_7043958 : Nat := 401881796009228523958937

theorem tailTrace_7043958 : CollatzResearch.WordTrace tailWord_7043958 prefixEnd_7043958 401881796009228523958937 := by
  unfold tailWord_7043958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16057140913434415818425783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171276169743300435396541685 16057140913434415818425783)
  ·
    refine ⟨24085711370151623727638675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16057140913434415818425783 24085711370151623727638675)
    ·
      refine ⟨36128567055227435591458013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24085711370151623727638675 36128567055227435591458013)
      ·
        refine ⟨13548212645710288346796755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36128567055227435591458013 13548212645710288346796755)
        ·
          refine ⟨20322318968565432520195133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13548212645710288346796755 20322318968565432520195133)
          ·
            refine ⟨7620869613212037195073175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20322318968565432520195133 7620869613212037195073175)
            ·
              refine ⟨11431304419818055792609763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7620869613212037195073175 11431304419818055792609763)
              ·
                refine ⟨17146956629727083688914645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11431304419818055792609763 17146956629727083688914645)
                ·
                  refine ⟨401881796009228523958937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17146956629727083688914645 401881796009228523958937)
                  ·
                    rfl

theorem cell23_7043958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_7043958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043958 prefixEnd_7043958 := by exact prefixLift 7043958
  have htrace : WordTrace (prefixWord ++ tailWord_7043958) baseStart_7043958 baseEnd_7043958 := by
    simpa [prefixWord, tailWord_7043958, baseEnd_7043958] using wordTrace_append hprefix tailTrace_7043958
  have hstable : (prefixWord ++ tailWord_7043958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043958).length < 2 ^ (prefixWord ++ tailWord_7043958).sum := by decide
  have hdescent : baseEnd_7043958 < baseStart_7043958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7043991 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 4]
def baseStart_7043991 : Nat := 118140960795 + 7043991 * 2 ^ 59
def prefixEnd_7043991 : Nat := 4983230072969 + 3 ^ 40 * 7043991 * 2
def baseEnd_7043991 : Nat := 3616953108944655086517781

theorem tailTrace_7043991 : CollatzResearch.WordTrace tailWord_7043991 prefixEnd_7043991 3616953108944655086517781 := by
  unfold tailWord_7043991
  simp only [CollatzResearch.WordTrace]
  refine ⟨256915458223831099730763827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171276972149220733153842551 256915458223831099730763827)
  ·
    refine ⟨385373187335746649596145741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256915458223831099730763827 385373187335746649596145741)
    ·
      refine ⟨144514945250904993598554653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385373187335746649596145741 144514945250904993598554653)
      ·
        refine ⟨54193104469089372599457995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144514945250904993598554653 54193104469089372599457995)
        ·
          refine ⟨81289656703634058899186993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54193104469089372599457995 81289656703634058899186993)
          ·
            refine ⟨60967242527725544174390245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81289656703634058899186993 60967242527725544174390245)
            ·
              refine ⟨11431357973948539532698171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60967242527725544174390245 11431357973948539532698171)
              ·
                refine ⟨17147036960922809299047257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11431357973948539532698171 17147036960922809299047257)
                ·
                  refine ⟨12860277720692106974285443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17147036960922809299047257 12860277720692106974285443)
                  ·
                    refine ⟨19290416581038160461428165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12860277720692106974285443 19290416581038160461428165)
                    ·
                      refine ⟨3616953108944655086517781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19290416581038160461428165 3616953108944655086517781)
                      ·
                        rfl

theorem cell23_7043991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_7043991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7043991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7043991 prefixEnd_7043991 := by exact prefixLift 7043991
  have htrace : WordTrace (prefixWord ++ tailWord_7043991) baseStart_7043991 baseEnd_7043991 := by
    simpa [prefixWord, tailWord_7043991, baseEnd_7043991] using wordTrace_append hprefix tailTrace_7043991
  have hstable : (prefixWord ++ tailWord_7043991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7043991).length < 2 ^ (prefixWord ++ tailWord_7043991).sum := by decide
  have hdescent : baseEnd_7043991 < baseStart_7043991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7043991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044004 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_7044004 : Nat := 118140960795 + 7044004 * 2 ^ 59
def prefixEnd_7044004 : Nat := 4983230072969 + 3 ^ 40 * 7044004 * 2
def baseEnd_7044004 : Nat := 3616959784193163535655221

theorem tailTrace_7044004 : CollatzResearch.WordTrace tailWord_7044004 prefixEnd_7044004 3616959784193163535655221 := by
  unfold tailWord_7044004
  simp only [CollatzResearch.WordTrace]
  refine ⟨128457966186392001475493533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171277288248522668633991377 128457966186392001475493533)
  ·
    refine ⟨48171737319897000553310075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128457966186392001475493533 48171737319897000553310075)
    ·
      refine ⟨72257605979845500829965113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48171737319897000553310075 72257605979845500829965113)
      ·
        refine ⟨54193204484884125622473835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72257605979845500829965113 54193204484884125622473835)
        ·
          refine ⟨81289806727326188433710753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54193204484884125622473835 81289806727326188433710753)
          ·
            refine ⟨60967355045494641325283065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81289806727326188433710753 60967355045494641325283065)
            ·
              refine ⟨45725516284120980993962299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60967355045494641325283065 45725516284120980993962299)
              ·
                refine ⟨68588274426181471490943449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45725516284120980993962299 68588274426181471490943449)
                ·
                  refine ⟨51441205819636103618207587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68588274426181471490943449 51441205819636103618207587)
                  ·
                    refine ⟨77161808729454155427311381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51441205819636103618207587 77161808729454155427311381)
                    ·
                      refine ⟨3616959784193163535655221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77161808729454155427311381 3616959784193163535655221)
                      ·
                        rfl

theorem cell23_7044004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_7044004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044004 prefixEnd_7044004 := by exact prefixLift 7044004
  have htrace : WordTrace (prefixWord ++ tailWord_7044004) baseStart_7044004 baseEnd_7044004 := by
    simpa [prefixWord, tailWord_7044004, baseEnd_7044004] using wordTrace_append hprefix tailTrace_7044004
  have hstable : (prefixWord ++ tailWord_7044004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044004).length < 2 ^ (prefixWord ++ tailWord_7044004).sum := by decide
  have hdescent : baseEnd_7044004 < baseStart_7044004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044132 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 3, 2, 2]
def baseStart_7044132 : Nat := 118140960795 + 7044132 * 2 ^ 59
def prefixEnd_7044132 : Nat := 4983230072969 + 3 ^ 40 * 7044132 * 2
def baseEnd_7044132 : Nat := 3617025509716939034854633

theorem tailTrace_7044132 : CollatzResearch.WordTrace tailWord_7044132 prefixEnd_7044132 3617025509716939034854633 := by
  unfold tailWord_7044132
  simp only [CollatzResearch.WordTrace]
  refine ⟨128460300458160140405823325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171280400610880187207764433 128460300458160140405823325)
  ·
    refine ⟨48172612671810052652183747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128460300458160140405823325 48172612671810052652183747)
    ·
      refine ⟨72258919007715078978275621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48172612671810052652183747 72258919007715078978275621)
      ·
        refine ⟨13548547313946577308426679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72258919007715078978275621 13548547313946577308426679)
        ·
          refine ⟨20322820970919865962640019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13548547313946577308426679 20322820970919865962640019)
          ·
            refine ⟨30484231456379798943960029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20322820970919865962640019 30484231456379798943960029)
            ·
              refine ⟨11431586796142424603985011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30484231456379798943960029 11431586796142424603985011)
              ·
                refine ⟨17147380194213636905977517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11431586796142424603985011 17147380194213636905977517)
                ·
                  refine ⟨6430267572830113839741569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17147380194213636905977517 6430267572830113839741569)
                  ·
                    refine ⟨4822700679622585379806177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6430267572830113839741569 4822700679622585379806177)
                    ·
                      refine ⟨3617025509716939034854633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822700679622585379806177 3617025509716939034854633)
                      ·
                        rfl

theorem cell23_7044132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_7044132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044132 prefixEnd_7044132 := by exact prefixLift 7044132
  have htrace : WordTrace (prefixWord ++ tailWord_7044132) baseStart_7044132 baseEnd_7044132 := by
    simpa [prefixWord, tailWord_7044132, baseEnd_7044132] using wordTrace_append hprefix tailTrace_7044132
  have hstable : (prefixWord ++ tailWord_7044132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044132).length < 2 ^ (prefixWord ++ tailWord_7044132).sum := by decide
  have hdescent : baseEnd_7044132 < baseStart_7044132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044138 : List Nat := [3, 1, 4, 1, 3, 1, 2, 8]
def baseStart_7044138 : Nat := 118140960795 + 7044138 * 2 ^ 59
def prefixEnd_7044138 : Nat := 4983230072969 + 3 ^ 40 * 7044138 * 2
def baseEnd_7044138 : Nat := 133964021874106148569615

theorem tailTrace_7044138 : CollatzResearch.WordTrace tailWord_7044138 prefixEnd_7044138 133964021874106148569615 := by
  unfold tailWord_7044138
  simp only [CollatzResearch.WordTrace]
  refine ⟨64230204938574635959091267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171280546502865695890910045 64230204938574635959091267)
  ·
    refine ⟨96345307407861953938636901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64230204938574635959091267 96345307407861953938636901)
    ·
      refine ⟨18064745138974116363494419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96345307407861953938636901 18064745138974116363494419)
      ·
        refine ⟨27097117708461174545241629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18064745138974116363494419 27097117708461174545241629)
        ·
          refine ⟨10161419140672940454465611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27097117708461174545241629 10161419140672940454465611)
          ·
            refine ⟨15242128711009410681698417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10161419140672940454465611 15242128711009410681698417)
            ·
              refine ⟨11431596533257058011273813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15242128711009410681698417 11431596533257058011273813)
              ·
                refine ⟨133964021874106148569615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11431596533257058011273813 133964021874106148569615)
                ·
                  rfl

theorem cell23_7044138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 8].length) (baseStart_7044138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044138 prefixEnd_7044138 := by exact prefixLift 7044138
  have htrace : WordTrace (prefixWord ++ tailWord_7044138) baseStart_7044138 baseEnd_7044138 := by
    simpa [prefixWord, tailWord_7044138, baseEnd_7044138] using wordTrace_append hprefix tailTrace_7044138
  have hstable : (prefixWord ++ tailWord_7044138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044138).length < 2 ^ (prefixWord ++ tailWord_7044138).sum := by decide
  have hdescent : baseEnd_7044138 < baseStart_7044138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044181 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_7044181 : Nat := 118140960795 + 7044181 * 2 ^ 59
def prefixEnd_7044181 : Nat := 4983230072969 + 3 ^ 40 * 7044181 * 2
def baseEnd_7044181 : Nat := 1205683556756336447713969

theorem tailTrace_7044181 : CollatzResearch.WordTrace tailWord_7044181 prefixEnd_7044181 1205683556756336447713969 := by
  unfold tailWord_7044181
  simp only [CollatzResearch.WordTrace]
  refine ⟨256922388093142762180180397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171281592062095174786786931 256922388093142762180180397)
  ·
    refine ⟨96345895534928535817567649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256922388093142762180180397 96345895534928535817567649)
    ·
      refine ⟨72259421651196401863175737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96345895534928535817567649 72259421651196401863175737)
      ·
        refine ⟨54194566238397301397381803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72259421651196401863175737 54194566238397301397381803)
        ·
          refine ⟨81291849357595952096072705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54194566238397301397381803 81291849357595952096072705)
          ·
            refine ⟨60968887018196964072054529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81291849357595952096072705 60968887018196964072054529)
            ·
              refine ⟨45726665263647723054040897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60968887018196964072054529 45726665263647723054040897)
              ·
                refine ⟨34294998947735792290530673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45726665263647723054040897 34294998947735792290530673)
                ·
                  refine ⟨25721249210801844217898005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34294998947735792290530673 25721249210801844217898005)
                  ·
                    refine ⟨1205683556756336447713969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25721249210801844217898005 1205683556756336447713969)
                    ·
                      rfl

theorem cell23_7044181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_7044181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044181 prefixEnd_7044181 := by exact prefixLift 7044181
  have htrace : WordTrace (prefixWord ++ tailWord_7044181) baseStart_7044181 baseEnd_7044181 := by
    simpa [prefixWord, tailWord_7044181, baseEnd_7044181] using wordTrace_append hprefix tailTrace_7044181
  have hstable : (prefixWord ++ tailWord_7044181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044181).length < 2 ^ (prefixWord ++ tailWord_7044181).sum := by decide
  have hdescent : baseEnd_7044181 < baseStart_7044181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044191 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 3]
def baseStart_7044191 : Nat := 118140960795 + 7044191 * 2 ^ 59
def prefixEnd_7044191 : Nat := 4983230072969 + 3 ^ 40 * 7044191 * 2
def baseEnd_7044191 : Nat := 3617055805075554304016861

theorem tailTrace_7044191 : CollatzResearch.WordTrace tailWord_7044191 prefixEnd_7044191 3617055805075554304016861 := by
  unfold tailWord_7044191
  simp only [CollatzResearch.WordTrace]
  refine ⟨256922752823106533888044427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171281835215404355925362951 256922752823106533888044427)
  ·
    refine ⟨385384129234659800832066641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256922752823106533888044427 385384129234659800832066641)
    ·
      refine ⟨289038096925994850624049981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385384129234659800832066641 289038096925994850624049981)
      ·
        refine ⟨108389286347248068984018743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289038096925994850624049981 108389286347248068984018743)
        ·
          refine ⟨162583929520872103476028115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108389286347248068984018743 162583929520872103476028115)
          ·
            refine ⟨243875894281308155214042173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162583929520872103476028115 243875894281308155214042173)
            ·
              refine ⟨91453460355490558205265815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243875894281308155214042173 91453460355490558205265815)
              ·
                refine ⟨137180190533235837307898723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91453460355490558205265815 137180190533235837307898723)
                ·
                  refine ⟨205770285799853755961848085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137180190533235837307898723 205770285799853755961848085)
                  ·
                    refine ⟨9645482146868144810711629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 205770285799853755961848085 9645482146868144810711629)
                    ·
                      refine ⟨3617055805075554304016861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9645482146868144810711629 3617055805075554304016861)
                      ·
                        rfl

theorem cell23_7044191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_7044191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044191 prefixEnd_7044191 := by exact prefixLift 7044191
  have htrace : WordTrace (prefixWord ++ tailWord_7044191) baseStart_7044191 baseEnd_7044191 := by
    simpa [prefixWord, tailWord_7044191, baseEnd_7044191] using wordTrace_append hprefix tailTrace_7044191
  have hstable : (prefixWord ++ tailWord_7044191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044191).length < 2 ^ (prefixWord ++ tailWord_7044191).sum := by decide
  have hdescent : baseEnd_7044191 < baseStart_7044191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044201 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_7044201 : Nat := 118140960795 + 7044201 * 2 ^ 59
def prefixEnd_7044201 : Nat := 4983230072969 + 3 ^ 40 * 7044201 * 2
def baseEnd_7044201 : Nat := 3617060939882099264891815

theorem tailTrace_7044201 : CollatzResearch.WordTrace tailWord_7044201 prefixEnd_7044201 3617060939882099264891815 := by
  unfold tailWord_7044201
  simp only [CollatzResearch.WordTrace]
  refine ⟨256923117553070305595908457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171282078368713537063938971 256923117553070305595908457)
  ·
    refine ⟨192692338164802729196931343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256923117553070305595908457 192692338164802729196931343)
    ·
      refine ⟨289038507247204093795397015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192692338164802729196931343 289038507247204093795397015)
      ·
        refine ⟨433557760870806140693095523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289038507247204093795397015 433557760870806140693095523)
        ·
          refine ⟨650336641306209211039643285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433557760870806140693095523 650336641306209211039643285)
          ·
            refine ⟨30484530061228556767483279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 650336641306209211039643285 30484530061228556767483279)
            ·
              refine ⟨45726795091842835151224919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30484530061228556767483279 45726795091842835151224919)
              ·
                refine ⟨68590192637764252726837379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45726795091842835151224919 68590192637764252726837379)
                ·
                  refine ⟨102885288956646379090256069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68590192637764252726837379 102885288956646379090256069)
                  ·
                    refine ⟨19290991679371196079423013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102885288956646379090256069 19290991679371196079423013)
                    ·
                      refine ⟨3617060939882099264891815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19290991679371196079423013 3617060939882099264891815)
                      ·
                        rfl

theorem cell23_7044201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_7044201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044201 prefixEnd_7044201 := by exact prefixLift 7044201
  have htrace : WordTrace (prefixWord ++ tailWord_7044201) baseStart_7044201 baseEnd_7044201 := by
    simpa [prefixWord, tailWord_7044201, baseEnd_7044201] using wordTrace_append hprefix tailTrace_7044201
  have hstable : (prefixWord ++ tailWord_7044201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044201).length < 2 ^ (prefixWord ++ tailWord_7044201).sum := by decide
  have hdescent : baseEnd_7044201 < baseStart_7044201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7044205 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_7044205 : Nat := 118140960795 + 7044205 * 2 ^ 59
def prefixEnd_7044205 : Nat := 4983230072969 + 3 ^ 40 * 7044205 * 2
def baseEnd_7044205 : Nat := 3617062993804717249241797

theorem tailTrace_7044205 : CollatzResearch.WordTrace tailWord_7044205 prefixEnd_7044205 3617062993804717249241797 := by
  unfold tailWord_7044205
  simp only [CollatzResearch.WordTrace]
  refine ⟨256923263445055814279054069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171282175630037209519369379 256923263445055814279054069)
  ·
    refine ⟨24086555947973982588661319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256923263445055814279054069 24086555947973982588661319)
    ·
      refine ⟨36129833921960973882991979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24086555947973982588661319 36129833921960973882991979)
      ·
        refine ⟨54194750882941460824487969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36129833921960973882991979 54194750882941460824487969)
        ·
          refine ⟨40646063162206095618365977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54194750882941460824487969 40646063162206095618365977)
          ·
            refine ⟨30484547371654571713774483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40646063162206095618365977 30484547371654571713774483)
            ·
              refine ⟨45726821057481857570661725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30484547371654571713774483 45726821057481857570661725)
              ·
                refine ⟨17147557896555696588998147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45726821057481857570661725 17147557896555696588998147)
                ·
                  refine ⟨25721336844833544883497221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17147557896555696588998147 25721336844833544883497221)
                  ·
                    refine ⟨4822750658406289665655729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25721336844833544883497221 4822750658406289665655729)
                    ·
                      refine ⟨3617062993804717249241797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4822750658406289665655729 3617062993804717249241797)
                      ·
                        rfl

theorem cell23_7044205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_7044205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7044205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7044205 prefixEnd_7044205 := by exact prefixLift 7044205
  have htrace : WordTrace (prefixWord ++ tailWord_7044205) baseStart_7044205 baseEnd_7044205 := by
    simpa [prefixWord, tailWord_7044205, baseEnd_7044205] using wordTrace_append hprefix tailTrace_7044205
  have hstable : (prefixWord ++ tailWord_7044205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7044205).length < 2 ^ (prefixWord ++ tailWord_7044205).sum := by decide
  have hdescent : baseEnd_7044205 < baseStart_7044205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7044205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
