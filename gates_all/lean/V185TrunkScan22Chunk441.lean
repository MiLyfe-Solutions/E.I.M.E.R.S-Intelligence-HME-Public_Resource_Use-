import V185TrunkScan22Chunk440

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3931342 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_3931342 : Nat := 118140960795 + 3931342 * 2 ^ 59
def prefixEnd_3931342 : Nat := 4983230072969 + 3 ^ 40 * 3931342 * 2
def baseEnd_3931342 : Nat := 1345778708805375226696729

theorem tailTrace_3931342 : CollatzResearch.WordTrace tailWord_3931342 prefixEnd_3931342 1345778708805375226696729 := by
  unfold tailWord_3931342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17923477815428353575531535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95591881682284552402834853 17923477815428353575531535)
  ·
    refine ⟨26885216723142530363297303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17923477815428353575531535 26885216723142530363297303)
    ·
      refine ⟨40327825084713795544945955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26885216723142530363297303 40327825084713795544945955)
      ·
        refine ⟨60491737627070693317418933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40327825084713795544945955 60491737627070693317418933)
        ·
          refine ⟨5671100402537877498508025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60491737627070693317418933 5671100402537877498508025)
          ·
            refine ⟨4253325301903408123881019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5671100402537877498508025 4253325301903408123881019)
            ·
              refine ⟨6379987952855112185821529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4253325301903408123881019 6379987952855112185821529)
              ·
                refine ⟨4784990964641334139366147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6379987952855112185821529 4784990964641334139366147)
                ·
                  refine ⟨7177486446962001209049221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784990964641334139366147 7177486446962001209049221)
                  ·
                    refine ⟨1345778708805375226696729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7177486446962001209049221 1345778708805375226696729)
                    ·
                      rfl

theorem cell22_3931342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_3931342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931342 prefixEnd_3931342 := by exact prefixLift 3931342
  have htrace : WordTrace (prefixWord ++ tailWord_3931342) baseStart_3931342 baseEnd_3931342 := by
    simpa [prefixWord, tailWord_3931342, baseEnd_3931342] using wordTrace_append hprefix tailTrace_3931342
  have hstable : (prefixWord ++ tailWord_3931342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931342).length < 2 ^ (prefixWord ++ tailWord_3931342).sum := by decide
  have hdescent : baseEnd_3931342 < baseStart_3931342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931351 : List Nat := [1, 1, 3, 2, 1, 2, 4, 8]
def baseStart_3931351 : Nat := 118140960795 + 3931351 * 2 ^ 59
def prefixEnd_3931351 : Nat := 4983230072969 + 3 ^ 40 * 3931351 * 2
def baseEnd_3931351 : Nat := 149531309965478022580189

theorem tailTrace_3931351 : CollatzResearch.WordTrace tailWord_3931351 prefixEnd_3931351 149531309965478022580189 := by
  unfold tailWord_3931351
  simp only [CollatzResearch.WordTrace]
  refine ⟨143388150780394223141329907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95592100520262815427553271 143388150780394223141329907)
  ·
    refine ⟨215082226170591334711994861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143388150780394223141329907 215082226170591334711994861)
    ·
      refine ⟨80655834813971750516998073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215082226170591334711994861 80655834813971750516998073)
      ·
        refine ⟨60491876110478812887748555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80655834813971750516998073 60491876110478812887748555)
        ·
          refine ⟨90737814165718219331622833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60491876110478812887748555 90737814165718219331622833)
          ·
            refine ⟨68053360624288664498717125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90737814165718219331622833 68053360624288664498717125)
            ·
              refine ⟨12760005117054124593509461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68053360624288664498717125 12760005117054124593509461)
              ·
                refine ⟨149531309965478022580189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12760005117054124593509461 149531309965478022580189)
                ·
                  rfl

theorem cell22_3931351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 8].length) (baseStart_3931351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931351 prefixEnd_3931351 := by exact prefixLift 3931351
  have htrace : WordTrace (prefixWord ++ tailWord_3931351) baseStart_3931351 baseEnd_3931351 := by
    simpa [prefixWord, tailWord_3931351, baseEnd_3931351] using wordTrace_append hprefix tailTrace_3931351
  have hstable : (prefixWord ++ tailWord_3931351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931351).length < 2 ^ (prefixWord ++ tailWord_3931351).sum := by decide
  have hdescent : baseEnd_3931351 < baseStart_3931351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931428 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_3931428 : Nat := 118140960795 + 3931428 * 2 ^ 59
def prefixEnd_3931428 : Nat := 4983230072969 + 3 ^ 40 * 3931428 * 2
def baseEnd_3931428 : Nat := 1345808148362899669046465

theorem tailTrace_3931428 : CollatzResearch.WordTrace tailWord_3931428 prefixEnd_3931428 1345808148362899669046465 := by
  unfold tailWord_3931428
  simp only [CollatzResearch.WordTrace]
  refine ⟨71695479600557632645941469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95593972800743510194588625 71695479600557632645941469)
  ·
    refine ⟨26885804850209112242228051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71695479600557632645941469 26885804850209112242228051)
    ·
      refine ⟨40328707275313668363342077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26885804850209112242228051 40328707275313668363342077)
      ·
        refine ⟨15123265228242625636253279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40328707275313668363342077 15123265228242625636253279)
        ·
          refine ⟨22684897842363938454379919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15123265228242625636253279 22684897842363938454379919)
          ·
            refine ⟨34027346763545907681569879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22684897842363938454379919 34027346763545907681569879)
            ·
              refine ⟨51041020145318861522354819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34027346763545907681569879 51041020145318861522354819)
              ·
                refine ⟨76561530217978292283532229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51041020145318861522354819 76561530217978292283532229)
                ·
                  refine ⟨14355286915870929803162293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76561530217978292283532229 14355286915870929803162293)
                  ·
                    refine ⟨1345808148362899669046465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14355286915870929803162293 1345808148362899669046465)
                    ·
                      rfl

theorem cell22_3931428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_3931428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931428 prefixEnd_3931428 := by exact prefixLift 3931428
  have htrace : WordTrace (prefixWord ++ tailWord_3931428) baseStart_3931428 baseEnd_3931428 := by
    simpa [prefixWord, tailWord_3931428, baseEnd_3931428] using wordTrace_append hprefix tailTrace_3931428
  have hstable : (prefixWord ++ tailWord_3931428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931428).length < 2 ^ (prefixWord ++ tailWord_3931428).sum := by decide
  have hdescent : baseEnd_3931428 < baseStart_3931428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931434 : List Nat := [3, 1, 4, 2, 1, 1, 2, 4, 1, 3]
def baseStart_3931434 : Nat := 118140960795 + 3931434 * 2 ^ 59
def prefixEnd_3931434 : Nat := 4983230072969 + 3 ^ 40 * 3931434 * 2
def baseEnd_3931434 : Nat := 1345810202285517653396447

theorem tailTrace_3931434 : CollatzResearch.WordTrace tailWord_3931434 prefixEnd_3931434 1345810202285517653396447 := by
  unfold tailWord_3931434
  simp only [CollatzResearch.WordTrace]
  refine ⟨35847794509773382079150339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95594118692729018877734237 35847794509773382079150339)
  ·
    refine ⟨53771691764660073118725509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35847794509773382079150339 53771691764660073118725509)
    ·
      refine ⟨10082192205873763709761033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53771691764660073118725509 10082192205873763709761033)
      ·
        refine ⟨7561644154405322782320775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10082192205873763709761033 7561644154405322782320775)
        ·
          refine ⟨11342466231607984173481163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7561644154405322782320775 11342466231607984173481163)
          ·
            refine ⟨17013699347411976260221745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11342466231607984173481163 17013699347411976260221745)
            ·
              refine ⟨12760274510558982195166309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17013699347411976260221745 12760274510558982195166309)
              ·
                refine ⟨2392551470729809161593683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12760274510558982195166309 2392551470729809161593683)
                ·
                  refine ⟨3588827206094713742390525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392551470729809161593683 3588827206094713742390525)
                  ·
                    refine ⟨1345810202285517653396447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3588827206094713742390525 1345810202285517653396447)
                    ·
                      rfl

theorem cell22_3931434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_3931434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931434 prefixEnd_3931434 := by exact prefixLift 3931434
  have htrace : WordTrace (prefixWord ++ tailWord_3931434) baseStart_3931434 baseEnd_3931434 := by
    simpa [prefixWord, tailWord_3931434, baseEnd_3931434] using wordTrace_append hprefix tailTrace_3931434
  have hstable : (prefixWord ++ tailWord_3931434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931434).length < 2 ^ (prefixWord ++ tailWord_3931434).sum := by decide
  have hdescent : baseEnd_3931434 < baseStart_3931434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931473 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_3931473 : Nat := 118140960795 + 3931473 * 2 ^ 59
def prefixEnd_3931473 : Nat := 4983230072969 + 3 ^ 40 * 3931473 * 2
def baseEnd_3931473 : Nat := 1345823552782534551671327

theorem tailTrace_3931473 : CollatzResearch.WordTrace tailWord_3931473 prefixEnd_3931473 1345823552782534551671327 := by
  unfold tailWord_3931473
  simp only [CollatzResearch.WordTrace]
  refine ⟨143392600485952237977271073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95595066990634825318180715 143392600485952237977271073)
  ·
    refine ⟨107544450364464178482953305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143392600485952237977271073 107544450364464178482953305)
    ·
      refine ⟨80658337773348133862214979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107544450364464178482953305 80658337773348133862214979)
      ·
        refine ⟨120987506660022200793322469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80658337773348133862214979 120987506660022200793322469)
        ·
          refine ⟨22685157498754162648747963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120987506660022200793322469 22685157498754162648747963)
          ·
            refine ⟨34027736248131243973121945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22685157498754162648747963 34027736248131243973121945)
            ·
              refine ⟨25520802186098432979841459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34027736248131243973121945 25520802186098432979841459)
              ·
                refine ⟨38281203279147649469762189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25520802186098432979841459 38281203279147649469762189)
                ·
                  refine ⟨14355451229680368551160821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38281203279147649469762189 14355451229680368551160821)
                  ·
                    refine ⟨1345823552782534551671327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14355451229680368551160821 1345823552782534551671327)
                    ·
                      rfl

theorem cell22_3931473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_3931473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931473 prefixEnd_3931473 := by exact prefixLift 3931473
  have htrace : WordTrace (prefixWord ++ tailWord_3931473) baseStart_3931473 baseEnd_3931473 := by
    simpa [prefixWord, tailWord_3931473, baseEnd_3931473] using wordTrace_append hprefix tailTrace_3931473
  have hstable : (prefixWord ++ tailWord_3931473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931473).length < 2 ^ (prefixWord ++ tailWord_3931473).sum := by decide
  have hdescent : baseEnd_3931473 < baseStart_3931473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931485 : List Nat := [1, 4, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3931485 : Nat := 118140960795 + 3931485 * 2 ^ 59
def prefixEnd_3931485 : Nat := 4983230072969 + 3 ^ 40 * 3931485 * 2
def baseEnd_3931485 : Nat := 1345827660627770520371291

theorem tailTrace_3931485 : CollatzResearch.WordTrace tailWord_3931485 prefixEnd_3931485 1345827660627770520371291 := by
  unfold tailWord_3931485
  simp only [CollatzResearch.WordTrace]
  refine ⟨143393038161908764026707909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95595358774605842684471939 143393038161908764026707909)
  ·
    refine ⟨26886194655357893255007733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143393038161908764026707909 26886194655357893255007733)
    ·
      refine ⟨2520580748939802492656975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26886194655357893255007733 2520580748939802492656975)
      ·
        refine ⟨3780871123409703738985463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520580748939802492656975 3780871123409703738985463)
        ·
          refine ⟨5671306685114555608478195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3780871123409703738985463 5671306685114555608478195)
          ·
            refine ⟨8506960027671833412717293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5671306685114555608478195 8506960027671833412717293)
            ·
              refine ⟨3190110010376937529768985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8506960027671833412717293 3190110010376937529768985)
              ·
                refine ⟨2392582507782703147326739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3190110010376937529768985 2392582507782703147326739)
                ·
                  refine ⟨3588873761674054720990109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392582507782703147326739 3588873761674054720990109)
                  ·
                    refine ⟨1345827660627770520371291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3588873761674054720990109 1345827660627770520371291)
                    ·
                      rfl

theorem cell22_3931485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3931485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931485 prefixEnd_3931485 := by exact prefixLift 3931485
  have htrace : WordTrace (prefixWord ++ tailWord_3931485) baseStart_3931485 baseEnd_3931485 := by
    simpa [prefixWord, tailWord_3931485, baseEnd_3931485] using wordTrace_append hprefix tailTrace_3931485
  have hstable : (prefixWord ++ tailWord_3931485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931485).length < 2 ^ (prefixWord ++ tailWord_3931485).sum := by decide
  have hdescent : baseEnd_3931485 < baseStart_3931485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931503 : List Nat := [1, 1, 2, 1, 3, 1, 6, 7]
def baseStart_3931503 : Nat := 118140960795 + 3931503 * 2 ^ 59
def prefixEnd_3931503 : Nat := 4983230072969 + 3 ^ 40 * 3931503 * 2
def baseEnd_3931503 : Nat := 149537091377291608157915

theorem tailTrace_3931503 : CollatzResearch.WordTrace tailWord_3931503 prefixEnd_3931503 149537091377291608157915 := by
  unfold tailWord_3931503
  simp only [CollatzResearch.WordTrace]
  refine ⟨143393694675843553100863163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95595796450562368733908775 143393694675843553100863163)
  ·
    refine ⟨215090542013765329651294745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143393694675843553100863163 215090542013765329651294745)
    ·
      refine ⟨161317906510323997238471059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215090542013765329651294745 161317906510323997238471059)
      ·
        refine ⟨241976859765485995857706589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161317906510323997238471059 241976859765485995857706589)
        ·
          refine ⟨90741322412057248446639971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241976859765485995857706589 90741322412057248446639971)
          ·
            refine ⟨136111983618085872669959957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90741322412057248446639971 136111983618085872669959957)
            ·
              refine ⟨6380249232097775281404373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136111983618085872669959957 6380249232097775281404373)
              ·
                refine ⟨149537091377291608157915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6380249232097775281404373 149537091377291608157915)
                ·
                  rfl

theorem cell22_3931503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 7].length) (baseStart_3931503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931503 prefixEnd_3931503 := by exact prefixLift 3931503
  have htrace : WordTrace (prefixWord ++ tailWord_3931503) baseStart_3931503 baseEnd_3931503 := by
    simpa [prefixWord, tailWord_3931503, baseEnd_3931503] using wordTrace_append hprefix tailTrace_3931503
  have hstable : (prefixWord ++ tailWord_3931503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931503).length < 2 ^ (prefixWord ++ tailWord_3931503).sum := by decide
  have hdescent : baseEnd_3931503 < baseStart_3931503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931593 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 10]
def baseStart_3931593 : Nat := 118140960795 + 3931593 * 2 ^ 59
def prefixEnd_3931593 : Nat := 4983230072969 + 3 ^ 40 * 3931593 * 2
def baseEnd_3931593 : Nat := 448621543744964746223653

theorem tailTrace_3931593 : CollatzResearch.WordTrace tailWord_3931593 prefixEnd_3931593 448621543744964746223653 := by
  unfold tailWord_3931593
  simp only [CollatzResearch.WordTrace]
  refine ⟨143396977245517498471639433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95597984830344998981092955 143396977245517498471639433)
  ·
    refine ⟨107547732934138123853729575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143396977245517498471639433 107547732934138123853729575)
    ·
      refine ⟨161321599401207185780594363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107547732934138123853729575 161321599401207185780594363)
      ·
        refine ⟨241982399101810778670891545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161321599401207185780594363 241982399101810778670891545)
        ·
          refine ⟨181486799326358084003168659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241982399101810778670891545 181486799326358084003168659)
          ·
            refine ⟨272230198989537126004752989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181486799326358084003168659 272230198989537126004752989)
            ·
              refine ⟨102086324621076422251782371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272230198989537126004752989 102086324621076422251782371)
              ·
                refine ⟨153129486931614633377673557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102086324621076422251782371 153129486931614633377673557)
                ·
                  refine ⟨448621543744964746223653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 153129486931614633377673557 448621543744964746223653)
                  ·
                    rfl

theorem cell22_3931593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_3931593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931593 prefixEnd_3931593 := by exact prefixLift 3931593
  have htrace : WordTrace (prefixWord ++ tailWord_3931593) baseStart_3931593 baseEnd_3931593 := by
    simpa [prefixWord, tailWord_3931593, baseEnd_3931593] using wordTrace_append hprefix tailTrace_3931593
  have hstable : (prefixWord ++ tailWord_3931593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931593).length < 2 ^ (prefixWord ++ tailWord_3931593).sum := by decide
  have hdescent : baseEnd_3931593 < baseStart_3931593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931610 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_3931610 : Nat := 118140960795 + 3931610 * 2 ^ 59
def prefixEnd_3931610 : Nat := 4983230072969 + 3 ^ 40 * 3931610 * 2
def baseEnd_3931610 : Nat := 448623483560770620331969

theorem tailTrace_3931610 : CollatzResearch.WordTrace tailWord_3931610 prefixEnd_3931610 448623483560770620331969 := by
  unfold tailWord_3931610
  simp only [CollatzResearch.WordTrace]
  refine ⟨35849399321613977593752071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95598398190970606916672189 35849399321613977593752071)
  ·
    refine ⟨53774098982420966390628107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35849399321613977593752071 53774098982420966390628107)
    ·
      refine ⟨80661148473631449585942161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53774098982420966390628107 80661148473631449585942161)
      ·
        refine ⟨60495861355223587189456621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80661148473631449585942161 60495861355223587189456621)
        ·
          refine ⟨22685948008208845196046233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60495861355223587189456621 22685948008208845196046233)
          ·
            refine ⟨17014461006156633897034675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22685948008208845196046233 17014461006156633897034675)
            ·
              refine ⟨25521691509234950845552013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17014461006156633897034675 25521691509234950845552013)
              ·
                refine ⟨9570634315963106567082005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25521691509234950845552013 9570634315963106567082005)
                ·
                  refine ⟨448623483560770620331969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9570634315963106567082005 448623483560770620331969)
                  ·
                    rfl

theorem cell22_3931610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_3931610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931610 prefixEnd_3931610 := by exact prefixLift 3931610
  have htrace : WordTrace (prefixWord ++ tailWord_3931610) baseStart_3931610 baseEnd_3931610 := by
    simpa [prefixWord, tailWord_3931610, baseEnd_3931610] using wordTrace_append hprefix tailTrace_3931610
  have hstable : (prefixWord ++ tailWord_3931610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931610).length < 2 ^ (prefixWord ++ tailWord_3931610).sum := by decide
  have hdescent : baseEnd_3931610 < baseStart_3931610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931640 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_3931640 : Nat := 118140960795 + 3931640 * 2 ^ 59
def prefixEnd_3931640 : Nat := 4983230072969 + 3 ^ 40 * 3931640 * 2
def baseEnd_3931640 : Nat := 1345880720295401782745815

theorem tailTrace_3931640 : CollatzResearch.WordTrace tailWord_3931640 prefixEnd_3931640 1345880720295401782745815 := by
  unfold tailWord_3931640
  simp only [CollatzResearch.WordTrace]
  refine ⟨71699345738173612749300187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95599127650898150332400249 71699345738173612749300187)
  ·
    refine ⟨107549018607260419123950281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71699345738173612749300187 107549018607260419123950281)
    ·
      refine ⟨80661763955445314342962711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107549018607260419123950281 80661763955445314342962711)
      ·
        refine ⟨120992645933167971514444067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80661763955445314342962711 120992645933167971514444067)
        ·
          refine ⟨181488968899751957271666101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120992645933167971514444067 181488968899751957271666101)
          ·
            refine ⟨17014590834351745994218697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181488968899751957271666101 17014590834351745994218697)
            ·
              refine ⟨12760943125763809495664023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17014590834351745994218697 12760943125763809495664023)
              ·
                refine ⟨19141414688645714243496035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12760943125763809495664023 19141414688645714243496035)
                ·
                  refine ⟨28712122032968571365244053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19141414688645714243496035 28712122032968571365244053)
                  ·
                    refine ⟨1345880720295401782745815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28712122032968571365244053 1345880720295401782745815)
                    ·
                      rfl

theorem cell22_3931640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_3931640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931640 prefixEnd_3931640 := by exact prefixLift 3931640
  have htrace : WordTrace (prefixWord ++ tailWord_3931640) baseStart_3931640 baseEnd_3931640 := by
    simpa [prefixWord, tailWord_3931640, baseEnd_3931640] using wordTrace_append hprefix tailTrace_3931640
  have hstable : (prefixWord ++ tailWord_3931640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931640).length < 2 ^ (prefixWord ++ tailWord_3931640).sum := by decide
  have hdescent : baseEnd_3931640 < baseStart_3931640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931655 : List Nat := [1, 1, 4, 3, 2, 1, 10]
def baseStart_3931655 : Nat := 118140960795 + 3931655 * 2 ^ 59
def prefixEnd_3931655 : Nat := 4983230072969 + 3 ^ 40 * 3931655 * 2
def baseEnd_3931655 : Nat := 49847624263035064578547

theorem tailTrace_3931655 : CollatzResearch.WordTrace tailWord_3931655 prefixEnd_3931655 49847624263035064578547 := by
  unfold tailWord_3931655
  simp only [CollatzResearch.WordTrace]
  refine ⟨143399238571292883060396419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95599492380861922040264279 143399238571292883060396419)
  ·
    refine ⟨215098857856939324590594629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143399238571292883060396419 215098857856939324590594629)
    ·
      refine ⟨40331035848176123360736493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215098857856939324590594629 40331035848176123360736493)
      ·
        refine ⟨15124138443066046260276185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40331035848176123360736493 15124138443066046260276185)
        ·
          refine ⟨11343103832299534695207139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15124138443066046260276185 11343103832299534695207139)
          ·
            refine ⟨17014655748449302042810709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11343103832299534695207139 17014655748449302042810709)
            ·
              refine ⟨49847624263035064578547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17014655748449302042810709 49847624263035064578547)
              ·
                rfl

theorem cell22_3931655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 10].length) (baseStart_3931655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931655 prefixEnd_3931655 := by exact prefixLift 3931655
  have htrace : WordTrace (prefixWord ++ tailWord_3931655) baseStart_3931655 baseEnd_3931655 := by
    simpa [prefixWord, tailWord_3931655, baseEnd_3931655] using wordTrace_append hprefix tailTrace_3931655
  have hstable : (prefixWord ++ tailWord_3931655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931655).length < 2 ^ (prefixWord ++ tailWord_3931655).sum := by decide
  have hdescent : baseEnd_3931655 < baseStart_3931655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931672 : List Nat := [2, 1, 2, 3, 4, 1, 2, 7]
def baseStart_3931672 : Nat := 118140960795 + 3931672 * 2 ^ 59
def prefixEnd_3931672 : Nat := 4983230072969 + 3 ^ 40 * 3931672 * 2
def baseEnd_3931672 : Nat := 149543519394373818438413

theorem tailTrace_3931672 : CollatzResearch.WordTrace tailWord_3931672 prefixEnd_3931672 149543519394373818438413 := by
  unfold tailWord_3931672
  simp only [CollatzResearch.WordTrace]
  refine ⟨71699929306115647481882635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95599905741487529975843513 71699929306115647481882635)
  ·
    refine ⟨107549893959173471222823953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71699929306115647481882635 107549893959173471222823953)
    ·
      refine ⟨80662420469380103417117965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107549893959173471222823953 80662420469380103417117965)
      ·
        refine ⟨30248407676017538781419237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80662420469380103417117965 30248407676017538781419237)
        ·
          refine ⟨5671576439253288521516107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30248407676017538781419237 5671576439253288521516107)
          ·
            refine ⟨8507364658879932782274161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5671576439253288521516107 8507364658879932782274161)
            ·
              refine ⟨6380523494159949586705621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8507364658879932782274161 6380523494159949586705621)
              ·
                refine ⟨149543519394373818438413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6380523494159949586705621 149543519394373818438413)
                ·
                  rfl

theorem cell22_3931672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 7].length) (baseStart_3931672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931672 prefixEnd_3931672 := by exact prefixLift 3931672
  have htrace : WordTrace (prefixWord ++ tailWord_3931672) baseStart_3931672 baseEnd_3931672 := by
    simpa [prefixWord, tailWord_3931672, baseEnd_3931672] using wordTrace_append hprefix tailTrace_3931672
  have hstable : (prefixWord ++ tailWord_3931672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931672).length < 2 ^ (prefixWord ++ tailWord_3931672).sum := by decide
  have hdescent : baseEnd_3931672 < baseStart_3931672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931717 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 5]
def baseStart_3931717 : Nat := 118140960795 + 3931717 * 2 ^ 59
def prefixEnd_3931717 : Nat := 4983230072969 + 3 ^ 40 * 3931717 * 2
def baseEnd_3931717 : Nat := 448635692989666416190193

theorem tailTrace_3931717 : CollatzResearch.WordTrace tailWord_3931717 prefixEnd_3931717 448635692989666416190193 := by
  unfold tailWord_3931717
  simp only [CollatzResearch.WordTrace]
  refine ⟨143401499897068267649153405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95600999931378845099435603 143401499897068267649153405)
  ·
    refine ⟨53775562461400600368432527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143401499897068267649153405 53775562461400600368432527)
    ·
      refine ⟨80663343692100900552648791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53775562461400600368432527 80663343692100900552648791)
      ·
        refine ⟨120995015538151350828973187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80663343692100900552648791 120995015538151350828973187)
        ·
          refine ⟨181492523307227026243459781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120995015538151350828973187 181492523307227026243459781)
          ·
            refine ⟨34029848120105067420648709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181492523307227026243459781 34029848120105067420648709)
            ·
              refine ⟨6380596522519700141371633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34029848120105067420648709 6380596522519700141371633)
              ·
                refine ⟨4785447391889775106028725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6380596522519700141371633 4785447391889775106028725)
                ·
                  refine ⟨448635692989666416190193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4785447391889775106028725 448635692989666416190193)
                  ·
                    rfl

theorem cell22_3931717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_3931717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931717 prefixEnd_3931717 := by exact prefixLift 3931717
  have htrace : WordTrace (prefixWord ++ tailWord_3931717) baseStart_3931717 baseEnd_3931717 := by
    simpa [prefixWord, tailWord_3931717, baseEnd_3931717] using wordTrace_append hprefix tailTrace_3931717
  have hstable : (prefixWord ++ tailWord_3931717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931717).length < 2 ^ (prefixWord ++ tailWord_3931717).sum := by decide
  have hdescent : baseEnd_3931717 < baseStart_3931717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931732 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_3931732 : Nat := 118140960795 + 3931732 * 2 ^ 59
def prefixEnd_3931732 : Nat := 4983230072969 + 3 ^ 40 * 3931732 * 2
def baseEnd_3931732 : Nat := 1345912213775544209445533

theorem tailTrace_3931732 : CollatzResearch.WordTrace tailWord_3931732 prefixEnd_3931732 1345912213775544209445533 := by
  unfold tailWord_3931732
  simp only [CollatzResearch.WordTrace]
  refine ⟨71701023496006962605474725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95601364661342616807299633 71701023496006962605474725)
  ·
    refine ⟨13443941905501305488526511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71701023496006962605474725 13443941905501305488526511)
    ·
      refine ⟨20165912858251958232789767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13443941905501305488526511 20165912858251958232789767)
      ·
        refine ⟨30248869287377937349184651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20165912858251958232789767 30248869287377937349184651)
        ·
          refine ⟨45373303931066906023776977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30248869287377937349184651 45373303931066906023776977)
          ·
            refine ⟨34029977948300179517832733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45373303931066906023776977 34029977948300179517832733)
            ·
              refine ⟨12761241730612567319187275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34029977948300179517832733 12761241730612567319187275)
              ·
                refine ⟨19141862595918850978780913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12761241730612567319187275 19141862595918850978780913)
                ·
                  refine ⟨14356396946939138234085685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19141862595918850978780913 14356396946939138234085685)
                  ·
                    refine ⟨1345912213775544209445533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14356396946939138234085685 1345912213775544209445533)
                    ·
                      rfl

theorem cell22_3931732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_3931732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931732 prefixEnd_3931732 := by exact prefixLift 3931732
  have htrace : WordTrace (prefixWord ++ tailWord_3931732) baseStart_3931732 baseEnd_3931732 := by
    simpa [prefixWord, tailWord_3931732, baseEnd_3931732] using wordTrace_append hprefix tailTrace_3931732
  have hstable : (prefixWord ++ tailWord_3931732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931732).length < 2 ^ (prefixWord ++ tailWord_3931732).sum := by decide
  have hdescent : baseEnd_3931732 < baseStart_3931732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931747 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 3, 4]
def baseStart_3931747 : Nat := 118140960795 + 3931747 * 2 ^ 59
def prefixEnd_3931747 : Nat := 4983230072969 + 3 ^ 40 * 3931747 * 2
def baseEnd_3931747 : Nat := 1345917348582089170320487

theorem tailTrace_3931747 : CollatzResearch.WordTrace tailWord_3931747 prefixEnd_3931747 1345917348582089170320487 := by
  unfold tailWord_3931747
  simp only [CollatzResearch.WordTrace]
  refine ⟨143402594086959582772745495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95601729391306388515163663 143402594086959582772745495)
  ·
    refine ⟨215103891130439374159118243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143402594086959582772745495 215103891130439374159118243)
    ·
      refine ⟨322655836695659061238677365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215103891130439374159118243 322655836695659061238677365)
      ·
        refine ⟨30248984690218036991126003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322655836695659061238677365 30248984690218036991126003)
        ·
          refine ⟨45373477035327055486689005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30248984690218036991126003 45373477035327055486689005)
          ·
            refine ⟨17015053888247645807508377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45373477035327055486689005 17015053888247645807508377)
            ·
              refine ⟨12761290416185734355631283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17015053888247645807508377 12761290416185734355631283)
              ·
                refine ⟨19141935624278601533446925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12761290416185734355631283 19141935624278601533446925)
                ·
                  refine ⟨7178225859104475575042597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19141935624278601533446925 7178225859104475575042597)
                  ·
                    refine ⟨1345917348582089170320487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7178225859104475575042597 1345917348582089170320487)
                    ·
                      rfl

theorem cell22_3931747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 4].length) (baseStart_3931747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931747 prefixEnd_3931747 := by exact prefixLift 3931747
  have htrace : WordTrace (prefixWord ++ tailWord_3931747) baseStart_3931747 baseEnd_3931747 := by
    simpa [prefixWord, tailWord_3931747, baseEnd_3931747] using wordTrace_append hprefix tailTrace_3931747
  have hstable : (prefixWord ++ tailWord_3931747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931747).length < 2 ^ (prefixWord ++ tailWord_3931747).sum := by decide
  have hdescent : baseEnd_3931747 < baseStart_3931747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931830 : List Nat := [5, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_3931830 : Nat := 118140960795 + 3931830 * 2 ^ 59
def prefixEnd_3931830 : Nat := 4983230072969 + 3 ^ 40 * 3931830 * 2
def baseEnd_3931830 : Nat := 448648587059434873498411

theorem tailTrace_3931830 : CollatzResearch.WordTrace tailWord_3931830 prefixEnd_3931830 448648587059434873498411 := by
  unfold tailWord_3931830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8962851334103680496751059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95603747563772591965344629 8962851334103680496751059)
  ·
    refine ⟨13444277001155520745126589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8962851334103680496751059 13444277001155520745126589)
    ·
      refine ⟨5041603875433320279422471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13444277001155520745126589 5041603875433320279422471)
      ·
        refine ⟨7562405813149980419133707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5041603875433320279422471 7562405813149980419133707)
        ·
          refine ⟨11343608719724970628700561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7562405813149980419133707 11343608719724970628700561)
          ·
            refine ⟨8507706539793727971525421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11343608719724970628700561 8507706539793727971525421)
            ·
              refine ⟨3190389952422647989322033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8507706539793727971525421 3190389952422647989322033)
              ·
                refine ⟨2392792464316985991991525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3190389952422647989322033 2392792464316985991991525)
                ·
                  refine ⟨448648587059434873498411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2392792464316985991991525 448648587059434873498411)
                  ·
                    rfl

theorem cell22_3931830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_3931830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931830 prefixEnd_3931830 := by exact prefixLift 3931830
  have htrace : WordTrace (prefixWord ++ tailWord_3931830) baseStart_3931830 baseEnd_3931830 := by
    simpa [prefixWord, tailWord_3931830, baseEnd_3931830] using wordTrace_append hprefix tailTrace_3931830
  have hstable : (prefixWord ++ tailWord_3931830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931830).length < 2 ^ (prefixWord ++ tailWord_3931830).sum := by decide
  have hdescent : baseEnd_3931830 < baseStart_3931830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931837 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3931837 : Nat := 118140960795 + 3931837 * 2 ^ 59
def prefixEnd_3931837 : Nat := 4983230072969 + 3 ^ 40 * 3931837 * 2
def baseEnd_3931837 : Nat := 1345948157421358935570211

theorem tailTrace_3931837 : CollatzResearch.WordTrace tailWord_3931837 prefixEnd_3931837 1345948157421358935570211 := by
  unfold tailWord_3931837
  simp only [CollatzResearch.WordTrace]
  refine ⟨143405876656633528143521765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95603917771089018762347843 143405876656633528143521765)
  ·
    refine ⟨26888601873118786526910331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143405876656633528143521765 26888601873118786526910331)
    ·
      refine ⟨40332902809678179790365497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26888601873118786526910331 40332902809678179790365497)
      ·
        refine ⟨30249677107258634842774123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40332902809678179790365497 30249677107258634842774123)
        ·
          refine ⟨45374515660887952264161185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30249677107258634842774123 45374515660887952264161185)
          ·
            refine ⟨34030886745665964198120889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45374515660887952264161185 34030886745665964198120889)
            ·
              refine ⟨25523165059249473148590667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34030886745665964198120889 25523165059249473148590667)
              ·
                refine ⟨38284747588874209722886001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25523165059249473148590667 38284747588874209722886001)
                ·
                  refine ⟨28713560691655657292164501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38284747588874209722886001 28713560691655657292164501)
                  ·
                    refine ⟨1345948157421358935570211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28713560691655657292164501 1345948157421358935570211)
                    ·
                      rfl

theorem cell22_3931837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3931837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931837 prefixEnd_3931837 := by exact prefixLift 3931837
  have htrace : WordTrace (prefixWord ++ tailWord_3931837) baseStart_3931837 baseEnd_3931837 := by
    simpa [prefixWord, tailWord_3931837, baseEnd_3931837] using wordTrace_append hprefix tailTrace_3931837
  have hstable : (prefixWord ++ tailWord_3931837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931837).length < 2 ^ (prefixWord ++ tailWord_3931837).sum := by decide
  have hdescent : baseEnd_3931837 < baseStart_3931837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931914 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_3931914 : Nat := 118140960795 + 3931914 * 2 ^ 59
def prefixEnd_3931914 : Nat := 4983230072969 + 3 ^ 40 * 3931914 * 2
def baseEnd_3931914 : Nat := 448658172031652133798325

theorem tailTrace_3931914 : CollatzResearch.WordTrace tailWord_3931914 prefixEnd_3931914 448658172031652133798325 := by
  unfold tailWord_3931914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35852171269338642573518699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95605790051569713529383197 35852171269338642573518699)
  ·
    refine ⟨53778256904007963860278049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35852171269338642573518699 53778256904007963860278049)
    ·
      refine ⟨40333692678005972895208537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53778256904007963860278049 40333692678005972895208537)
      ·
        refine ⟨30250269508504479671406403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40333692678005972895208537 30250269508504479671406403)
        ·
          refine ⟨45375404262756719507109605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30250269508504479671406403 45375404262756719507109605)
          ·
            refine ⟨8507888299266884907583051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45375404262756719507109605 8507888299266884907583051)
            ·
              refine ⟨12761832448900327361374577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8507888299266884907583051 12761832448900327361374577)
              ·
                refine ⟨9571374336675245521030933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12761832448900327361374577 9571374336675245521030933)
                ·
                  refine ⟨448658172031652133798325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9571374336675245521030933 448658172031652133798325)
                  ·
                    rfl

theorem cell22_3931914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_3931914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931914 prefixEnd_3931914 := by exact prefixLift 3931914
  have htrace : WordTrace (prefixWord ++ tailWord_3931914) baseStart_3931914 baseEnd_3931914 := by
    simpa [prefixWord, tailWord_3931914, baseEnd_3931914] using wordTrace_append hprefix tailTrace_3931914
  have hstable : (prefixWord ++ tailWord_3931914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931914).length < 2 ^ (prefixWord ++ tailWord_3931914).sum := by decide
  have hdescent : baseEnd_3931914 < baseStart_3931914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931924 : List Nat := [2, 4, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3931924 : Nat := 118140960795 + 3931924 * 2 ^ 59
def prefixEnd_3931924 : Nat := 4983230072969 + 3 ^ 40 * 3931924 * 2
def baseEnd_3931924 : Nat := 1345977939299319708644945

theorem tailTrace_3931924 : CollatzResearch.WordTrace tailWord_3931924 prefixEnd_3931924 1345977939299319708644945 := by
  unfold tailWord_3931924
  simp only [CollatzResearch.WordTrace]
  refine ⟨71704524903659171000969413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95606033204878894667959217 71704524903659171000969413)
  ·
    refine ⟨13444598419436094562681765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71704524903659171000969413 13444598419436094562681765)
    ·
      refine ⟨2520862203644267730502831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13444598419436094562681765 2520862203644267730502831)
      ·
        refine ⟨3781293305466401595754247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520862203644267730502831 3781293305466401595754247)
        ·
          refine ⟨5671939958199602393631371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781293305466401595754247 5671939958199602393631371)
          ·
            refine ⟨8507909937299403590447057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5671939958199602393631371 8507909937299403590447057)
            ·
              refine ⟨6380932452974552692835293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8507909937299403590447057 6380932452974552692835293)
              ·
                refine ⟨2392849669865457259813235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6380932452974552692835293 2392849669865457259813235)
                ·
                  refine ⟨3589274504798185889719853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392849669865457259813235 3589274504798185889719853)
                  ·
                    refine ⟨1345977939299319708644945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3589274504798185889719853 1345977939299319708644945)
                    ·
                      rfl

theorem cell22_3931924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3931924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931924 prefixEnd_3931924 := by exact prefixLift 3931924
  have htrace : WordTrace (prefixWord ++ tailWord_3931924) baseStart_3931924 baseEnd_3931924 := by
    simpa [prefixWord, tailWord_3931924, baseEnd_3931924] using wordTrace_append hprefix tailTrace_3931924
  have hstable : (prefixWord ++ tailWord_3931924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931924).length < 2 ^ (prefixWord ++ tailWord_3931924).sum := by decide
  have hdescent : baseEnd_3931924 < baseStart_3931924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931976 : List Nat := [2, 1, 3, 1, 1, 6, 2, 6]
def baseStart_3931976 : Nat := 118140960795 + 3931976 * 2 ^ 59
def prefixEnd_3931976 : Nat := 4983230072969 + 3 ^ 40 * 3931976 * 2
def baseEnd_3931976 : Nat := 149555082218000989593865

theorem tailTrace_3931976 : CollatzResearch.WordTrace tailWord_3931976 prefixEnd_3931976 149555082218000989593865 := by
  unfold tailWord_3931976
  simp only [CollatzResearch.WordTrace]
  refine ⟨71705473201564977441415891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95607297602086636588554521 71705473201564977441415891)
  ·
    refine ⟨107558209802347466162123837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71705473201564977441415891 107558209802347466162123837)
    ·
      refine ⟨40334328675880299810796439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107558209802347466162123837 40334328675880299810796439)
      ·
        refine ⟨60501493013820449716194659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40334328675880299810796439 60501493013820449716194659)
        ·
          refine ⟨90752239520730674574291989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60501493013820449716194659 90752239520730674574291989)
          ·
            refine ⟨4254011227534250370669937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90752239520730674574291989 4254011227534250370669937)
            ·
              refine ⟨3190508420650687778002453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4254011227534250370669937 3190508420650687778002453)
              ·
                refine ⟨149555082218000989593865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3190508420650687778002453 149555082218000989593865)
                ·
                  rfl

theorem cell22_3931976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 6].length) (baseStart_3931976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3931976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3931976 prefixEnd_3931976 := by exact prefixLift 3931976
  have htrace : WordTrace (prefixWord ++ tailWord_3931976) baseStart_3931976 baseEnd_3931976 := by
    simpa [prefixWord, tailWord_3931976, baseEnd_3931976] using wordTrace_append hprefix tailTrace_3931976
  have hstable : (prefixWord ++ tailWord_3931976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931976).length < 2 ^ (prefixWord ++ tailWord_3931976).sum := by decide
  have hdescent : baseEnd_3931976 < baseStart_3931976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932021 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 5]
def baseStart_3932021 : Nat := 118140960795 + 3932021 * 2 ^ 59
def prefixEnd_3932021 : Nat := 4983230072969 + 3 ^ 40 * 3932021 * 2
def baseEnd_3932021 : Nat := 448670381460547929656549

theorem tailTrace_3932021 : CollatzResearch.WordTrace tailWord_3932021 prefixEnd_3932021 448670381460547929656549 := by
  unfold tailWord_3932021
  simp only [CollatzResearch.WordTrace]
  refine ⟨143412587687966927568219917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95608391791977951712146611 143412587687966927568219917)
  ·
    refine ⟨53779720382987597838082469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143412587687966927568219917 53779720382987597838082469)
    ·
      refine ⟨10083697571810174594640463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53779720382987597838082469 10083697571810174594640463)
      ·
        refine ⟨15125546357715261891960695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10083697571810174594640463 15125546357715261891960695)
        ·
          refine ⟨22688319536572892837941043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15125546357715261891960695 22688319536572892837941043)
          ·
            refine ⟨34032479304859339256911565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22688319536572892837941043 34032479304859339256911565)
            ·
              refine ⟨12762179739322252221341837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34032479304859339256911565 12762179739322252221341837)
              ·
                refine ⟨4785817402245844583003189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12762179739322252221341837 4785817402245844583003189)
                ·
                  refine ⟨448670381460547929656549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4785817402245844583003189 448670381460547929656549)
                  ·
                    rfl

theorem cell22_3932021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_3932021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932021 prefixEnd_3932021 := by exact prefixLift 3932021
  have htrace : WordTrace (prefixWord ++ tailWord_3932021) baseStart_3932021 baseEnd_3932021 := by
    simpa [prefixWord, tailWord_3932021, baseEnd_3932021] using wordTrace_append hprefix tailTrace_3932021
  have hstable : (prefixWord ++ tailWord_3932021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932021).length < 2 ^ (prefixWord ++ tailWord_3932021).sum := by decide
  have hdescent : baseEnd_3932021 < baseStart_3932021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932064 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_3932064 : Nat := 118140960795 + 3932064 * 2 ^ 59
def prefixEnd_3932064 : Nat := 4983230072969 + 3 ^ 40 * 3932064 * 2
def baseEnd_3932064 : Nat := 1346025864160406010144515

theorem tailTrace_3932064 : CollatzResearch.WordTrace tailWord_3932064 prefixEnd_3932064 1346025864160406010144515 := by
  unfold tailWord_3932064
  simp only [CollatzResearch.WordTrace]
  refine ⟨71707078013405572956017623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95609437351207430608023497 71707078013405572956017623)
  ·
    refine ⟨107560617020108359434026435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71707078013405572956017623 107560617020108359434026435)
    ·
      refine ⟨161340925530162539151039653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107560617020108359434026435 161340925530162539151039653)
      ·
        refine ⟨30251423536905476090819935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161340925530162539151039653 30251423536905476090819935)
        ·
          refine ⟨45377135305358214136229903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30251423536905476090819935 45377135305358214136229903)
          ·
            refine ⟨68065702958037321204344855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45377135305358214136229903 68065702958037321204344855)
            ·
              refine ⟨102098554437055981806517283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68065702958037321204344855 102098554437055981806517283)
              ·
                refine ⟨153147831655583972709775925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102098554437055981806517283 153147831655583972709775925)
                ·
                  refine ⟨14357609217710997441541493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153147831655583972709775925 14357609217710997441541493)
                  ·
                    refine ⟨1346025864160406010144515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14357609217710997441541493 1346025864160406010144515)
                    ·
                      rfl

theorem cell22_3932064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_3932064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932064 prefixEnd_3932064 := by exact prefixLift 3932064
  have htrace : WordTrace (prefixWord ++ tailWord_3932064) baseStart_3932064 baseEnd_3932064 := by
    simpa [prefixWord, tailWord_3932064, baseEnd_3932064] using wordTrace_append hprefix tailTrace_3932064
  have hstable : (prefixWord ++ tailWord_3932064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932064).length < 2 ^ (prefixWord ++ tailWord_3932064).sum := by decide
  have hdescent : baseEnd_3932064 < baseStart_3932064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932079 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 1, 6]
def baseStart_3932079 : Nat := 118140960795 + 3932079 * 2 ^ 59
def prefixEnd_3932079 : Nat := 4983230072969 + 3 ^ 40 * 3932079 * 2
def baseEnd_3932079 : Nat := 1346030998966950971019469

theorem tailTrace_3932079 : CollatzResearch.WordTrace tailWord_3932079 prefixEnd_3932079 1346030998966950971019469 := by
  unfold tailWord_3932079
  simp only [CollatzResearch.WordTrace]
  refine ⟨143414703121756803473831291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95609802081171202315887527 143414703121756803473831291)
  ·
    refine ⟨215122054682635205210746937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143414703121756803473831291 215122054682635205210746937)
    ·
      refine ⟨161341541011976403908060203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215122054682635205210746937 161341541011976403908060203)
      ·
        refine ⟨242012311517964605862090305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161341541011976403908060203 242012311517964605862090305)
        ·
          refine ⟨181509233638473454396567729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242012311517964605862090305 181509233638473454396567729)
          ·
            refine ⟨136131925228855090797425797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181509233638473454396567729 136131925228855090797425797)
            ·
              refine ⟨25524735980410329524517337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136131925228855090797425797 25524735980410329524517337)
              ·
                refine ⟨19143551985307747143388003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25524735980410329524517337 19143551985307747143388003)
                ·
                  refine ⟨28715327977961620715082005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19143551985307747143388003 28715327977961620715082005)
                  ·
                    refine ⟨1346030998966950971019469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28715327977961620715082005 1346030998966950971019469)
                    ·
                      rfl

theorem cell22_3932079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_3932079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932079 prefixEnd_3932079 := by exact prefixLift 3932079
  have htrace : WordTrace (prefixWord ++ tailWord_3932079) baseStart_3932079 baseEnd_3932079 := by
    simpa [prefixWord, tailWord_3932079, baseEnd_3932079] using wordTrace_append hprefix tailTrace_3932079
  have hstable : (prefixWord ++ tailWord_3932079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932079).length < 2 ^ (prefixWord ++ tailWord_3932079).sum := by decide
  have hdescent : baseEnd_3932079 < baseStart_3932079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932081 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_3932081 : Nat := 118140960795 + 3932081 * 2 ^ 59
def prefixEnd_3932081 : Nat := 4983230072969 + 3 ^ 40 * 3932081 * 2
def baseEnd_3932081 : Nat := 1346031683607823632469463

theorem tailTrace_3932081 : CollatzResearch.WordTrace tailWord_3932081 prefixEnd_3932081 1346031683607823632469463 := by
  unfold tailWord_3932081
  simp only [CollatzResearch.WordTrace]
  refine ⟨143414776067749557815404097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95609850711833038543602731 143414776067749557815404097)
  ·
    refine ⟨107561082050812168361553073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143414776067749557815404097 107561082050812168361553073)
    ·
      refine ⟨80670811538109126271164805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107561082050812168361553073 80670811538109126271164805)
      ·
        refine ⟨15125777163395461175843401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80670811538109126271164805 15125777163395461175843401)
        ·
          refine ⟨11344332872546595881882551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15125777163395461175843401 11344332872546595881882551)
          ·
            refine ⟨17016499308819893822823827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11344332872546595881882551 17016499308819893822823827)
            ·
              refine ⟨25524748963229840734235741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17016499308819893822823827 25524748963229840734235741)
              ·
                refine ⟨9571780861211190275338403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25524748963229840734235741 9571780861211190275338403)
                ·
                  refine ⟨14357671291816785413007605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9571780861211190275338403 14357671291816785413007605)
                  ·
                    refine ⟨1346031683607823632469463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14357671291816785413007605 1346031683607823632469463)
                    ·
                      rfl

theorem cell22_3932081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_3932081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932081 prefixEnd_3932081 := by exact prefixLift 3932081
  have htrace : WordTrace (prefixWord ++ tailWord_3932081) baseStart_3932081 baseEnd_3932081 := by
    simpa [prefixWord, tailWord_3932081, baseEnd_3932081] using wordTrace_append hprefix tailTrace_3932081
  have hstable : (prefixWord ++ tailWord_3932081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932081).length < 2 ^ (prefixWord ++ tailWord_3932081).sum := by decide
  have hdescent : baseEnd_3932081 < baseStart_3932081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932145 : List Nat := [1, 2, 2, 2, 6, 1, 2, 6]
def baseStart_3932145 : Nat := 118140960795 + 3932145 * 2 ^ 59
def prefixEnd_3932145 : Nat := 4983230072969 + 3 ^ 40 * 3932145 * 2
def baseEnd_3932145 : Nat := 149561510235083199874363

theorem tailTrace_3932145 : CollatzResearch.WordTrace tailWord_3932145 prefixEnd_3932145 149561510235083199874363 := by
  unfold tailWord_3932145
  simp only [CollatzResearch.WordTrace]
  refine ⟨143417110339517696745733889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95611406893011797830489259 143417110339517696745733889)
  ·
    refine ⟨107562832754638272559300417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143417110339517696745733889 107562832754638272559300417)
    ·
      refine ⟨80672124565978704419475313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107562832754638272559300417 80672124565978704419475313)
      ·
        refine ⟨60504093424484028314606485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80672124565978704419475313 60504093424484028314606485)
        ·
          refine ⟨2836129379272688827247179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60504093424484028314606485 2836129379272688827247179)
          ·
            refine ⟨4254194068909033240870769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836129379272688827247179 4254194068909033240870769)
            ·
              refine ⟨3190645551681774930653077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4254194068909033240870769 3190645551681774930653077)
              ·
                refine ⟨149561510235083199874363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3190645551681774930653077 149561510235083199874363)
                ·
                  rfl

theorem cell22_3932145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 6].length) (baseStart_3932145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932145 prefixEnd_3932145 := by exact prefixLift 3932145
  have htrace : WordTrace (prefixWord ++ tailWord_3932145) baseStart_3932145 baseEnd_3932145 := by
    simpa [prefixWord, tailWord_3932145, baseEnd_3932145] using wordTrace_append hprefix tailTrace_3932145
  have hstable : (prefixWord ++ tailWord_3932145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932145).length < 2 ^ (prefixWord ++ tailWord_3932145).sum := by decide
  have hdescent : baseEnd_3932145 < baseStart_3932145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932218 : List Nat := [3, 1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_3932218 : Nat := 118140960795 + 3932218 * 2 ^ 59
def prefixEnd_3932218 : Nat := 4983230072969 + 3 ^ 40 * 3932218 * 2
def baseEnd_3932218 : Nat := 448692860502533647264681

theorem tailTrace_3932218 : CollatzResearch.WordTrace tailWord_3932218 prefixEnd_3932218 448692860502533647264681 := by
  unfold tailWord_3932218
  simp only [CollatzResearch.WordTrace]
  refine ⟨35854943217063307553285327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95613181912168820142094205 35854943217063307553285327)
  ·
    refine ⟨53782414825594961329927991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35854943217063307553285327 53782414825594961329927991)
    ·
      refine ⟨80673622238392441994891987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53782414825594961329927991 80673622238392441994891987)
      ·
        refine ⟨121010433357588662992337981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80673622238392441994891987 121010433357588662992337981)
        ·
          refine ⟨45378912509095748622126743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121010433357588662992337981 45378912509095748622126743)
          ·
            refine ⟨68068368763643622933190115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45378912509095748622126743 68068368763643622933190115)
            ·
              refine ⟨102102553145465434399785173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68068368763643622933190115 102102553145465434399785173)
              ·
                refine ⟨2393028589346846118744965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102102553145465434399785173 2393028589346846118744965)
                ·
                  refine ⟨448692860502533647264681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393028589346846118744965 448692860502533647264681)
                  ·
                    rfl

theorem cell22_3932218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_3932218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932218 prefixEnd_3932218 := by exact prefixLift 3932218
  have htrace : WordTrace (prefixWord ++ tailWord_3932218) baseStart_3932218 baseEnd_3932218 := by
    simpa [prefixWord, tailWord_3932218, baseEnd_3932218] using wordTrace_append hprefix tailTrace_3932218
  have hstable : (prefixWord ++ tailWord_3932218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932218).length < 2 ^ (prefixWord ++ tailWord_3932218).sum := by decide
  have hdescent : baseEnd_3932218 < baseStart_3932218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932220 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 1, 4]
def baseStart_3932220 : Nat := 118140960795 + 3932220 * 2 ^ 59
def prefixEnd_3932220 : Nat := 4983230072969 + 3 ^ 40 * 3932220 * 2
def baseEnd_3932220 : Nat := 1346079266148473603244037

theorem tailTrace_3932220 : CollatzResearch.WordTrace tailWord_3932220 prefixEnd_3932220 1346079266148473603244037 := by
  unfold tailWord_3932220
  simp only [CollatzResearch.WordTrace]
  refine ⟨71709922907122992277357057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95613230542830656369809409 71709922907122992277357057)
  ·
    refine ⟨53782442180342244208017793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71709922907122992277357057 53782442180342244208017793)
    ·
      refine ⟨40336831635256683156013345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53782442180342244208017793 40336831635256683156013345)
      ·
        refine ⟨30252623726442512367010009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40336831635256683156013345 30252623726442512367010009)
        ·
          refine ⟨22689467794831884275257507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30252623726442512367010009 22689467794831884275257507)
          ·
            refine ⟨34034201692247826412886261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22689467794831884275257507 34034201692247826412886261)
            ·
              refine ⟨3190706408648233726208087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34034201692247826412886261 3190706408648233726208087)
              ·
                refine ⟨4786059612972350589312131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190706408648233726208087 4786059612972350589312131)
                ·
                  refine ⟨7179089419458525883968197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4786059612972350589312131 7179089419458525883968197)
                  ·
                    refine ⟨1346079266148473603244037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7179089419458525883968197 1346079266148473603244037)
                    ·
                      rfl

theorem cell22_3932220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_3932220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932220 prefixEnd_3932220 := by exact prefixLift 3932220
  have htrace : WordTrace (prefixWord ++ tailWord_3932220) baseStart_3932220 baseEnd_3932220 := by
    simpa [prefixWord, tailWord_3932220, baseEnd_3932220] using wordTrace_append hprefix tailTrace_3932220
  have hstable : (prefixWord ++ tailWord_3932220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932220).length < 2 ^ (prefixWord ++ tailWord_3932220).sum := by decide
  have hdescent : baseEnd_3932220 < baseStart_3932220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932263 : List Nat := [1, 1, 5, 1, 1, 2, 5, 6]
def baseStart_3932263 : Nat := 118140960795 + 3932263 * 2 ^ 59
def prefixEnd_3932263 : Nat := 4983230072969 + 3 ^ 40 * 3932263 * 2
def baseEnd_3932263 : Nat := 149565998436359536046545

theorem tailTrace_3932263 : CollatzResearch.WordTrace tailWord_3932263 prefixEnd_3932263 149565998436359536046545 := by
  unfold tailWord_3932263
  simp only [CollatzResearch.WordTrace]
  refine ⟨143421414153090202898529443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95614276102060135265686295 143421414153090202898529443)
  ·
    refine ⟨215132121229635304347794165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143421414153090202898529443 215132121229635304347794165)
    ·
      refine ⟨20168636365278309782605703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215132121229635304347794165 20168636365278309782605703)
      ·
        refine ⟨30252954547917464673908555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20168636365278309782605703 30252954547917464673908555)
        ·
          refine ⟨45379431821876197010862833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30252954547917464673908555 45379431821876197010862833)
          ·
            refine ⟨34034573866407147758147125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45379431821876197010862833 34034573866407147758147125)
            ·
              refine ⟨3190741299975670102326293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34034573866407147758147125 3190741299975670102326293)
              ·
                refine ⟨149565998436359536046545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3190741299975670102326293 149565998436359536046545)
                ·
                  rfl

theorem cell22_3932263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 6].length) (baseStart_3932263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932263 prefixEnd_3932263 := by exact prefixLift 3932263
  have htrace : WordTrace (prefixWord ++ tailWord_3932263) baseStart_3932263 baseEnd_3932263 := by
    simpa [prefixWord, tailWord_3932263, baseEnd_3932263] using wordTrace_append hprefix tailTrace_3932263
  have hstable : (prefixWord ++ tailWord_3932263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932263).length < 2 ^ (prefixWord ++ tailWord_3932263).sum := by decide
  have hdescent : baseEnd_3932263 < baseStart_3932263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932402 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_3932402 : Nat := 118140960795 + 3932402 * 2 ^ 59
def prefixEnd_3932402 : Nat := 4983230072969 + 3 ^ 40 * 3932402 * 2
def baseEnd_3932402 : Nat := 1346141568467885795193479

theorem tailTrace_3932402 : CollatzResearch.WordTrace tailWord_3932402 prefixEnd_3932402 1346141568467885795193479 := by
  unfold tailWord_3932402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35856620974896657409459865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95617655933057753091892973 35856620974896657409459865)
  ·
    refine ⟨26892465731172493057094899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35856620974896657409459865 26892465731172493057094899)
    ·
      refine ⟨40338698596758739585642349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26892465731172493057094899 40338698596758739585642349)
      ·
        refine ⟨15127011973784527344615881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40338698596758739585642349 15127011973784527344615881)
        ·
          refine ⟨11345258980338395508461911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15127011973784527344615881 11345258980338395508461911)
          ·
            refine ⟨17017888470507593262692867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11345258980338395508461911 17017888470507593262692867)
            ·
              refine ⟨25526832705761389894039301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17017888470507593262692867 25526832705761389894039301)
              ·
                refine ⟨4786281132330260605132369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25526832705761389894039301 4786281132330260605132369)
                ·
                  refine ⟨3589710849247695453849277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4786281132330260605132369 3589710849247695453849277)
                  ·
                    refine ⟨1346141568467885795193479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3589710849247695453849277 1346141568467885795193479)
                    ·
                      rfl

theorem cell22_3932402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_3932402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932402 prefixEnd_3932402 := by exact prefixLift 3932402
  have htrace : WordTrace (prefixWord ++ tailWord_3932402) baseStart_3932402 baseEnd_3932402 := by
    simpa [prefixWord, tailWord_3932402, baseEnd_3932402] using wordTrace_append hprefix tailTrace_3932402
  have hstable : (prefixWord ++ tailWord_3932402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932402).length < 2 ^ (prefixWord ++ tailWord_3932402).sum := by decide
  have hdescent : baseEnd_3932402 < baseStart_3932402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932428 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_3932428 : Nat := 118140960795 + 3932428 * 2 ^ 59
def prefixEnd_3932428 : Nat := 4983230072969 + 3 ^ 40 * 3932428 * 2
def baseEnd_3932428 : Nat := 1346150468799230394043399

theorem tailTrace_3932428 : CollatzResearch.WordTrace tailWord_3932428 prefixEnd_3932428 1346150468799230394043399 := by
  unfold tailWord_3932428
  simp only [CollatzResearch.WordTrace]
  refine ⟨71713716098746218039142969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95618288131661624052190625 71713716098746218039142969)
  ·
    refine ⟨53785287074059663529357227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71713716098746218039142969 53785287074059663529357227)
    ·
      refine ⟨80677930611089495294035841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53785287074059663529357227 80677930611089495294035841)
      ·
        refine ⟨60508447958317121470526881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80677930611089495294035841 60508447958317121470526881)
        ·
          refine ⟨45381335968737841102895161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60508447958317121470526881 45381335968737841102895161)
          ·
            refine ⟨34036001976553380827171371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45381335968737841102895161 34036001976553380827171371)
            ·
              refine ⟨51054002964830071240757057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34036001976553380827171371 51054002964830071240757057)
              ·
                refine ⟨38290502223622553430567793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51054002964830071240757057 38290502223622553430567793)
                ·
                  refine ⟨28717876667716915072925845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38290502223622553430567793 28717876667716915072925845)
                  ·
                    refine ⟨1346150468799230394043399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28717876667716915072925845 1346150468799230394043399)
                    ·
                      rfl

theorem cell22_3932428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_3932428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932428 prefixEnd_3932428 := by exact prefixLift 3932428
  have htrace : WordTrace (prefixWord ++ tailWord_3932428) baseStart_3932428 baseEnd_3932428 := by
    simpa [prefixWord, tailWord_3932428, baseEnd_3932428] using wordTrace_append hprefix tailTrace_3932428
  have hstable : (prefixWord ++ tailWord_3932428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932428).length < 2 ^ (prefixWord ++ tailWord_3932428).sum := by decide
  have hdescent : baseEnd_3932428 < baseStart_3932428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932460 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 5]
def baseStart_3932460 : Nat := 118140960795 + 3932460 * 2 ^ 59
def prefixEnd_3932460 : Nat := 4983230072969 + 3 ^ 40 * 3932460 * 2
def baseEnd_3932460 : Nat := 448720474351064325747767

theorem tailTrace_3932460 : CollatzResearch.WordTrace tailWord_3932460 prefixEnd_3932460 448720474351064325747767 := by
  unfold tailWord_3932460
  simp only [CollatzResearch.WordTrace]
  refine ⟨71714299666688252771725417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95619066222251003695633889 71714299666688252771725417)
  ·
    refine ⟨53785724750016189578794063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71714299666688252771725417 53785724750016189578794063)
    ·
      refine ⟨80678587125024284368191095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53785724750016189578794063 80678587125024284368191095)
      ·
        refine ⟨121017880687536426552286643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80678587125024284368191095 121017880687536426552286643)
        ·
          refine ⟨181526821031304639828429965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121017880687536426552286643 181526821031304639828429965)
          ·
            refine ⟨68072557886739239935661237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181526821031304639828429965 68072557886739239935661237)
            ·
              refine ⟨6381802301881803743968241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68072557886739239935661237 6381802301881803743968241)
              ·
                refine ⟨4786351726411352807976181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6381802301881803743968241 4786351726411352807976181)
                ·
                  refine ⟨448720474351064325747767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4786351726411352807976181 448720474351064325747767)
                  ·
                    rfl

theorem cell22_3932460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_3932460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932460 prefixEnd_3932460 := by exact prefixLift 3932460
  have htrace : WordTrace (prefixWord ++ tailWord_3932460) baseStart_3932460 baseEnd_3932460 := by
    simpa [prefixWord, tailWord_3932460, baseEnd_3932460] using wordTrace_append hprefix tailTrace_3932460
  have hstable : (prefixWord ++ tailWord_3932460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932460).length < 2 ^ (prefixWord ++ tailWord_3932460).sum := by decide
  have hdescent : baseEnd_3932460 < baseStart_3932460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932522 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_3932522 : Nat := 118140960795 + 3932522 * 2 ^ 59
def prefixEnd_3932522 : Nat := 4983230072969 + 3 ^ 40 * 3932522 * 2
def baseEnd_3932522 : Nat := 448727548973415160731037

theorem tailTrace_3932522 : CollatzResearch.WordTrace tailWord_3932522 prefixEnd_3932522 448727548973415160731037 := by
  unfold tailWord_3932522
  simp only [CollatzResearch.WordTrace]
  refine ⟨35857715164787972533051955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95620573772767926754805213 35857715164787972533051955)
  ·
    refine ⟨53786572747181958799577933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35857715164787972533051955 53786572747181958799577933)
    ·
      refine ⟨20169964780193234549841725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53786572747181958799577933 20169964780193234549841725)
      ·
        refine ⟨7563736792572462956190647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20169964780193234549841725 7563736792572462956190647)
        ·
          refine ⟨11345605188858694434285971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7563736792572462956190647 11345605188858694434285971)
          ·
            refine ⟨17018407783288041651428957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11345605188858694434285971 17018407783288041651428957)
            ·
              refine ⟨6381902918733015619285859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17018407783288041651428957 6381902918733015619285859)
              ·
                refine ⟨9572854378099523428928789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6381902918733015619285859 9572854378099523428928789)
                ·
                  refine ⟨448727548973415160731037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9572854378099523428928789 448727548973415160731037)
                  ·
                    rfl

theorem cell22_3932522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_3932522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932522 prefixEnd_3932522 := by exact prefixLift 3932522
  have htrace : WordTrace (prefixWord ++ tailWord_3932522) baseStart_3932522 baseEnd_3932522 := by
    simpa [prefixWord, tailWord_3932522, baseEnd_3932522] using wordTrace_append hprefix tailTrace_3932522
  have hstable : (prefixWord ++ tailWord_3932522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932522).length < 2 ^ (prefixWord ++ tailWord_3932522).sum := by decide
  have hdescent : baseEnd_3932522 < baseStart_3932522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932552 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 2, 4]
def baseStart_3932552 : Nat := 118140960795 + 3932552 * 2 ^ 59
def prefixEnd_3932552 : Nat := 4983230072969 + 3 ^ 40 * 3932552 * 2
def baseEnd_3932552 : Nat := 1346192916533335403943019

theorem tailTrace_3932552 : CollatzResearch.WordTrace tailWord_3932552 prefixEnd_3932552 1346192916533335403943019 := by
  unfold tailWord_3932552
  simp only [CollatzResearch.WordTrace]
  refine ⟨71715977424521602627899955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95621303232695470170533273 71715977424521602627899955)
  ·
    refine ⟨107573966136782403941849933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71715977424521602627899955 107573966136782403941849933)
    ·
      refine ⟨40340237301293401478193725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107573966136782403941849933 40340237301293401478193725)
      ·
        refine ⟨15127588987985025554322647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40340237301293401478193725 15127588987985025554322647)
        ·
          refine ⟨22691383481977538331483971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15127588987985025554322647 22691383481977538331483971)
          ·
            refine ⟨34037075222966307497225957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22691383481977538331483971 34037075222966307497225957)
            ·
              refine ⟨6381951604306182655729867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34037075222966307497225957 6381951604306182655729867)
              ·
                refine ⟨9572927406459273983594801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6381951604306182655729867 9572927406459273983594801)
                ·
                  refine ⟨7179695554844455487696101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9572927406459273983594801 7179695554844455487696101)
                  ·
                    refine ⟨1346192916533335403943019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7179695554844455487696101 1346192916533335403943019)
                    ·
                      rfl

theorem cell22_3932552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_3932552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932552 prefixEnd_3932552 := by exact prefixLift 3932552
  have htrace : WordTrace (prefixWord ++ tailWord_3932552) baseStart_3932552 baseEnd_3932552 := by
    simpa [prefixWord, tailWord_3932552, baseEnd_3932552] using wordTrace_append hprefix tailTrace_3932552
  have hstable : (prefixWord ++ tailWord_3932552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932552).length < 2 ^ (prefixWord ++ tailWord_3932552).sum := by decide
  have hdescent : baseEnd_3932552 < baseStart_3932552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932554 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 1, 5]
def baseStart_3932554 : Nat := 118140960795 + 3932554 * 2 ^ 59
def prefixEnd_3932554 : Nat := 4983230072969 + 3 ^ 40 * 3932554 * 2
def baseEnd_3932554 : Nat := 1346193601174208065393013

theorem tailTrace_3932554 : CollatzResearch.WordTrace tailWord_3932554 prefixEnd_3932554 1346193601174208065393013 := by
  unfold tailWord_3932554
  simp only [CollatzResearch.WordTrace]
  refine ⟨35858006948758989899343179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95621351863357306398248477 35858006948758989899343179)
  ·
    refine ⟨53787010423138484849014769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35858006948758989899343179 53787010423138484849014769)
    ·
      refine ⟨40340257817353863636761077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53787010423138484849014769 40340257817353863636761077)
      ·
        refine ⟨3781899170376924715946351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40340257817353863636761077 3781899170376924715946351)
        ·
          refine ⟨5672848755565387073919527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781899170376924715946351 5672848755565387073919527)
          ·
            refine ⟨8509273133348080610879291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5672848755565387073919527 8509273133348080610879291)
            ·
              refine ⟨12763909700022120916318937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8509273133348080610879291 12763909700022120916318937)
              ·
                refine ⟨9572932275016590687239203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12763909700022120916318937 9572932275016590687239203)
                ·
                  refine ⟨14359398412524886030858805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9572932275016590687239203 14359398412524886030858805)
                  ·
                    refine ⟨1346193601174208065393013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14359398412524886030858805 1346193601174208065393013)
                    ·
                      rfl

theorem cell22_3932554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_3932554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932554 prefixEnd_3932554 := by exact prefixLift 3932554
  have htrace : WordTrace (prefixWord ++ tailWord_3932554) baseStart_3932554 baseEnd_3932554 := by
    simpa [prefixWord, tailWord_3932554, baseEnd_3932554] using wordTrace_append hprefix tailTrace_3932554
  have hstable : (prefixWord ++ tailWord_3932554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932554).length < 2 ^ (prefixWord ++ tailWord_3932554).sum := by decide
  have hdescent : baseEnd_3932554 < baseStart_3932554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932573 : List Nat := [1, 4, 2, 1, 5, 1, 2, 2, 4]
def baseStart_3932573 : Nat := 118140960795 + 3932573 * 2 ^ 59
def prefixEnd_3932573 : Nat := 4983230072969 + 3 ^ 40 * 3932573 * 2
def baseEnd_3932573 : Nat := 448733368420832783055985

theorem tailTrace_3932573 : CollatzResearch.WordTrace tailWord_3932573 prefixEnd_3932573 448733368420832783055985 := by
  unfold tailWord_3932573
  simp only [CollatzResearch.WordTrace]
  refine ⟨143432720781967125842314373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95621813854644750561542915 143432720781967125842314373)
  ·
    refine ⟨26893635146618836095433945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143432720781967125842314373 26893635146618836095433945)
    ·
      refine ⟨20170226359964127071575459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26893635146618836095433945 20170226359964127071575459)
      ·
        refine ⟨30255339539946190607363189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20170226359964127071575459 30255339539946190607363189)
        ·
          refine ⟨2836438081869955369440299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30255339539946190607363189 2836438081869955369440299)
          ·
            refine ⟨4254657122804933054160449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836438081869955369440299 4254657122804933054160449)
            ·
              refine ⟨3190992842103699790620337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4254657122804933054160449 3190992842103699790620337)
              ·
                refine ⟨2393244631577774842965253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3190992842103699790620337 2393244631577774842965253)
                ·
                  refine ⟨448733368420832783055985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393244631577774842965253 448733368420832783055985)
                  ·
                    rfl

theorem cell22_3932573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_3932573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932573 prefixEnd_3932573 := by exact prefixLift 3932573
  have htrace : WordTrace (prefixWord ++ tailWord_3932573) baseStart_3932573 baseEnd_3932573 := by
    simpa [prefixWord, tailWord_3932573, baseEnd_3932573] using wordTrace_append hprefix tailTrace_3932573
  have hstable : (prefixWord ++ tailWord_3932573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932573).length < 2 ^ (prefixWord ++ tailWord_3932573).sum := by decide
  have hdescent : baseEnd_3932573 < baseStart_3932573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932580 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_3932580 : Nat := 118140960795 + 3932580 * 2 ^ 59
def prefixEnd_3932580 : Nat := 4983230072969 + 3 ^ 40 * 3932580 * 2
def baseEnd_3932580 : Nat := 1346202501505552664242933

theorem tailTrace_3932580 : CollatzResearch.WordTrace tailWord_3932580 prefixEnd_3932580 1346202501505552664242933 := by
  unfold tailWord_3932580
  simp only [CollatzResearch.WordTrace]
  refine ⟨71716488046470883018909597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95621984061961177358546129 71716488046470883018909597)
  ·
    refine ⟨26893683017426581132091099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71716488046470883018909597 26893683017426581132091099)
    ·
      refine ⟨40340524526139871698136649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26893683017426581132091099 40340524526139871698136649)
      ·
        refine ⟨30255393394604903773602487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40340524526139871698136649 30255393394604903773602487)
        ·
          refine ⟨45383090091907355660403731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30255393394604903773602487 45383090091907355660403731)
          ·
            refine ⟨68074635137861033490605597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45383090091907355660403731 68074635137861033490605597)
            ·
              refine ⟨25527988176697887558977099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68074635137861033490605597 25527988176697887558977099)
              ·
                refine ⟨38291982265046831338465649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25527988176697887558977099 38291982265046831338465649)
                ·
                  refine ⟨28718986698785123503849237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38291982265046831338465649 28718986698785123503849237)
                  ·
                    refine ⟨1346202501505552664242933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28718986698785123503849237 1346202501505552664242933)
                    ·
                      rfl

theorem cell22_3932580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_3932580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932580 prefixEnd_3932580 := by exact prefixLift 3932580
  have htrace : WordTrace (prefixWord ++ tailWord_3932580) baseStart_3932580 baseEnd_3932580 := by
    simpa [prefixWord, tailWord_3932580, baseEnd_3932580] using wordTrace_append hprefix tailTrace_3932580
  have hstable : (prefixWord ++ tailWord_3932580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932580).length < 2 ^ (prefixWord ++ tailWord_3932580).sum := by decide
  have hdescent : baseEnd_3932580 < baseStart_3932580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932584 : List Nat := [2, 1, 6, 1, 1, 3, 1, 7]
def baseStart_3932584 : Nat := 118140960795 + 3932584 * 2 ^ 59
def prefixEnd_3932584 : Nat := 4983230072969 + 3 ^ 40 * 3932584 * 2
def baseEnd_3932584 : Nat := 149578207865255331904769

theorem tailTrace_3932584 : CollatzResearch.WordTrace tailWord_3932584 prefixEnd_3932584 149578207865255331904769 := by
  unfold tailWord_3932584
  simp only [CollatzResearch.WordTrace]
  refine ⟨71716560992463637360482403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95622081323284849813976537 71716560992463637360482403)
  ·
    refine ⟨107574841488695456040723605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71716560992463637360482403 107574841488695456040723605)
    ·
      refine ⟨5042570694782599501908919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107574841488695456040723605 5042570694782599501908919)
      ·
        refine ⟨7563856042173899252863379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5042570694782599501908919 7563856042173899252863379)
        ·
          refine ⟨11345784063260848879295069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7563856042173899252863379 11345784063260848879295069)
          ·
            refine ⟨4254669023722818329735651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11345784063260848879295069 4254669023722818329735651)
            ·
              refine ⟨6382003535584227494603477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4254669023722818329735651 6382003535584227494603477)
              ·
                refine ⟨149578207865255331904769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6382003535584227494603477 149578207865255331904769)
                ·
                  rfl

theorem cell22_3932584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 7].length) (baseStart_3932584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932584 prefixEnd_3932584 := by exact prefixLift 3932584
  have htrace : WordTrace (prefixWord ++ tailWord_3932584) baseStart_3932584 baseEnd_3932584 := by
    simpa [prefixWord, tailWord_3932584, baseEnd_3932584] using wordTrace_append hprefix tailTrace_3932584
  have hstable : (prefixWord ++ tailWord_3932584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932584).length < 2 ^ (prefixWord ++ tailWord_3932584).sum := by decide
  have hdescent : baseEnd_3932584 < baseStart_3932584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932616 : List Nat := [2, 1, 3, 1, 3, 3, 2, 3, 1, 3]
def baseStart_3932616 : Nat := 118140960795 + 3932616 * 2 ^ 59
def prefixEnd_3932616 : Nat := 4983230072969 + 3 ^ 40 * 3932616 * 2
def baseEnd_3932616 : Nat := 1346214825041260570342823

theorem tailTrace_3932616 : CollatzResearch.WordTrace tailWord_3932616 prefixEnd_3932616 1346214825041260570342823 := by
  unfold tailWord_3932616
  simp only [CollatzResearch.WordTrace]
  refine ⟨71717144560405672093064851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95622859413874229457419801 71717144560405672093064851)
  ·
    refine ⟨107575716840608508139597277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71717144560405672093064851 107575716840608508139597277)
    ·
      refine ⟨40340893815228190552348979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107575716840608508139597277 40340893815228190552348979)
      ·
        refine ⟨60511340722842285828523469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40340893815228190552348979 60511340722842285828523469)
        ·
          refine ⟨22691752771065857185696301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60511340722842285828523469 22691752771065857185696301)
          ·
            refine ⟨8509407289149696444636113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22691752771065857185696301 8509407289149696444636113)
            ·
              refine ⟨6382055466862272333477085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8509407289149696444636113 6382055466862272333477085)
              ·
                refine ⟨2393270800073352125053907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6382055466862272333477085 2393270800073352125053907)
                ·
                  refine ⟨3589906200110028187580861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393270800073352125053907 3589906200110028187580861)
                  ·
                    refine ⟨1346214825041260570342823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3589906200110028187580861 1346214825041260570342823)
                    ·
                      rfl

theorem cell22_3932616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_3932616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932616 prefixEnd_3932616 := by exact prefixLift 3932616
  have htrace : WordTrace (prefixWord ++ tailWord_3932616) baseStart_3932616 baseEnd_3932616 := by
    simpa [prefixWord, tailWord_3932616, baseEnd_3932616] using wordTrace_append hprefix tailTrace_3932616
  have hstable : (prefixWord ++ tailWord_3932616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932616).length < 2 ^ (prefixWord ++ tailWord_3932616).sum := by decide
  have hdescent : baseEnd_3932616 < baseStart_3932616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932629 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 5]
def baseStart_3932629 : Nat := 118140960795 + 3932629 * 2 ^ 59
def prefixEnd_3932629 : Nat := 4983230072969 + 3 ^ 40 * 3932629 * 2
def baseEnd_3932629 : Nat := 448739758402310956589261

theorem tailTrace_3932629 : CollatzResearch.WordTrace tailWord_3932629 prefixEnd_3932629 448739758402310956589261 := by
  unfold tailWord_3932629
  simp only [CollatzResearch.WordTrace]
  refine ⟨143434763269764247406352941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95623175513176164937568627 143434763269764247406352941)
  ·
    refine ⟨53788036226161592777382353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143434763269764247406352941 53788036226161592777382353)
    ·
      refine ⟨40341027169621194583036765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53788036226161592777382353 40341027169621194583036765)
      ·
        refine ⟨15127885188607947968638787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40341027169621194583036765 15127885188607947968638787)
        ·
          refine ⟨22691827782911921952958181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15127885188607947968638787 22691827782911921952958181)
          ·
            refine ⟨4254717709295985366179659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22691827782911921952958181 4254717709295985366179659)
            ·
              refine ⟨6382076563943978049269489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4254717709295985366179659 6382076563943978049269489)
              ·
                refine ⟨4786557422957983536952117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6382076563943978049269489 4786557422957983536952117)
                ·
                  refine ⟨448739758402310956589261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4786557422957983536952117 448739758402310956589261)
                  ·
                    rfl

theorem cell22_3932629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_3932629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932629 prefixEnd_3932629 := by exact prefixLift 3932629
  have htrace : WordTrace (prefixWord ++ tailWord_3932629) baseStart_3932629 baseEnd_3932629 := by
    simpa [prefixWord, tailWord_3932629, baseEnd_3932629] using wordTrace_append hprefix tailTrace_3932629
  have hstable : (prefixWord ++ tailWord_3932629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932629).length < 2 ^ (prefixWord ++ tailWord_3932629).sum := by decide
  have hdescent : baseEnd_3932629 < baseStart_3932629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932747 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 5]
def baseStart_3932747 : Nat := 118140960795 + 3932747 * 2 ^ 59
def prefixEnd_3932747 : Nat := 4983230072969 + 3 ^ 40 * 3932747 * 2
def baseEnd_3932747 : Nat := 448753223006139965105807

theorem tailTrace_3932747 : CollatzResearch.WordTrace tailWord_3932747 prefixEnd_3932747 448753223006139965105807 := by
  unfold tailWord_3932747
  simp only [CollatzResearch.WordTrace]
  refine ⟨143439067083336753559148495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95626044722224502372765663 143439067083336753559148495)
  ·
    refine ⟨215158600625005130338722743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143439067083336753559148495 215158600625005130338722743)
    ·
      refine ⟨322737900937507695508084115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215158600625005130338722743 322737900937507695508084115)
      ·
        refine ⟨484106851406261543262126173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322737900937507695508084115 484106851406261543262126173)
        ·
          refine ⟨181540069277348078723297315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484106851406261543262126173 181540069277348078723297315)
          ·
            refine ⟨272310103916022118084945973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181540069277348078723297315 272310103916022118084945973)
            ·
              refine ⟨25529072242127073570463685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272310103916022118084945973 25529072242127073570463685)
              ·
                refine ⟨4786701045398826294461941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25529072242127073570463685 4786701045398826294461941)
                ·
                  refine ⟨448753223006139965105807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4786701045398826294461941 448753223006139965105807)
                  ·
                    rfl

theorem cell22_3932747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 5].length) (baseStart_3932747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932747 prefixEnd_3932747 := by exact prefixLift 3932747
  have htrace : WordTrace (prefixWord ++ tailWord_3932747) baseStart_3932747 baseEnd_3932747 := by
    simpa [prefixWord, tailWord_3932747, baseEnd_3932747] using wordTrace_append hprefix tailTrace_3932747
  have hstable : (prefixWord ++ tailWord_3932747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932747).length < 2 ^ (prefixWord ++ tailWord_3932747).sum := by decide
  have hdescent : baseEnd_3932747 < baseStart_3932747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932749 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3932749 : Nat := 118140960795 + 3932749 * 2 ^ 59
def prefixEnd_3932749 : Nat := 4983230072969 + 3 ^ 40 * 3932749 * 2
def baseEnd_3932749 : Nat := 1346260353659292556767415

theorem tailTrace_3932749 : CollatzResearch.WordTrace tailWord_3932749 prefixEnd_3932749 1346260353659292556767415 := by
  unfold tailWord_3932749
  simp only [CollatzResearch.WordTrace]
  refine ⟨143439140029329507900721301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95626093352886338600480867 143439140029329507900721301)
  ·
    refine ⟨6723709688874820682846311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143439140029329507900721301 6723709688874820682846311)
    ·
      refine ⟨10085564533312231024269467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6723709688874820682846311 10085564533312231024269467)
      ·
        refine ⟨15128346799968346536404201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10085564533312231024269467 15128346799968346536404201)
        ·
          refine ⟨11346260099976259902303151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15128346799968346536404201 11346260099976259902303151)
          ·
            refine ⟨17019390149964389853454727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11346260099976259902303151 17019390149964389853454727)
            ·
              refine ⟨25529085224946584780182091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17019390149964389853454727 25529085224946584780182091)
              ·
                refine ⟨38293627837419877170273137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25529085224946584780182091 38293627837419877170273137)
                ·
                  refine ⟨28720220878064907877704853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38293627837419877170273137 28720220878064907877704853)
                  ·
                    refine ⟨1346260353659292556767415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28720220878064907877704853 1346260353659292556767415)
                    ·
                      rfl

theorem cell22_3932749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3932749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932749 prefixEnd_3932749 := by exact prefixLift 3932749
  have htrace : WordTrace (prefixWord ++ tailWord_3932749) baseStart_3932749 baseEnd_3932749 := by
    simpa [prefixWord, tailWord_3932749, baseEnd_3932749] using wordTrace_append hprefix tailTrace_3932749
  have hstable : (prefixWord ++ tailWord_3932749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932749).length < 2 ^ (prefixWord ++ tailWord_3932749).sum := by decide
  have hdescent : baseEnd_3932749 < baseStart_3932749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3932802 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3932802 : Nat := 118140960795 + 3932802 * 2 ^ 59
def prefixEnd_3932802 : Nat := 4983230072969 + 3 ^ 40 * 3932802 * 2
def baseEnd_3932802 : Nat := 1346278496642418085192253

theorem tailTrace_3932802 : CollatzResearch.WordTrace tailWord_3932802 prefixEnd_3932802 1346278496642418085192253 := by
  unfold tailWord_3932802
  simp only [CollatzResearch.WordTrace]
  refine ⟨35860268274534374488100165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95627382065424998634933773 35860268274534374488100165)
  ·
    refine ⟨6723800301475195216518781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35860268274534374488100165 6723800301475195216518781)
    ·
      refine ⟨2521425113053198206194543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6723800301475195216518781 2521425113053198206194543)
      ·
        refine ⟨3782137669579797309291815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2521425113053198206194543 3782137669579797309291815)
        ·
          refine ⟨5673206504369695963937723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3782137669579797309291815 5673206504369695963937723)
          ·
            refine ⟨8509809756554543945906585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673206504369695963937723 8509809756554543945906585)
            ·
              refine ⟨6382357317415907959429939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8509809756554543945906585 6382357317415907959429939)
              ·
                refine ⟨9573535976123861939144909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6382357317415907959429939 9573535976123861939144909)
                ·
                  refine ⟨3590075991046448227179341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9573535976123861939144909 3590075991046448227179341)
                  ·
                    refine ⟨1346278496642418085192253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3590075991046448227179341 1346278496642418085192253)
                    ·
                      rfl

theorem cell22_3932802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3932802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3932802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3932802 prefixEnd_3932802 := by exact prefixLift 3932802
  have htrace : WordTrace (prefixWord ++ tailWord_3932802) baseStart_3932802 baseEnd_3932802 := by
    simpa [prefixWord, tailWord_3932802, baseEnd_3932802] using wordTrace_append hprefix tailTrace_3932802
  have hstable : (prefixWord ++ tailWord_3932802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3932802).length < 2 ^ (prefixWord ++ tailWord_3932802).sum := by decide
  have hdescent : baseEnd_3932802 < baseStart_3932802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3932802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933012 : List Nat := [2, 4, 1, 1, 5, 1, 1, 3, 4]
def baseStart_3933012 : Nat := 118140960795 + 3933012 * 2 ^ 59
def prefixEnd_3933012 : Nat := 4983230072969 + 3 ^ 40 * 3933012 * 2
def baseEnd_3933012 : Nat := 448783461311349179147203

theorem tailTrace_3933012 : CollatzResearch.WordTrace tailWord_3933012 prefixEnd_3933012 448783461311349179147203 := by
  unfold tailWord_3933012
  simp only [CollatzResearch.WordTrace]
  refine ⟨71724366213688351908772645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95632488284917802545030193 71724366213688351908772645)
  ·
    refine ⟨13448318665066565982894871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71724366213688351908772645 13448318665066565982894871)
    ·
      refine ⟨20172477997599848974342307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13448318665066565982894871 20172477997599848974342307)
      ·
        refine ⟨30258716996399773461513461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20172477997599848974342307 30258716996399773461513461)
        ·
          refine ⟨2836754718412478762016887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30258716996399773461513461 2836754718412478762016887)
          ·
            refine ⟨4255132077618718143025331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836754718412478762016887 4255132077618718143025331)
            ·
              refine ⟨6382698116428077214537997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255132077618718143025331 6382698116428077214537997)
              ·
                refine ⟨2393511793660528955451749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6382698116428077214537997 2393511793660528955451749)
                ·
                  refine ⟨448783461311349179147203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393511793660528955451749 448783461311349179147203)
                  ·
                    rfl

theorem cell22_3933012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_3933012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933012 prefixEnd_3933012 := by exact prefixLift 3933012
  have htrace : WordTrace (prefixWord ++ tailWord_3933012) baseStart_3933012 baseEnd_3933012 := by
    simpa [prefixWord, tailWord_3933012, baseEnd_3933012] using wordTrace_append hprefix tailTrace_3933012
  have hstable : (prefixWord ++ tailWord_3933012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933012).length < 2 ^ (prefixWord ++ tailWord_3933012).sum := by decide
  have hdescent : baseEnd_3933012 < baseStart_3933012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933089 : List Nat := [1, 2, 3, 4, 1, 3, 2, 2, 1, 3]
def baseStart_3933089 : Nat := 118140960795 + 3933089 * 2 ^ 59
def prefixEnd_3933089 : Nat := 4983230072969 + 3 ^ 40 * 3933089 * 2
def baseEnd_3933089 : Nat := 1346376742607645003266373

theorem tailTrace_3933089 : CollatzResearch.WordTrace tailWord_3933089 prefixEnd_3933089 1346376742607645003266373 := by
  unfold tailWord_3933089
  simp only [CollatzResearch.WordTrace]
  refine ⟨143451540848097745968098321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95634360565398497312065547 143451540848097745968098321)
  ·
    refine ⟨107588655636073309476073741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143451540848097745968098321 107588655636073309476073741)
    ·
      refine ⟨40345745863527491053527653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107588655636073309476073741 40345745863527491053527653)
      ·
        refine ⟨7564827349411404572536435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40345745863527491053527653 7564827349411404572536435)
        ·
          refine ⟨11347241024117106858804653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564827349411404572536435 11347241024117106858804653)
          ·
            refine ⟨4255215384043915072051745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11347241024117106858804653 4255215384043915072051745)
            ·
              refine ⟨3191411538032936304038809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255215384043915072051745 3191411538032936304038809)
              ·
                refine ⟨2393558653524702228029107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191411538032936304038809 2393558653524702228029107)
                ·
                  refine ⟨3590337980287053342043661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393558653524702228029107 3590337980287053342043661)
                  ·
                    refine ⟨1346376742607645003266373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3590337980287053342043661 1346376742607645003266373)
                    ·
                      rfl

theorem cell22_3933089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_3933089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933089 prefixEnd_3933089 := by exact prefixLift 3933089
  have htrace : WordTrace (prefixWord ++ tailWord_3933089) baseStart_3933089 baseEnd_3933089 := by
    simpa [prefixWord, tailWord_3933089, baseEnd_3933089] using wordTrace_append hprefix tailTrace_3933089
  have hstable : (prefixWord ++ tailWord_3933089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933089).length < 2 ^ (prefixWord ++ tailWord_3933089).sum := by decide
  have hdescent : baseEnd_3933089 < baseStart_3933089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933111 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 1, 5]
def baseStart_3933111 : Nat := 118140960795 + 3933111 * 2 ^ 59
def prefixEnd_3933111 : Nat := 4983230072969 + 3 ^ 40 * 3933111 * 2
def baseEnd_3933111 : Nat := 1346384273657244279216305

theorem tailTrace_3933111 : CollatzResearch.WordTrace tailWord_3933111 prefixEnd_3933111 1346384273657244279216305 := by
  unfold tailWord_3933111
  simp only [CollatzResearch.WordTrace]
  refine ⟨143452343254018043725399187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95634895502678695816932791 143452343254018043725399187)
  ·
    refine ⟨215178514881027065588098781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143452343254018043725399187 215178514881027065588098781)
    ·
      refine ⟨80691943080385149595537043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215178514881027065588098781 80691943080385149595537043)
      ·
        refine ⟨121037914620577724393305565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80691943080385149595537043 121037914620577724393305565)
        ·
          refine ⟨45389217982716646647489587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121037914620577724393305565 45389217982716646647489587)
          ·
            refine ⟨68083826974074969971234381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45389217982716646647489587 68083826974074969971234381)
            ·
              refine ⟨25531435115278113739212893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68083826974074969971234381 25531435115278113739212893)
              ·
                refine ⟨9574288168229292652204835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25531435115278113739212893 9574288168229292652204835)
                ·
                  refine ⟨14361432252343938978307253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9574288168229292652204835 14361432252343938978307253)
                  ·
                    refine ⟨1346384273657244279216305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14361432252343938978307253 1346384273657244279216305)
                    ·
                      rfl

theorem cell22_3933111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_3933111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933111 prefixEnd_3933111 := by exact prefixLift 3933111
  have htrace : WordTrace (prefixWord ++ tailWord_3933111) baseStart_3933111 baseEnd_3933111 := by
    simpa [prefixWord, tailWord_3933111, baseEnd_3933111] using wordTrace_append hprefix tailTrace_3933111
  have hstable : (prefixWord ++ tailWord_3933111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933111).length < 2 ^ (prefixWord ++ tailWord_3933111).sum := by decide
  have hdescent : baseEnd_3933111 < baseStart_3933111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933145 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 2, 3]
def baseStart_3933145 : Nat := 118140960795 + 3933145 * 2 ^ 59
def prefixEnd_3933145 : Nat := 4983230072969 + 3 ^ 40 * 3933145 * 2
def baseEnd_3933145 : Nat := 1346395912552079523866201

theorem tailTrace_3933145 : CollatzResearch.WordTrace tailWord_3933145 prefixEnd_3933145 1346395912552079523866201 := by
  unfold tailWord_3933145
  simp only [CollatzResearch.WordTrace]
  refine ⟨143453583335894867532136889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95635722223929911688091259 143453583335894867532136889)
  ·
    refine ⟨107590187501921150649102667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143453583335894867532136889 107590187501921150649102667)
    ·
      refine ⟨161385281252881725973654001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107590187501921150649102667 161385281252881725973654001)
      ·
        refine ⟨121038960939661294480240501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161385281252881725973654001 121038960939661294480240501)
        ·
          refine ⟨11347402588093246357522547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121038960939661294480240501 11347402588093246357522547)
          ·
            refine ⟨17021103882139869536283821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11347402588093246357522547 17021103882139869536283821)
            ·
              refine ⟨6382913955802451076106433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17021103882139869536283821 6382913955802451076106433)
              ·
                refine ⟨4787185466851838307079825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6382913955802451076106433 4787185466851838307079825)
                ·
                  refine ⟨3590389100138878730309869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4787185466851838307079825 3590389100138878730309869)
                  ·
                    refine ⟨1346395912552079523866201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3590389100138878730309869 1346395912552079523866201)
                    ·
                      rfl

theorem cell22_3933145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 3].length) (baseStart_3933145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933145 prefixEnd_3933145 := by exact prefixLift 3933145
  have htrace : WordTrace (prefixWord ++ tailWord_3933145) baseStart_3933145 baseEnd_3933145 := by
    simpa [prefixWord, tailWord_3933145, baseEnd_3933145] using wordTrace_append hprefix tailTrace_3933145
  have hstable : (prefixWord ++ tailWord_3933145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933145).length < 2 ^ (prefixWord ++ tailWord_3933145).sum := by decide
  have hdescent : baseEnd_3933145 < baseStart_3933145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933162 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 2, 3]
def baseStart_3933162 : Nat := 118140960795 + 3933162 * 2 ^ 59
def prefixEnd_3933162 : Nat := 4983230072969 + 3 ^ 40 * 3933162 * 2
def baseEnd_3933162 : Nat := 1346401731999497146191149

theorem tailTrace_3933162 : CollatzResearch.WordTrace tailWord_3933162 prefixEnd_3933162 1346401731999497146191149 := by
  unfold tailWord_3933162
  simp only [CollatzResearch.WordTrace]
  refine ⟨35863550844208319858876435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95636135584555519623670493 35863550844208319858876435)
  ·
    refine ⟨53795326266312479788314653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35863550844208319858876435 53795326266312479788314653)
    ·
      refine ⟨20173247349867179920617995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53795326266312479788314653 20173247349867179920617995)
      ·
        refine ⟨30259871024800769880926993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20173247349867179920617995 30259871024800769880926993)
        ·
          refine ⟨22694903268600577410695245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30259871024800769880926993 22694903268600577410695245)
          ·
            refine ⟨8510588725725216529010717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22694903268600577410695245 8510588725725216529010717)
            ·
              refine ⟨3191470772146956198379019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8510588725725216529010717 3191470772146956198379019)
              ·
                refine ⟨4787206158220434297568529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191470772146956198379019 4787206158220434297568529)
                ·
                  refine ⟨3590404618665325723176397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4787206158220434297568529 3590404618665325723176397)
                  ·
                    refine ⟨1346401731999497146191149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3590404618665325723176397 1346401731999497146191149)
                    ·
                      rfl

theorem cell22_3933162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_3933162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933162 prefixEnd_3933162 := by exact prefixLift 3933162
  have htrace : WordTrace (prefixWord ++ tailWord_3933162) baseStart_3933162 baseEnd_3933162 := by
    simpa [prefixWord, tailWord_3933162, baseEnd_3933162] using wordTrace_append hprefix tailTrace_3933162
  have hstable : (prefixWord ++ tailWord_3933162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933162).length < 2 ^ (prefixWord ++ tailWord_3933162).sum := by decide
  have hdescent : baseEnd_3933162 < baseStart_3933162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933201 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_3933201 : Nat := 118140960795 + 3933201 * 2 ^ 59
def prefixEnd_3933201 : Nat := 4983230072969 + 3 ^ 40 * 3933201 * 2
def baseEnd_3933201 : Nat := 1346415082496514044466029

theorem tailTrace_3933201 : CollatzResearch.WordTrace tailWord_3933201 prefixEnd_3933201 1346415082496514044466029 := by
  unfold tailWord_3933201
  simp only [CollatzResearch.WordTrace]
  refine ⟨143455625823691989096175457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95637083882461326064116971 143455625823691989096175457)
  ·
    refine ⟨107591719367768991822131593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143455625823691989096175457 107591719367768991822131593)
    ·
      refine ⟨80693789525826743866598695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107591719367768991822131593 80693789525826743866598695)
      ·
        refine ⟨121040684288740115799898043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80693789525826743866598695 121040684288740115799898043)
        ·
          refine ⟨181561026433110173699847065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121040684288740115799898043 181561026433110173699847065)
          ·
            refine ⟨136170769824832630274885299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181561026433110173699847065 136170769824832630274885299)
            ·
              refine ⟨204256154737248945412327949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136170769824832630274885299 204256154737248945412327949)
              ·
                refine ⟨76596058026468354529622981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204256154737248945412327949 76596058026468354529622981)
                ·
                  refine ⟨14361760879962816474304309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76596058026468354529622981 14361760879962816474304309)
                  ·
                    refine ⟨1346415082496514044466029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14361760879962816474304309 1346415082496514044466029)
                    ·
                      rfl

theorem cell22_3933201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_3933201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933201 prefixEnd_3933201 := by exact prefixLift 3933201
  have htrace : WordTrace (prefixWord ++ tailWord_3933201) baseStart_3933201 baseEnd_3933201 := by
    simpa [prefixWord, tailWord_3933201, baseEnd_3933201] using wordTrace_append hprefix tailTrace_3933201
  have hstable : (prefixWord ++ tailWord_3933201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933201).length < 2 ^ (prefixWord ++ tailWord_3933201).sum := by decide
  have hdescent : baseEnd_3933201 < baseStart_3933201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933207 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 3, 3]
def baseStart_3933207 : Nat := 118140960795 + 3933207 * 2 ^ 59
def prefixEnd_3933207 : Nat := 4983230072969 + 3 ^ 40 * 3933207 * 2
def baseEnd_3933207 : Nat := 1346417136419132028816011

theorem tailTrace_3933207 : CollatzResearch.WordTrace tailWord_3933207 prefixEnd_3933207 1346417136419132028816011 := by
  unfold tailWord_3933207
  simp only [CollatzResearch.WordTrace]
  refine ⟨143455844661670252120893875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95637229774446834747262583 143455844661670252120893875)
  ·
    refine ⟨215183766992505378181340813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143455844661670252120893875 215183766992505378181340813)
    ·
      refine ⟨80693912622189516818002805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215183766992505378181340813 80693912622189516818002805)
      ·
        refine ⟨7565054308330267201687763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80693912622189516818002805 7565054308330267201687763)
        ·
          refine ⟨11347581462495400802531645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7565054308330267201687763 11347581462495400802531645)
          ·
            refine ⟨4255343048435775300949367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11347581462495400802531645 4255343048435775300949367)
            ·
              refine ⟨6383014572653662951424051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255343048435775300949367 6383014572653662951424051)
              ·
                refine ⟨9574521858980494427136077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383014572653662951424051 9574521858980494427136077)
                ·
                  refine ⟨3590445697117685410176029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9574521858980494427136077 3590445697117685410176029)
                  ·
                    refine ⟨1346417136419132028816011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3590445697117685410176029 1346417136419132028816011)
                    ·
                      rfl

theorem cell22_3933207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_3933207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933207 prefixEnd_3933207 := by exact prefixLift 3933207
  have htrace : WordTrace (prefixWord ++ tailWord_3933207) baseStart_3933207 baseEnd_3933207 := by
    simpa [prefixWord, tailWord_3933207, baseEnd_3933207] using wordTrace_append hprefix tailTrace_3933207
  have hstable : (prefixWord ++ tailWord_3933207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933207).length < 2 ^ (prefixWord ++ tailWord_3933207).sum := by decide
  have hdescent : baseEnd_3933207 < baseStart_3933207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933220 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 5]
def baseStart_3933220 : Nat := 118140960795 + 3933220 * 2 ^ 59
def prefixEnd_3933220 : Nat := 4983230072969 + 3 ^ 40 * 3933220 * 2
def baseEnd_3933220 : Nat := 448807195528268109413657

theorem tailTrace_3933220 : CollatzResearch.WordTrace tailWord_3933220 prefixEnd_3933220 448807195528268109413657 := by
  unfold tailWord_3933220
  simp only [CollatzResearch.WordTrace]
  refine ⟨71728159405311577670558557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95637545873748770227411409 71728159405311577670558557)
  ·
    refine ⟨26898059776991841626459459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71728159405311577670558557 26898059776991841626459459)
    ·
      refine ⟨40347089665487762439689189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26898059776991841626459459 40347089665487762439689189)
      ·
        refine ⟨7565079312278955457441723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40347089665487762439689189 7565079312278955457441723)
        ·
          refine ⟨11347618968418433186162585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7565079312278955457441723 11347618968418433186162585)
          ·
            refine ⟨8510714226313824889621939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11347618968418433186162585 8510714226313824889621939)
            ·
              refine ⟨12766071339470737334432909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8510714226313824889621939 12766071339470737334432909)
              ·
                refine ⟨4787276752301526500412341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12766071339470737334432909 4787276752301526500412341)
                ·
                  refine ⟨448807195528268109413657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4787276752301526500412341 448807195528268109413657)
                  ·
                    rfl

theorem cell22_3933220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_3933220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933220 prefixEnd_3933220 := by exact prefixLift 3933220
  have htrace : WordTrace (prefixWord ++ tailWord_3933220) baseStart_3933220 baseEnd_3933220 := by
    simpa [prefixWord, tailWord_3933220, baseEnd_3933220] using wordTrace_append hprefix tailTrace_3933220
  have hstable : (prefixWord ++ tailWord_3933220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933220).length < 2 ^ (prefixWord ++ tailWord_3933220).sum := by decide
  have hdescent : baseEnd_3933220 < baseStart_3933220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933233 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_3933233 : Nat := 118140960795 + 3933233 * 2 ^ 59
def prefixEnd_3933233 : Nat := 4983230072969 + 3 ^ 40 * 3933233 * 2
def baseEnd_3933233 : Nat := 1346426036750476627665931

theorem tailTrace_3933233 : CollatzResearch.WordTrace tailWord_3933233 prefixEnd_3933233 1346426036750476627665931 := by
  unfold tailWord_3933233
  simp only [CollatzResearch.WordTrace]
  refine ⟨143456792959576058561340353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95637861973050705707560235 143456792959576058561340353)
  ·
    refine ⟨107592594719682043921005265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143456792959576058561340353 107592594719682043921005265)
    ·
      refine ⟨80694446039761532940753949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107592594719682043921005265 80694446039761532940753949)
      ·
        refine ⟨30260417264910574852782731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80694446039761532940753949 30260417264910574852782731)
        ·
          refine ⟨45390625897365862279174097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30260417264910574852782731 45390625897365862279174097)
          ·
            refine ⟨34042969423024396709380573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45390625897365862279174097 34042969423024396709380573)
            ·
              refine ⟨12766113533634148766017715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34042969423024396709380573 12766113533634148766017715)
              ·
                refine ⟨19149170300451223149026573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12766113533634148766017715 19149170300451223149026573)
                ·
                  refine ⟨7180938862669208680884965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19149170300451223149026573 7180938862669208680884965)
                  ·
                    refine ⟨1346426036750476627665931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7180938862669208680884965 1346426036750476627665931)
                    ·
                      rfl

theorem cell22_3933233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_3933233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933233 prefixEnd_3933233 := by exact prefixLift 3933233
  have htrace : WordTrace (prefixWord ++ tailWord_3933233) baseStart_3933233 baseEnd_3933233 := by
    simpa [prefixWord, tailWord_3933233, baseEnd_3933233] using wordTrace_append hprefix tailTrace_3933233
  have hstable : (prefixWord ++ tailWord_3933233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933233).length < 2 ^ (prefixWord ++ tailWord_3933233).sum := by decide
  have hdescent : baseEnd_3933233 < baseStart_3933233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933280 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 2, 3]
def baseStart_3933280 : Nat := 118140960795 + 3933280 * 2 ^ 59
def prefixEnd_3933280 : Nat := 4983230072969 + 3 ^ 40 * 3933280 * 2
def baseEnd_3933280 : Nat := 1346442125810984171740787

theorem tailTrace_3933280 : CollatzResearch.WordTrace tailWord_3933280 prefixEnd_3933280 1346442125810984171740787 := by
  unfold tailWord_3933280
  simp only [CollatzResearch.WordTrace]
  refine ⟨71729253595202892794150647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95639004793603857058867529 71729253595202892794150647)
  ·
    refine ⟨107593880392804339191225971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71729253595202892794150647 107593880392804339191225971)
    ·
      refine ⟨161390820589206508786838957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107593880392804339191225971 161390820589206508786838957)
      ·
        refine ⟨60521557720952440795064609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161390820589206508786838957 60521557720952440795064609)
        ·
          refine ⟨45391168290714330596298457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60521557720952440795064609 45391168290714330596298457)
          ·
            refine ⟨34043376218035747947223843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45391168290714330596298457 34043376218035747947223843)
            ·
              refine ⟨51065064327053621920835765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34043376218035747947223843 51065064327053621920835765)
              ·
                refine ⟨4787349780661277055078353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51065064327053621920835765 4787349780661277055078353)
                ·
                  refine ⟨3590512335495957791308765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4787349780661277055078353 3590512335495957791308765)
                  ·
                    refine ⟨1346442125810984171740787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3590512335495957791308765 1346442125810984171740787)
                    ·
                      rfl

theorem cell22_3933280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2, 3].length) (baseStart_3933280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933280 prefixEnd_3933280 := by exact prefixLift 3933280
  have htrace : WordTrace (prefixWord ++ tailWord_3933280) baseStart_3933280 baseEnd_3933280 := by
    simpa [prefixWord, tailWord_3933280, baseEnd_3933280] using wordTrace_append hprefix tailTrace_3933280
  have hstable : (prefixWord ++ tailWord_3933280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933280).length < 2 ^ (prefixWord ++ tailWord_3933280).sum := by decide
  have hdescent : baseEnd_3933280 < baseStart_3933280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933301 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3933301 : Nat := 118140960795 + 3933301 * 2 ^ 59
def prefixEnd_3933301 : Nat := 4983230072969 + 3 ^ 40 * 3933301 * 2
def baseEnd_3933301 : Nat := 1346449314540147116965723

theorem tailTrace_3933301 : CollatzResearch.WordTrace tailWord_3933301 prefixEnd_3933301 1346449314540147116965723 := by
  unfold tailWord_3933301
  simp only [CollatzResearch.WordTrace]
  refine ⟨143459273123329706174815757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95639515415553137449877171 143459273123329706174815757)
  ·
    refine ⟨53797227421248639815555909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143459273123329706174815757 53797227421248639815555909)
    ·
      refine ⟨10086980141484119965416733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53797227421248639815555909 10086980141484119965416733)
      ·
        refine ⟨3782617553056544987031275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10086980141484119965416733 3782617553056544987031275)
        ·
          refine ⟨5673926329584817480546913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3782617553056544987031275 5673926329584817480546913)
          ·
            refine ⟨4255444747188613110410185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5673926329584817480546913 4255444747188613110410185)
            ·
              refine ⟨3191583560391459832807639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255444747188613110410185 3191583560391459832807639)
              ·
                refine ⟨4787375340587189749211459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191583560391459832807639 4787375340587189749211459)
                ·
                  refine ⟨7181063010880784623817189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787375340587189749211459 7181063010880784623817189)
                  ·
                    refine ⟨1346449314540147116965723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7181063010880784623817189 1346449314540147116965723)
                    ·
                      rfl

theorem cell22_3933301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3933301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933301 prefixEnd_3933301 := by exact prefixLift 3933301
  have htrace : WordTrace (prefixWord ++ tailWord_3933301) baseStart_3933301 baseEnd_3933301 := by
    simpa [prefixWord, tailWord_3933301, baseEnd_3933301] using wordTrace_append hprefix tailTrace_3933301
  have hstable : (prefixWord ++ tailWord_3933301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933301).length < 2 ^ (prefixWord ++ tailWord_3933301).sum := by decide
  have hdescent : baseEnd_3933301 < baseStart_3933301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933376 : List Nat := [2, 1, 1, 2, 6, 1, 3, 2, 1, 3]
def baseStart_3933376 : Nat := 118140960795 + 3933376 * 2 ^ 59
def prefixEnd_3933376 : Nat := 4983230072969 + 3 ^ 40 * 3933376 * 2
def baseEnd_3933376 : Nat := 1346474988572871921340493

theorem tailTrace_3933376 : CollatzResearch.WordTrace tailWord_3933376 prefixEnd_3933376 1346474988572871921340493 := by
  unfold tailWord_3933376
  simp only [CollatzResearch.WordTrace]
  refine ⟨71731004299028996991897991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95641339065371995989197321 71731004299028996991897991)
  ·
    refine ⟨107596506448543495487846987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71731004299028996991897991 107596506448543495487846987)
    ·
      refine ⟨161394759672815243231770481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107596506448543495487846987 161394759672815243231770481)
      ·
        refine ⟨121046069754611432423827861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161394759672815243231770481 121046069754611432423827861)
        ·
          refine ⟨5674034519747410894866931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121046069754611432423827861 5674034519747410894866931)
          ·
            refine ⟨8511051779621116342300397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5674034519747410894866931 8511051779621116342300397)
            ·
              refine ⟨3191644417357918628362649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8511051779621116342300397 3191644417357918628362649)
              ·
                refine ⟨2393733313018438971271987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191644417357918628362649 2393733313018438971271987)
                ·
                  refine ⟨3590599969527658456907981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393733313018438971271987 3590599969527658456907981)
                  ·
                    refine ⟨1346474988572871921340493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3590599969527658456907981 1346474988572871921340493)
                    ·
                      rfl

theorem cell22_3933376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 1, 3].length) (baseStart_3933376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933376 prefixEnd_3933376 := by exact prefixLift 3933376
  have htrace : WordTrace (prefixWord ++ tailWord_3933376) baseStart_3933376 baseEnd_3933376 := by
    simpa [prefixWord, tailWord_3933376, baseEnd_3933376] using wordTrace_append hprefix tailTrace_3933376
  have hstable : (prefixWord ++ tailWord_3933376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933376).length < 2 ^ (prefixWord ++ tailWord_3933376).sum := by decide
  have hdescent : baseEnd_3933376 < baseStart_3933376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933382 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3933382 : Nat := 118140960795 + 3933382 * 2 ^ 59
def prefixEnd_3933382 : Nat := 4983230072969 + 3 ^ 40 * 3933382 * 2
def baseEnd_3933382 : Nat := 1346477042495489905690475

theorem tailTrace_3933382 : CollatzResearch.WordTrace tailWord_3933382 prefixEnd_3933382 1346477042495489905690475 := by
  unfold tailWord_3933382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483194607376133031516075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95641484957357504672342933 4483194607376133031516075)
  ·
    refine ⟨6724791911064199547274113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4483194607376133031516075 6724791911064199547274113)
    ·
      refine ⟨5043593933298149660455585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6724791911064199547274113 5043593933298149660455585)
      ·
        refine ⟨3782695449973612245341689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5043593933298149660455585 3782695449973612245341689)
        ·
          refine ⟨2837021587480209184006267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3782695449973612245341689 2837021587480209184006267)
          ·
            refine ⟨4255532381220313776009401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837021587480209184006267 4255532381220313776009401)
            ·
              refine ⟨3191649285915235332007051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255532381220313776009401 3191649285915235332007051)
              ·
                refine ⟨4787473928872852998010577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191649285915235332007051 4787473928872852998010577)
                ·
                  refine ⟨3590605446654639748507933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4787473928872852998010577 3590605446654639748507933)
                  ·
                    refine ⟨1346477042495489905690475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3590605446654639748507933 1346477042495489905690475)
                    ·
                      rfl

theorem cell22_3933382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3933382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933382 prefixEnd_3933382 := by exact prefixLift 3933382
  have htrace : WordTrace (prefixWord ++ tailWord_3933382) baseStart_3933382 baseEnd_3933382 := by
    simpa [prefixWord, tailWord_3933382, baseEnd_3933382] using wordTrace_append hprefix tailTrace_3933382
  have hstable : (prefixWord ++ tailWord_3933382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933382).length < 2 ^ (prefixWord ++ tailWord_3933382).sum := by decide
  have hdescent : baseEnd_3933382 < baseStart_3933382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933430 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3933430 : Nat := 118140960795 + 3933430 * 2 ^ 59
def prefixEnd_3933430 : Nat := 4983230072969 + 3 ^ 40 * 3933430 * 2
def baseEnd_3933430 : Nat := 1346493473876433780490327

theorem tailTrace_3933430 : CollatzResearch.WordTrace tailWord_3933430 prefixEnd_3933430 1346493473876433780490327 := by
  unfold tailWord_3933430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8966498633741397575391359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95642652093241574137507829 8966498633741397575391359)
  ·
    refine ⟨13449747950612096363087039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8966498633741397575391359 13449747950612096363087039)
    ·
      refine ⟨20174621925918144544630559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13449747950612096363087039 20174621925918144544630559)
      ·
        refine ⟨30261932888877216816945839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20174621925918144544630559 30261932888877216816945839)
        ·
          refine ⟨45392899333315825225418759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30261932888877216816945839 45392899333315825225418759)
          ·
            refine ⟨68089348999973737838128139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45392899333315825225418759 68089348999973737838128139)
            ·
              refine ⟨102134023499960606757192209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68089348999973737838128139 102134023499960606757192209)
              ·
                refine ⟨76600517624970455067894157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102134023499960606757192209 76600517624970455067894157)
                ·
                  refine ⟨28725194109363920650460309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76600517624970455067894157 28725194109363920650460309)
                  ·
                    refine ⟨1346493473876433780490327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28725194109363920650460309 1346493473876433780490327)
                    ·
                      rfl

theorem cell22_3933430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3933430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933430 prefixEnd_3933430 := by exact prefixLift 3933430
  have htrace : WordTrace (prefixWord ++ tailWord_3933430) baseStart_3933430 baseEnd_3933430 := by
    simpa [prefixWord, tailWord_3933430, baseEnd_3933430] using wordTrace_append hprefix tailTrace_3933430
  have hstable : (prefixWord ++ tailWord_3933430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933430).length < 2 ^ (prefixWord ++ tailWord_3933430).sum := by decide
  have hdescent : baseEnd_3933430 < baseStart_3933430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933470 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3933470 : Nat := 118140960795 + 3933470 * 2 ^ 59
def prefixEnd_3933470 : Nat := 4983230072969 + 3 ^ 40 * 3933470 * 2
def baseEnd_3933470 : Nat := 1346507166693887009490205

theorem tailTrace_3933470 : CollatzResearch.WordTrace tailWord_3933470 prefixEnd_3933470 1346507166693887009490205 := by
  unfold tailWord_3933470
  simp only [CollatzResearch.WordTrace]
  refine ⟨17933179632464681004714733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95643624706478298691811909 17933179632464681004714733)
  ·
    refine ⟨6724942362174255376768025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17933179632464681004714733 6724942362174255376768025)
    ·
      refine ⟨5043706771630691532576019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6724942362174255376768025 5043706771630691532576019)
      ·
        refine ⟨7565560157446037298864029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5043706771630691532576019 7565560157446037298864029)
        ·
          refine ⟨2837085059042263987074011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7565560157446037298864029 2837085059042263987074011)
          ·
            refine ⟨4255627588563395980611017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837085059042263987074011 4255627588563395980611017)
            ·
              refine ⟨3191720691422546985458263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255627588563395980611017 3191720691422546985458263)
              ·
                refine ⟨4787581037133820478187395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191720691422546985458263 4787581037133820478187395)
                ·
                  refine ⟨7181371555700730717281093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787581037133820478187395 7181371555700730717281093)
                  ·
                    refine ⟨1346507166693887009490205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7181371555700730717281093 1346507166693887009490205)
                    ·
                      rfl

theorem cell22_3933470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3933470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933470 prefixEnd_3933470 := by exact prefixLift 3933470
  have htrace : WordTrace (prefixWord ++ tailWord_3933470) baseStart_3933470 baseEnd_3933470 := by
    simpa [prefixWord, tailWord_3933470, baseEnd_3933470] using wordTrace_append hprefix tailTrace_3933470
  have hstable : (prefixWord ++ tailWord_3933470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933470).length < 2 ^ (prefixWord ++ tailWord_3933470).sum := by decide
  have hdescent : baseEnd_3933470 < baseStart_3933470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933580 : List Nat := [2, 2, 1, 2, 1, 3, 1, 10]
def baseStart_3933580 : Nat := 118140960795 + 3933580 * 2 ^ 59
def prefixEnd_3933580 : Nat := 4983230072969 + 3 ^ 40 * 3933580 * 2
def baseEnd_3933580 : Nat := 149616091326875932137763

theorem tailTrace_3933580 : CollatzResearch.WordTrace tailWord_3933580 prefixEnd_3933580 149616091326875932137763 := by
  unfold tailWord_3933580
  simp only [CollatzResearch.WordTrace]
  refine ⟨71734724544659468412111097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95646299392879291216148129 71734724544659468412111097)
  ·
    refine ⟨53801043408494601309083323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71734724544659468412111097 53801043408494601309083323)
    ·
      refine ⟨80701565112741901963624985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53801043408494601309083323 80701565112741901963624985)
      ·
        refine ⟨60526173834556426472718739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80701565112741901963624985 60526173834556426472718739)
        ·
          refine ⟨90789260751834639709078109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60526173834556426472718739 90789260751834639709078109)
          ·
            refine ⟨34045972781937989890904291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90789260751834639709078109 34045972781937989890904291)
            ·
              refine ⟨51068959172906984836356437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34045972781937989890904291 51068959172906984836356437)
              ·
                refine ⟨149616091326875932137763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51068959172906984836356437 149616091326875932137763)
                ·
                  rfl

theorem cell22_3933580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 10].length) (baseStart_3933580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933580 prefixEnd_3933580 := by exact prefixLift 3933580
  have htrace : WordTrace (prefixWord ++ tailWord_3933580) baseStart_3933580 baseEnd_3933580 := by
    simpa [prefixWord, tailWord_3933580, baseEnd_3933580] using wordTrace_append hprefix tailTrace_3933580
  have hstable : (prefixWord ++ tailWord_3933580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933580).length < 2 ^ (prefixWord ++ tailWord_3933580).sum := by decide
  have hdescent : baseEnd_3933580 < baseStart_3933580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933629 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_3933629 : Nat := 118140960795 + 3933629 * 2 ^ 59
def prefixEnd_3933629 : Nat := 4983230072969 + 3 ^ 40 * 3933629 * 2
def baseEnd_3933629 : Nat := 1346561595643263594764717

theorem tailTrace_3933629 : CollatzResearch.WordTrace tailWord_3933629 prefixEnd_3933629 1346561595643263594764717 := by
  unfold tailWord_3933629
  simp only [CollatzResearch.WordTrace]
  refine ⟨143471236266141418192755941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95647490844094278795170627 143471236266141418192755941)
  ·
    refine ⟨26900856799901515911141739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143471236266141418192755941 26900856799901515911141739)
    ·
      refine ⟨40351285199852273866712609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26900856799901515911141739 40351285199852273866712609)
      ·
        refine ⟨30263463899889205400034457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40351285199852273866712609 30263463899889205400034457)
        ·
          refine ⟨22697597924916904050025843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30263463899889205400034457 22697597924916904050025843)
          ·
            refine ⟨34046396887375356075038765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22697597924916904050025843 34046396887375356075038765)
            ·
              refine ⟨12767398832765758528139537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34046396887375356075038765 12767398832765758528139537)
              ·
                refine ⟨9575549124574318896104653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12767398832765758528139537 9575549124574318896104653)
                ·
                  refine ⟨3590830921715369586039245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9575549124574318896104653 3590830921715369586039245)
                  ·
                    refine ⟨1346561595643263594764717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3590830921715369586039245 1346561595643263594764717)
                    ·
                      rfl

theorem cell22_3933629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_3933629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933629 prefixEnd_3933629 := by exact prefixLift 3933629
  have htrace : WordTrace (prefixWord ++ tailWord_3933629) baseStart_3933629 baseEnd_3933629 := by
    simpa [prefixWord, tailWord_3933629, baseEnd_3933629] using wordTrace_append hprefix tailTrace_3933629
  have hstable : (prefixWord ++ tailWord_3933629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933629).length < 2 ^ (prefixWord ++ tailWord_3933629).sum := by decide
  have hdescent : baseEnd_3933629 < baseStart_3933629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933646 : List Nat := [4, 1, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_3933646 : Nat := 118140960795 + 3933646 * 2 ^ 59
def prefixEnd_3933646 : Nat := 4983230072969 + 3 ^ 40 * 3933646 * 2
def baseEnd_3933646 : Nat := 1346567415090681217089665

theorem tailTrace_3933646 : CollatzResearch.WordTrace tailWord_3933646 prefixEnd_3933646 1346567415090681217089665 := by
  unfold tailWord_3933646
  simp only [CollatzResearch.WordTrace]
  refine ⟨17933982038384978762015599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95647904204719886730749861 17933982038384978762015599)
  ·
    refine ⟨26900973057577468143023399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17933982038384978762015599 26900973057577468143023399)
    ·
      refine ⟨40351459586366202214535099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26900973057577468143023399 40351459586366202214535099)
      ·
        refine ⟨60527189379549303321802649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40351459586366202214535099 60527189379549303321802649)
        ·
          refine ⟨45395392034661977491351987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60527189379549303321802649 45395392034661977491351987)
          ·
            refine ⟨68093088051992966237027981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45395392034661977491351987 68093088051992966237027981)
            ·
              refine ⟨25534908019497362338885493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68093088051992966237027981 25534908019497362338885493)
              ·
                refine ⟨2393897626827877719270515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25534908019497362338885493 2393897626827877719270515)
                ·
                  refine ⟨3590846440241816578905773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393897626827877719270515 3590846440241816578905773)
                  ·
                    refine ⟨1346567415090681217089665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3590846440241816578905773 1346567415090681217089665)
                    ·
                      rfl

theorem cell22_3933646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_3933646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933646 prefixEnd_3933646 := by exact prefixLift 3933646
  have htrace : WordTrace (prefixWord ++ tailWord_3933646) baseStart_3933646 baseEnd_3933646 := by
    simpa [prefixWord, tailWord_3933646, baseEnd_3933646] using wordTrace_append hprefix tailTrace_3933646
  have hstable : (prefixWord ++ tailWord_3933646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933646).length < 2 ^ (prefixWord ++ tailWord_3933646).sum := by decide
  have hdescent : baseEnd_3933646 < baseStart_3933646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933657 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_3933657 : Nat := 118140960795 + 3933657 * 2 ^ 59
def prefixEnd_3933657 : Nat := 4983230072969 + 3 ^ 40 * 3933657 * 2
def baseEnd_3933657 : Nat := 1346571180615480855064631

theorem tailTrace_3933657 : CollatzResearch.WordTrace tailWord_3933657 prefixEnd_3933657 1346571180615480855064631 := by
  unfold tailWord_3933657
  simp only [CollatzResearch.WordTrace]
  refine ⟨143472257510039978974775225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95648171673359985983183483 143472257510039978974775225)
  ·
    refine ⟨107604193132529984231081419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143472257510039978974775225 107604193132529984231081419)
    ·
      refine ⟨161406289698794976346622129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107604193132529984231081419 161406289698794976346622129)
      ·
        refine ⟨121054717274096232259966597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161406289698794976346622129 121054717274096232259966597)
        ·
          refine ⟨22697759488893043548743737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121054717274096232259966597 22697759488893043548743737)
          ·
            refine ⟨17023319616669782661557803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22697759488893043548743737 17023319616669782661557803)
            ·
              refine ⟨25534979425004673992336705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17023319616669782661557803 25534979425004673992336705)
              ·
                refine ⟨19151234568753505494252529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25534979425004673992336705 19151234568753505494252529)
                ·
                  refine ⟨14363425926565129120689397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19151234568753505494252529 14363425926565129120689397)
                  ·
                    refine ⟨1346571180615480855064631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14363425926565129120689397 1346571180615480855064631)
                    ·
                      rfl

theorem cell22_3933657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_3933657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933657 prefixEnd_3933657 := by exact prefixLift 3933657
  have htrace : WordTrace (prefixWord ++ tailWord_3933657) baseStart_3933657 baseEnd_3933657 := by
    simpa [prefixWord, tailWord_3933657, baseEnd_3933657] using wordTrace_append hprefix tailTrace_3933657
  have hstable : (prefixWord ++ tailWord_3933657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933657).length < 2 ^ (prefixWord ++ tailWord_3933657).sum := by decide
  have hdescent : baseEnd_3933657 < baseStart_3933657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933766 : List Nat := [6, 1, 1, 1, 3, 10]
def baseStart_3933766 : Nat := 118140960795 + 3933766 * 2 ^ 59
def prefixEnd_3933766 : Nat := 4983230072969 + 3 ^ 40 * 3933766 * 2
def baseEnd_3933766 : Nat := 16624796216580751902337

theorem tailTrace_3933766 : CollatzResearch.WordTrace tailWord_3933766 prefixEnd_3933766 16624796216580751902337 := by
  unfold tailWord_3933766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483632283332659080952911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95650822044430060393662101 4483632283332659080952911)
  ·
    refine ⟨6725448424998988621429367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4483632283332659080952911 6725448424998988621429367)
    ·
      refine ⟨10088172637498482932144051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6725448424998988621429367 10088172637498482932144051)
      ·
        refine ⟨15132258956247724398216077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10088172637498482932144051 15132258956247724398216077)
        ·
          refine ⟨5674597108592896649331029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15132258956247724398216077 5674597108592896649331029)
          ·
            refine ⟨16624796216580751902337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5674597108592896649331029 16624796216580751902337)
            ·
              rfl

theorem cell22_3933766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 10].length) (baseStart_3933766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933766 prefixEnd_3933766 := by exact prefixLift 3933766
  have htrace : WordTrace (prefixWord ++ tailWord_3933766) baseStart_3933766 baseEnd_3933766 := by
    simpa [prefixWord, tailWord_3933766, baseEnd_3933766] using wordTrace_append hprefix tailTrace_3933766
  have hstable : (prefixWord ++ tailWord_3933766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933766).length < 2 ^ (prefixWord ++ tailWord_3933766).sum := by decide
  have hdescent : baseEnd_3933766 < baseStart_3933766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933828 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 5]
def baseStart_3933828 : Nat := 118140960795 + 3933828 * 2 ^ 59
def prefixEnd_3933828 : Nat := 4983230072969 + 3 ^ 40 * 3933828 * 2
def baseEnd_3933828 : Nat := 448876572470031136346369

theorem tailTrace_3933828 : CollatzResearch.WordTrace tailWord_3933828 prefixEnd_3933828 448876572470031136346369 := by
  unfold tailWord_3933828
  simp only [CollatzResearch.WordTrace]
  refine ⟨71739247196210237589625069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95652329594946983452833425 71739247196210237589625069)
  ·
    refine ⟨26902217698578839096109401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71739247196210237589625069 26902217698578839096109401)
    ·
      refine ⟨20176663273934129322082051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26902217698578839096109401 20176663273934129322082051)
      ·
        refine ⟨30264994910901193983123077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20176663273934129322082051 30264994910901193983123077)
        ·
          refine ⟨5674686545793973871835577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30264994910901193983123077 5674686545793973871835577)
          ·
            refine ⟨4256014909345480403876683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5674686545793973871835577 4256014909345480403876683)
            ·
              refine ⟨6384022364018220605815025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256014909345480403876683 6384022364018220605815025)
              ·
                refine ⟨4788016773013665454361269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384022364018220605815025 4788016773013665454361269)
                ·
                  refine ⟨448876572470031136346369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4788016773013665454361269 448876572470031136346369)
                  ·
                    rfl

theorem cell22_3933828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_3933828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933828 prefixEnd_3933828 := by exact prefixLift 3933828
  have htrace : WordTrace (prefixWord ++ tailWord_3933828) baseStart_3933828 baseEnd_3933828 := by
    simpa [prefixWord, tailWord_3933828, baseEnd_3933828] using wordTrace_append hprefix tailTrace_3933828
  have hstable : (prefixWord ++ tailWord_3933828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933828).length < 2 ^ (prefixWord ++ tailWord_3933828).sum := by decide
  have hdescent : baseEnd_3933828 < baseStart_3933828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933884 : List Nat := [2, 2, 2, 3, 1, 2, 10]
def baseStart_3933884 : Nat := 118140960795 + 3933884 * 2 ^ 59
def prefixEnd_3933884 : Nat := 4983230072969 + 3 ^ 40 * 3933884 * 2
def baseEnd_3933884 : Nat := 49875884716834367764405

theorem tailTrace_3933884 : CollatzResearch.WordTrace tailWord_3933884 prefixEnd_3933884 49875884716834367764405 := by
  unfold tailWord_3933884
  simp only [CollatzResearch.WordTrace]
  refine ⟨71740268440108798371644353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95653691253478397828859137 71740268440108798371644353)
  ·
    refine ⟨53805201330081598778733265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71740268440108798371644353 53805201330081598778733265)
    ·
      refine ⟨40353900997561199084049949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53805201330081598778733265 40353900997561199084049949)
      ·
        refine ⟨15132712874085449656518731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40353900997561199084049949 15132712874085449656518731)
        ·
          refine ⟨22699069311128174484778097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15132712874085449656518731 22699069311128174484778097)
          ·
            refine ⟨17024301983346130863583573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22699069311128174484778097 17024301983346130863583573)
            ·
              refine ⟨49875884716834367764405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17024301983346130863583573 49875884716834367764405)
              ·
                rfl

theorem cell22_3933884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 10].length) (baseStart_3933884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933884 prefixEnd_3933884 := by exact prefixLift 3933884
  have htrace : WordTrace (prefixWord ++ tailWord_3933884) baseStart_3933884 baseEnd_3933884 := by
    simpa [prefixWord, tailWord_3933884, baseEnd_3933884] using wordTrace_append hprefix tailTrace_3933884
  have hstable : (prefixWord ++ tailWord_3933884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933884).length < 2 ^ (prefixWord ++ tailWord_3933884).sum := by decide
  have hdescent : baseEnd_3933884 < baseStart_3933884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933886 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3933886 : Nat := 118140960795 + 3933886 * 2 ^ 59
def prefixEnd_3933886 : Nat := 4983230072969 + 3 ^ 40 * 3933886 * 2
def baseEnd_3933886 : Nat := 1346649571995400591088929

theorem tailTrace_3933886 : CollatzResearch.WordTrace tailWord_3933886 prefixEnd_3933886 1346649571995400591088929 := by
  unfold tailWord_3933886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17935076228276293885607689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95653739884140234056574341 17935076228276293885607689)
  ·
    refine ⟨13451307171207220414205767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17935076228276293885607689 13451307171207220414205767)
    ·
      refine ⟨20176960756810830621308651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13451307171207220414205767 20176960756810830621308651)
      ·
        refine ⟨30265441135216245931962977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20176960756810830621308651 30265441135216245931962977)
        ·
          refine ⟨22699080851412184448972233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30265441135216245931962977 22699080851412184448972233)
          ·
            refine ⟨17024310638559138336729175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22699080851412184448972233 17024310638559138336729175)
            ·
              refine ⟨25536465957838707505093763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17024310638559138336729175 25536465957838707505093763)
              ·
                refine ⟨38304698936758061257640645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25536465957838707505093763 38304698936758061257640645)
                ·
                  refine ⟨7182131050642136485807621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38304698936758061257640645 7182131050642136485807621)
                  ·
                    refine ⟨1346649571995400591088929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7182131050642136485807621 1346649571995400591088929)
                    ·
                      rfl

theorem cell22_3933886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3933886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933886 prefixEnd_3933886 := by exact prefixLift 3933886
  have htrace : WordTrace (prefixWord ++ tailWord_3933886) baseStart_3933886 baseEnd_3933886 := by
    simpa [prefixWord, tailWord_3933886, baseEnd_3933886] using wordTrace_append hprefix tailTrace_3933886
  have hstable : (prefixWord ++ tailWord_3933886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933886).length < 2 ^ (prefixWord ++ tailWord_3933886).sum := by decide
  have hdescent : baseEnd_3933886 < baseStart_3933886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933905 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 2, 3]
def baseStart_3933905 : Nat := 118140960795 + 3933905 * 2 ^ 59
def prefixEnd_3933905 : Nat := 4983230072969 + 3 ^ 40 * 3933905 * 2
def baseEnd_3933905 : Nat := 1346656076083690874863871

theorem tailTrace_3933905 : CollatzResearch.WordTrace tailWord_3933905 prefixEnd_3933905 1346656076083690874863871 := by
  unfold tailWord_3933905
  simp only [CollatzResearch.WordTrace]
  refine ⟨143481302813141517329803169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95654201875427678219868779 143481302813141517329803169)
  ·
    refine ⟨107610977109856137997352377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143481302813141517329803169 107610977109856137997352377)
    ·
      refine ⟨80708232832392103498014283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107610977109856137997352377 80708232832392103498014283)
      ·
        refine ⟨121062349248588155247021425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80708232832392103498014283 121062349248588155247021425)
        ·
          refine ⟨90796761936441116435266069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121062349248588155247021425 90796761936441116435266069)
          ·
            refine ⟨4256098215770677332903097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90796761936441116435266069 4256098215770677332903097)
            ·
              refine ⟨3192073661828007999677323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4256098215770677332903097 3192073661828007999677323)
              ·
                refine ⟨4788110492742011999515985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192073661828007999677323 4788110492742011999515985)
                ·
                  refine ⟨3591082869556508999636989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4788110492742011999515985 3591082869556508999636989)
                  ·
                    refine ⟨1346656076083690874863871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591082869556508999636989 1346656076083690874863871)
                    ·
                      rfl

theorem cell22_3933905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_3933905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933905 prefixEnd_3933905 := by exact prefixLift 3933905
  have htrace : WordTrace (prefixWord ++ tailWord_3933905) baseStart_3933905 baseEnd_3933905 := by
    simpa [prefixWord, tailWord_3933905, baseEnd_3933905] using wordTrace_append hprefix tailTrace_3933905
  have hstable : (prefixWord ++ tailWord_3933905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933905).length < 2 ^ (prefixWord ++ tailWord_3933905).sum := by decide
  have hdescent : baseEnd_3933905 < baseStart_3933905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933976 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_3933976 : Nat := 118140960795 + 3933976 * 2 ^ 59
def prefixEnd_3933976 : Nat := 4983230072969 + 3 ^ 40 * 3933976 * 2
def baseEnd_3933976 : Nat := 1346680380834670356338653

theorem tailTrace_3933976 : CollatzResearch.WordTrace tailWord_3933976 prefixEnd_3933976 1346680380834670356338653 := by
  unfold tailWord_3933976
  simp only [CollatzResearch.WordTrace]
  refine ⟨71741946197942148227818891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95655928263922864303758521 71741946197942148227818891)
  ·
    refine ⟨107612919296913222341728337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71741946197942148227818891 107612919296913222341728337)
    ·
      refine ⟨80709689472684916756296253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107612919296913222341728337 80709689472684916756296253)
      ·
        refine ⟨30266133552256843783611095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80709689472684916756296253 30266133552256843783611095)
        ·
          refine ⟨45399200328385265675416643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30266133552256843783611095 45399200328385265675416643)
          ·
            refine ⟨68098800492577898513124965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45399200328385265675416643 68098800492577898513124965)
            ·
              refine ⟨12768525092358355971210931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68098800492577898513124965 12768525092358355971210931)
              ·
                refine ⟨19152787638537533956816397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12768525092358355971210931 19152787638537533956816397)
                ·
                  refine ⟨7182295364451575233806149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19152787638537533956816397 7182295364451575233806149)
                  ·
                    refine ⟨1346680380834670356338653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7182295364451575233806149 1346680380834670356338653)
                    ·
                      rfl

theorem cell22_3933976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_3933976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3933976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3933976 prefixEnd_3933976 := by exact prefixLift 3933976
  have htrace : WordTrace (prefixWord ++ tailWord_3933976) baseStart_3933976 baseEnd_3933976 := by
    simpa [prefixWord, tailWord_3933976, baseEnd_3933976] using wordTrace_append hprefix tailTrace_3933976
  have hstable : (prefixWord ++ tailWord_3933976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933976).length < 2 ^ (prefixWord ++ tailWord_3933976).sum := by decide
  have hdescent : baseEnd_3933976 < baseStart_3933976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934008 : List Nat := [2, 1, 2, 1, 3, 3, 2, 4, 4]
def baseStart_3934008 : Nat := 118140960795 + 3934008 * 2 ^ 59
def prefixEnd_3934008 : Nat := 4983230072969 + 3 ^ 40 * 3934008 * 2
def baseEnd_3934008 : Nat := 448897111696210979846185

theorem tailTrace_3934008 : CollatzResearch.WordTrace tailWord_3934008 prefixEnd_3934008 448897111696210979846185 := by
  unfold tailWord_3934008
  simp only [CollatzResearch.WordTrace]
  refine ⟨71742529765884182960401339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95656706354512243947201785 71742529765884182960401339)
  ·
    refine ⟨107613794648826274440602009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71742529765884182960401339 107613794648826274440602009)
    ·
      refine ⟨80710345986619705830451507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107613794648826274440602009 80710345986619705830451507)
      ·
        refine ⟨121065518979929558745677261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80710345986619705830451507 121065518979929558745677261)
        ·
          refine ⟨45399569617473584529628973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121065518979929558745677261 45399569617473584529628973)
          ·
            refine ⟨17024838606552594198610865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45399569617473584529628973 17024838606552594198610865)
            ·
              refine ⟨12768628954914445648958149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17024838606552594198610865 12768628954914445648958149)
              ·
                refine ⟨2394117929046458559179653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12768628954914445648958149 2394117929046458559179653)
                ·
                  refine ⟨448897111696210979846185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2394117929046458559179653 448897111696210979846185)
                  ·
                    rfl

theorem cell22_3934008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 4].length) (baseStart_3934008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934008 prefixEnd_3934008 := by exact prefixLift 3934008
  have htrace : WordTrace (prefixWord ++ tailWord_3934008) baseStart_3934008 baseEnd_3934008 := by
    simpa [prefixWord, tailWord_3934008, baseEnd_3934008] using wordTrace_append hprefix tailTrace_3934008
  have hstable : (prefixWord ++ tailWord_3934008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934008).length < 2 ^ (prefixWord ++ tailWord_3934008).sum := by decide
  have hdescent : baseEnd_3934008 < baseStart_3934008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934023 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 2, 3]
def baseStart_3934023 : Nat := 118140960795 + 3934023 * 2 ^ 59
def prefixEnd_3934023 : Nat := 4983230072969 + 3 ^ 40 * 3934023 * 2
def baseEnd_3934023 : Nat := 1346696469895177900413509

theorem tailTrace_3934023 : CollatzResearch.WordTrace tailWord_3934023 prefixEnd_3934023 1346696469895177900413509 := by
  unfold tailWord_3934023
  simp only [CollatzResearch.WordTrace]
  refine ⟨143485606626714023482598723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95657071084476015655065815 143485606626714023482598723)
  ·
    refine ⟨215228409940071035223898085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143485606626714023482598723 215228409940071035223898085)
    ·
      refine ⟨40355326863763319104480891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215228409940071035223898085 40355326863763319104480891)
      ·
        refine ⟨60532990295644978656721337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40355326863763319104480891 60532990295644978656721337)
        ·
          refine ⟨45399742721733733992541003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60532990295644978656721337 45399742721733733992541003)
          ·
            refine ⟨68099614082600600988811505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45399742721733733992541003 68099614082600600988811505)
            ·
              refine ⟨51074710561950450741608629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68099614082600600988811505 51074710561950450741608629)
              ·
                refine ⟨4788254115182854757025809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51074710561950450741608629 4788254115182854757025809)
                ·
                  refine ⟨3591190586387141067769357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4788254115182854757025809 3591190586387141067769357)
                  ·
                    refine ⟨1346696469895177900413509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591190586387141067769357 1346696469895177900413509)
                    ·
                      rfl

theorem cell22_3934023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_3934023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934023 prefixEnd_3934023 := by exact prefixLift 3934023
  have htrace : WordTrace (prefixWord ++ tailWord_3934023) baseStart_3934023 baseEnd_3934023 := by
    simpa [prefixWord, tailWord_3934023, baseEnd_3934023] using wordTrace_append hprefix tailTrace_3934023
  have hstable : (prefixWord ++ tailWord_3934023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934023).length < 2 ^ (prefixWord ++ tailWord_3934023).sum := by decide
  have hdescent : baseEnd_3934023 < baseStart_3934023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934066 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_3934066 : Nat := 118140960795 + 3934066 * 2 ^ 59
def prefixEnd_3934066 : Nat := 4983230072969 + 3 ^ 40 * 3934066 * 2
def baseEnd_3934066 : Nat := 1346711189673940121588377

theorem tailTrace_3934066 : CollatzResearch.WordTrace tailWord_3934066 prefixEnd_3934066 1346711189673940121588377 := by
  unfold tailWord_3934066
  simp only [CollatzResearch.WordTrace]
  refine ⟨35871793741389560456603513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95658116643705494550942701 35871793741389560456603513)
  ·
    refine ⟨26903845306042170342452635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35871793741389560456603513 26903845306042170342452635)
    ·
      refine ⟨40355767959063255513678953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26903845306042170342452635 40355767959063255513678953)
      ·
        refine ⟨30266825969297441635259215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40355767959063255513678953 30266825969297441635259215)
        ·
          refine ⟨45400238953946162452888823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30266825969297441635259215 45400238953946162452888823)
          ·
            refine ⟨68100358430919243679333235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45400238953946162452888823 68100358430919243679333235)
            ·
              refine ⟨102150537646378865518999853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68100358430919243679333235 102150537646378865518999853)
              ·
                refine ⟨38306451617392074569624945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102150537646378865518999853 38306451617392074569624945)
                ·
                  refine ⟨28729838713044055927218709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38306451617392074569624945 28729838713044055927218709)
                  ·
                    refine ⟨1346711189673940121588377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28729838713044055927218709 1346711189673940121588377)
                    ·
                      rfl

theorem cell22_3934066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_3934066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934066 prefixEnd_3934066 := by exact prefixLift 3934066
  have htrace : WordTrace (prefixWord ++ tailWord_3934066) baseStart_3934066 baseEnd_3934066 := by
    simpa [prefixWord, tailWord_3934066, baseEnd_3934066] using wordTrace_append hprefix tailTrace_3934066
  have hstable : (prefixWord ++ tailWord_3934066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934066).length < 2 ^ (prefixWord ++ tailWord_3934066).sum := by decide
  have hdescent : baseEnd_3934066 < baseStart_3934066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934070 : List Nat := [5, 1, 1, 3, 2, 1, 2, 7]
def baseStart_3934070 : Nat := 118140960795 + 3934070 * 2 ^ 59
def prefixEnd_3934070 : Nat := 4983230072969 + 3 ^ 40 * 3934070 * 2
def baseEnd_3934070 : Nat := 149634728772853938276485

theorem tailTrace_3934070 : CollatzResearch.WordTrace tailWord_3934070 prefixEnd_3934070 149634728772853938276485 := by
  unfold tailWord_3934070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8967957553596484406847479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95658213905029167006373109 8967957553596484406847479)
  ·
    refine ⟨13451936330394726610271219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8967957553596484406847479 13451936330394726610271219)
    ·
      refine ⟨20177904495592089915406829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13451936330394726610271219 20177904495592089915406829)
      ·
        refine ⟨7566714185847033718277561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20177904495592089915406829 7566714185847033718277561)
        ·
          refine ⟨5675035639385275288708171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7566714185847033718277561 5675035639385275288708171)
          ·
            refine ⟨8512553459077912933062257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675035639385275288708171 8512553459077912933062257)
            ·
              refine ⟨6384415094308434699796693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8512553459077912933062257 6384415094308434699796693)
              ·
                refine ⟨149634728772853938276485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6384415094308434699796693 149634728772853938276485)
                ·
                  rfl

theorem cell22_3934070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_3934070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934070 prefixEnd_3934070 := by exact prefixLift 3934070
  have htrace : WordTrace (prefixWord ++ tailWord_3934070) baseStart_3934070 baseEnd_3934070 := by
    simpa [prefixWord, tailWord_3934070, baseEnd_3934070] using wordTrace_append hprefix tailTrace_3934070
  have hstable : (prefixWord ++ tailWord_3934070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934070).length < 2 ^ (prefixWord ++ tailWord_3934070).sum := by decide
  have hdescent : baseEnd_3934070 < baseStart_3934070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934119 : List Nat := [1, 1, 6, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3934119 : Nat := 118140960795 + 3934119 * 2 ^ 59
def prefixEnd_3934119 : Nat := 4983230072969 + 3 ^ 40 * 3934119 * 2
def baseEnd_3934119 : Nat := 1346729332657065650013215

theorem tailTrace_3934119 : CollatzResearch.WordTrace tailWord_3934119 prefixEnd_3934119 1346729332657065650013215 := by
  unfold tailWord_3934119
  simp only [CollatzResearch.WordTrace]
  refine ⟨143489108034366231878093411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95659405356244154585395607 143489108034366231878093411)
  ·
    refine ⟨215233662051549347817140117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143489108034366231878093411 215233662051549347817140117)
    ·
      refine ⟨10089077908666375678928443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215233662051549347817140117 10089077908666375678928443)
      ·
        refine ⟨15133616862999563518392665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10089077908666375678928443 15133616862999563518392665)
        ·
          refine ⟨11350212647249672638794499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15133616862999563518392665 11350212647249672638794499)
          ·
            refine ⟨17025318970874508958191749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11350212647249672638794499 17025318970874508958191749)
            ·
              refine ⟨3192247307038970429660953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17025318970874508958191749 3192247307038970429660953)
              ·
                refine ⟨2394185480279227822245715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192247307038970429660953 2394185480279227822245715)
                ·
                  refine ⟨3591278220418841733368573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394185480279227822245715 3591278220418841733368573)
                  ·
                    refine ⟨1346729332657065650013215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591278220418841733368573 1346729332657065650013215)
                    ·
                      rfl

theorem cell22_3934119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3934119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934119 prefixEnd_3934119 := by exact prefixLift 3934119
  have htrace : WordTrace (prefixWord ++ tailWord_3934119) baseStart_3934119 baseEnd_3934119 := by
    simpa [prefixWord, tailWord_3934119, baseEnd_3934119] using wordTrace_append hprefix tailTrace_3934119
  have hstable : (prefixWord ++ tailWord_3934119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934119).length < 2 ^ (prefixWord ++ tailWord_3934119).sum := by decide
  have hdescent : baseEnd_3934119 < baseStart_3934119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934158 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_3934158 : Nat := 118140960795 + 3934158 * 2 ^ 59
def prefixEnd_3934158 : Nat := 4983230072969 + 3 ^ 40 * 3934158 * 2
def baseEnd_3934158 : Nat := 1346742683154082548288095

theorem tailTrace_3934158 : CollatzResearch.WordTrace tailWord_3934158 prefixEnd_3934158 1346742683154082548288095 := by
  unfold tailWord_3934158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17936316310153117692345391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95660353654149961025842085 17936316310153117692345391)
  ·
    refine ⟨26904474465229676538518087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17936316310153117692345391 26904474465229676538518087)
    ·
      refine ⟨40356711697844514807777131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26904474465229676538518087 40356711697844514807777131)
      ·
        refine ⟨60535067546766772211665697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40356711697844514807777131 60535067546766772211665697)
        ·
          refine ⟨45401300660075079158749273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60535067546766772211665697 45401300660075079158749273)
          ·
            refine ⟨34050975495056309369061955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45401300660075079158749273 34050975495056309369061955)
            ·
              refine ⟨51076463242584464053592933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34050975495056309369061955 51076463242584464053592933)
              ·
                refine ⟨9576836857984587010048675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51076463242584464053592933 9576836857984587010048675)
                ·
                  refine ⟨14365255286976880515073013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9576836857984587010048675 14365255286976880515073013)
                  ·
                    refine ⟨1346742683154082548288095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14365255286976880515073013 1346742683154082548288095)
                    ·
                      rfl

theorem cell22_3934158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_3934158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934158 prefixEnd_3934158 := by exact prefixLift 3934158
  have htrace : WordTrace (prefixWord ++ tailWord_3934158) baseStart_3934158 baseEnd_3934158 := by
    simpa [prefixWord, tailWord_3934158, baseEnd_3934158] using wordTrace_append hprefix tailTrace_3934158
  have hstable : (prefixWord ++ tailWord_3934158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934158).length < 2 ^ (prefixWord ++ tailWord_3934158).sum := by decide
  have hdescent : baseEnd_3934158 < baseStart_3934158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934162 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_3934162 : Nat := 118140960795 + 3934162 * 2 ^ 59
def prefixEnd_3934162 : Nat := 4983230072969 + 3 ^ 40 * 3934162 * 2
def baseEnd_3934162 : Nat := 1346744052435827871188083

theorem tailTrace_3934162 : CollatzResearch.WordTrace tailWord_3934162 prefixEnd_3934162 1346744052435827871188083 := by
  unfold tailWord_3934162
  simp only [CollatzResearch.WordTrace]
  refine ⟨35872669093302612555477185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95660450915473633481272493 35872669093302612555477185)
  ·
    refine ⟨26904501819976959416607889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35872669093302612555477185 26904501819976959416607889)
    ·
      refine ⟨20178376364982719562455917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26904501819976959416607889 20178376364982719562455917)
      ·
        refine ⟨7566891136868519835920969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20178376364982719562455917 7566891136868519835920969)
        ·
          refine ⟨5675168352651389876940727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7566891136868519835920969 5675168352651389876940727)
          ·
            refine ⟨8512752528977084815411091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675168352651389876940727 8512752528977084815411091)
            ·
              refine ⟨12769128793465627223116637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8512752528977084815411091 12769128793465627223116637)
              ·
                refine ⟨4788423297549610208668739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12769128793465627223116637 4788423297549610208668739)
                ·
                  refine ⟨7182634946324415313003109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788423297549610208668739 7182634946324415313003109)
                  ·
                    refine ⟨1346744052435827871188083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7182634946324415313003109 1346744052435827871188083)
                    ·
                      rfl

theorem cell22_3934162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_3934162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934162 prefixEnd_3934162 := by exact prefixLift 3934162
  have htrace : WordTrace (prefixWord ++ tailWord_3934162) baseStart_3934162 baseEnd_3934162 := by
    simpa [prefixWord, tailWord_3934162, baseEnd_3934162] using wordTrace_append hprefix tailTrace_3934162
  have hstable : (prefixWord ++ tailWord_3934162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934162).length < 2 ^ (prefixWord ++ tailWord_3934162).sum := by decide
  have hdescent : baseEnd_3934162 < baseStart_3934162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934175 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 4, 3]
def baseStart_3934175 : Nat := 118140960795 + 3934175 * 2 ^ 59
def prefixEnd_3934175 : Nat := 4983230072969 + 3 ^ 40 * 3934175 * 2
def baseEnd_3934175 : Nat := 1346748502601500170613043

theorem tailTrace_3934175 : CollatzResearch.WordTrace tailWord_3934175 prefixEnd_3934175 1346748502601500170613043 := by
  unfold tailWord_3934175
  simp only [CollatzResearch.WordTrace]
  refine ⟨143491150522163353442131979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95660767014775568961421319 143491150522163353442131979)
  ·
    refine ⟨215236725783245030163197969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143491150522163353442131979 215236725783245030163197969)
    ·
      refine ⟨161427544337433772622398477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215236725783245030163197969 161427544337433772622398477)
      ·
        refine ⟨60535329126537664733399429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161427544337433772622398477 60535329126537664733399429)
        ·
          refine ⟨11350374211225812137512393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60535329126537664733399429 11350374211225812137512393)
          ·
            refine ⟨8512780658419359103134295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11350374211225812137512393 8512780658419359103134295)
            ·
              refine ⟨12769170987629038654701443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8512780658419359103134295 12769170987629038654701443)
              ·
                refine ⟨19153756481443557982052165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12769170987629038654701443 19153756481443557982052165)
                ·
                  refine ⟨3591329340270667121634781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19153756481443557982052165 3591329340270667121634781)
                  ·
                    refine ⟨1346748502601500170613043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591329340270667121634781 1346748502601500170613043)
                    ·
                      rfl

theorem cell22_3934175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 3].length) (baseStart_3934175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934175 prefixEnd_3934175 := by exact prefixLift 3934175
  have htrace : WordTrace (prefixWord ++ tailWord_3934175) baseStart_3934175 baseEnd_3934175 := by
    simpa [prefixWord, tailWord_3934175, baseEnd_3934175] using wordTrace_append hprefix tailTrace_3934175
  have hstable : (prefixWord ++ tailWord_3934175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934175).length < 2 ^ (prefixWord ++ tailWord_3934175).sum := by decide
  have hdescent : baseEnd_3934175 < baseStart_3934175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934233 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 5]
def baseStart_3934233 : Nat := 118140960795 + 3934233 * 2 ^ 59
def prefixEnd_3934233 : Nat := 4983230072969 + 3 ^ 40 * 3934233 * 2
def baseEnd_3934233 : Nat := 448922785728935784220955

theorem tailTrace_3934233 : CollatzResearch.WordTrace tailWord_3934233 prefixEnd_3934233 448922785728935784220955 := by
  unfold tailWord_3934233
  simp only [CollatzResearch.WordTrace]
  refine ⟨143493265955953229347743353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95662177303968819565162235 143493265955953229347743353)
  ·
    refine ⟨107619949466964922010807515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143493265955953229347743353 107619949466964922010807515)
    ·
      refine ⟨161429924200447383016211273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107619949466964922010807515 161429924200447383016211273)
      ·
        refine ⟨121072443150335537262158455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161429924200447383016211273 121072443150335537262158455)
        ·
          refine ⟨181608664725503305893237683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121072443150335537262158455 181608664725503305893237683)
          ·
            refine ⟨272412997088254958839856525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181608664725503305893237683 272412997088254958839856525)
            ·
              refine ⟨102154873908095609564946197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272412997088254958839856525 102154873908095609564946197)
              ·
                refine ⟨4788509714441981698356853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102154873908095609564946197 4788509714441981698356853)
                ·
                  refine ⟨448922785728935784220955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4788509714441981698356853 448922785728935784220955)
                  ·
                    rfl

theorem cell22_3934233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_3934233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934233 prefixEnd_3934233 := by exact prefixLift 3934233
  have htrace : WordTrace (prefixWord ++ tailWord_3934233) baseStart_3934233 baseEnd_3934233 := by
    simpa [prefixWord, tailWord_3934233, baseEnd_3934233] using wordTrace_append hprefix tailTrace_3934233
  have hstable : (prefixWord ++ tailWord_3934233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934233).length < 2 ^ (prefixWord ++ tailWord_3934233).sum := by decide
  have hdescent : baseEnd_3934233 < baseStart_3934233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934237 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_3934237 : Nat := 118140960795 + 3934237 * 2 ^ 59
def prefixEnd_3934237 : Nat := 4983230072969 + 3 ^ 40 * 3934237 * 2
def baseEnd_3934237 : Nat := 1346769726468552675562853

theorem tailTrace_3934237 : CollatzResearch.WordTrace tailWord_3934237 prefixEnd_3934237 1346769726468552675562853 := by
  unfold tailWord_3934237
  simp only [CollatzResearch.WordTrace]
  refine ⟨143493411847938738030888965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95662274565292492020592643 143493411847938738030888965)
  ·
    refine ⟨26905014721488513380791681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143493411847938738030888965 26905014721488513380791681)
    ·
      refine ⟨20178761041116385035593761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26905014721488513380791681 20178761041116385035593761)
      ·
        refine ⟨15134070780837288776695321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20178761041116385035593761 15134070780837288776695321)
        ·
          refine ⟨11350553085627966582521491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15134070780837288776695321 11350553085627966582521491)
          ·
            refine ⟨17025829628441949873782237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11350553085627966582521491 17025829628441949873782237)
            ·
              refine ⟨6384686110665731202668339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17025829628441949873782237 6384686110665731202668339)
              ·
                refine ⟨9577029165998596804002509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384686110665731202668339 9577029165998596804002509)
                ·
                  refine ⟨3591385937249473801500941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9577029165998596804002509 3591385937249473801500941)
                  ·
                    refine ⟨1346769726468552675562853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591385937249473801500941 1346769726468552675562853)
                    ·
                      rfl

theorem cell22_3934237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_3934237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934237 prefixEnd_3934237 := by exact prefixLift 3934237
  have htrace : WordTrace (prefixWord ++ tailWord_3934237) baseStart_3934237 baseEnd_3934237 := by
    simpa [prefixWord, tailWord_3934237, baseEnd_3934237] using wordTrace_append hprefix tailTrace_3934237
  have hstable : (prefixWord ++ tailWord_3934237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934237).length < 2 ^ (prefixWord ++ tailWord_3934237).sum := by decide
  have hdescent : baseEnd_3934237 < baseStart_3934237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934344 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 2, 3]
def baseStart_3934344 : Nat := 118140960795 + 3934344 * 2 ^ 59
def prefixEnd_3934344 : Nat := 4983230072969 + 3 ^ 40 * 3934344 * 2
def baseEnd_3934344 : Nat := 1346806354755240063137525

theorem tailTrace_3934344 : CollatzResearch.WordTrace tailWord_3934344 prefixEnd_3934344 1346806354755240063137525 := by
  unfold tailWord_3934344
  simp only [CollatzResearch.WordTrace]
  refine ⟨71748657229275547652517043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95664876305700730203356057 71748657229275547652517043)
  ·
    refine ⟨107622985843913321478775565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71748657229275547652517043 107622985843913321478775565)
    ·
      refine ⟨40358619691467495554540837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107622985843913321478775565 40358619691467495554540837)
      ·
        refine ⟨7567241192150155416476407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40358619691467495554540837 7567241192150155416476407)
        ·
          refine ⟨11350861788225233124714611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7567241192150155416476407 11350861788225233124714611)
          ·
            refine ⟨17026292682337849687071917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11350861788225233124714611 17026292682337849687071917)
            ·
              refine ⟨6384859755876693632651969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17026292682337849687071917 6384859755876693632651969)
              ·
                refine ⟨4788644816907520224488977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384859755876693632651969 4788644816907520224488977)
                ·
                  refine ⟨3591483612680640168366733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4788644816907520224488977 3591483612680640168366733)
                  ·
                    refine ⟨1346806354755240063137525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591483612680640168366733 1346806354755240063137525)
                    ·
                      rfl

theorem cell22_3934344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_3934344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934344 prefixEnd_3934344 := by exact prefixLift 3934344
  have htrace : WordTrace (prefixWord ++ tailWord_3934344) baseStart_3934344 baseEnd_3934344 := by
    simpa [prefixWord, tailWord_3934344, baseEnd_3934344] using wordTrace_append hprefix tailTrace_3934344
  have hstable : (prefixWord ++ tailWord_3934344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934344).length < 2 ^ (prefixWord ++ tailWord_3934344).sum := by decide
  have hdescent : baseEnd_3934344 < baseStart_3934344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934415 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 3, 4]
def baseStart_3934415 : Nat := 118140960795 + 3934415 * 2 ^ 59
def prefixEnd_3934415 : Nat := 4983230072969 + 3 ^ 40 * 3934415 * 2
def baseEnd_3934415 : Nat := 1346830659506219544612307

theorem tailTrace_3934415 : CollatzResearch.WordTrace tailWord_3934415 prefixEnd_3934415 1346830659506219544612307 := by
  unfold tailWord_3934415
  simp only [CollatzResearch.WordTrace]
  refine ⟨143499904041293874430868699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95666602694195916287245799 143499904041293874430868699)
  ·
    refine ⟨215249856061940811646303049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143499904041293874430868699 215249856061940811646303049)
    ·
      refine ⟨161437392046455608734727287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215249856061940811646303049 161437392046455608734727287)
      ·
        refine ⟨242156088069683413102090931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161437392046455608734727287 242156088069683413102090931)
        ·
          refine ⟨363234132104525119653136397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242156088069683413102090931 363234132104525119653136397)
          ·
            refine ⟨136212799539196919869926149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363234132104525119653136397 136212799539196919869926149)
            ·
              refine ⟨25539899913599422475611153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136212799539196919869926149 25539899913599422475611153)
              ·
                refine ⟨19154924935199566856708365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25539899913599422475611153 19154924935199566856708365)
                ·
                  refine ⟨7183096850699837571265637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19154924935199566856708365 7183096850699837571265637)
                  ·
                    refine ⟨1346830659506219544612307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7183096850699837571265637 1346830659506219544612307)
                    ·
                      rfl

theorem cell22_3934415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_3934415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934415 prefixEnd_3934415 := by exact prefixLift 3934415
  have htrace : WordTrace (prefixWord ++ tailWord_3934415) baseStart_3934415 baseEnd_3934415 := by
    simpa [prefixWord, tailWord_3934415, baseEnd_3934415] using wordTrace_append hprefix tailTrace_3934415
  have hstable : (prefixWord ++ tailWord_3934415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934415).length < 2 ^ (prefixWord ++ tailWord_3934415).sum := by decide
  have hdescent : baseEnd_3934415 < baseStart_3934415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934462 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3934462 : Nat := 118140960795 + 3934462 * 2 ^ 59
def prefixEnd_3934462 : Nat := 4983230072969 + 3 ^ 40 * 3934462 * 2
def baseEnd_3934462 : Nat := 1346846748566727088687163

theorem tailTrace_3934462 : CollatzResearch.WordTrace tailWord_3934462 prefixEnd_3934462 1346846748566727088687163 := by
  unfold tailWord_3934462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17937702284015450182228705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95667745514749067638553093 17937702284015450182228705)
  ·
    refine ⟨13453276713011587636671529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17937702284015450182228705 13453276713011587636671529)
    ·
      refine ⟨10089957534758690727503647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13453276713011587636671529 10089957534758690727503647)
      ·
        refine ⟨15134936302138036091255471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10089957534758690727503647 15134936302138036091255471)
        ·
          refine ⟨22702404453207054136883207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15134936302138036091255471 22702404453207054136883207)
          ·
            refine ⟨34053606679810581205324811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22702404453207054136883207 34053606679810581205324811)
            ·
              refine ⟨51080410019715871807987217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34053606679810581205324811 51080410019715871807987217)
              ·
                refine ⟨38310307514786903855990413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51080410019715871807987217 38310307514786903855990413)
                ·
                  refine ⟨14366365318045088945996405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38310307514786903855990413 14366365318045088945996405)
                  ·
                    refine ⟨1346846748566727088687163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14366365318045088945996405 1346846748566727088687163)
                    ·
                      rfl

theorem cell22_3934462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3934462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934462 prefixEnd_3934462 := by exact prefixLift 3934462
  have htrace : WordTrace (prefixWord ++ tailWord_3934462) baseStart_3934462 baseEnd_3934462 := by
    simpa [prefixWord, tailWord_3934462, baseEnd_3934462] using wordTrace_append hprefix tailTrace_3934462
  have hstable : (prefixWord ++ tailWord_3934462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934462).length < 2 ^ (prefixWord ++ tailWord_3934462).sum := by decide
  have hdescent : baseEnd_3934462 < baseStart_3934462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934464 : List Nat := [2, 1, 1, 2, 1, 1, 8, 2, 4]
def baseStart_3934464 : Nat := 118140960795 + 3934464 * 2 ^ 59
def prefixEnd_3934464 : Nat := 4983230072969 + 3 ^ 40 * 3934464 * 2
def baseEnd_3934464 : Nat := 448949144402533250045719

theorem tailTrace_3934464 : CollatzResearch.WordTrace tailWord_3934464 prefixEnd_3934464 448949144402533250045719 := by
  unfold tailWord_3934464
  simp only [CollatzResearch.WordTrace]
  refine ⟨71750845609058177899701223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95667794145410903866268297 71750845609058177899701223)
  ·
    refine ⟨107626268413587266849551835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71750845609058177899701223 107626268413587266849551835)
    ·
      refine ⟨161439402620380900274327753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107626268413587266849551835 161439402620380900274327753)
      ·
        refine ⟨121079551965285675205745815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161439402620380900274327753 121079551965285675205745815)
        ·
          refine ⟨181619327947928512808618723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121079551965285675205745815 181619327947928512808618723)
          ·
            refine ⟨272428991921892769212928085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181619327947928512808618723 272428991921892769212928085)
            ·
              refine ⟨3192527249084680889214001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 272428991921892769212928085 3192527249084680889214001)
              ·
                refine ⟨2394395436813510666910501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192527249084680889214001 2394395436813510666910501)
                ·
                  refine ⟨448949144402533250045719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2394395436813510666910501 448949144402533250045719)
                  ·
                    rfl

theorem cell22_3934464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 4].length) (baseStart_3934464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934464 prefixEnd_3934464 := by exact prefixLift 3934464
  have htrace : WordTrace (prefixWord ++ tailWord_3934464) baseStart_3934464 baseEnd_3934464 := by
    simpa [prefixWord, tailWord_3934464, baseEnd_3934464] using wordTrace_append hprefix tailTrace_3934464
  have hstable : (prefixWord ++ tailWord_3934464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934464).length < 2 ^ (prefixWord ++ tailWord_3934464).sum := by decide
  have hdescent : baseEnd_3934464 < baseStart_3934464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934509 : List Nat := [1, 5, 3, 1, 2, 1, 9]
def baseStart_3934509 : Nat := 118140960795 + 3934509 * 2 ^ 59
def prefixEnd_3934509 : Nat := 4983230072969 + 3 ^ 40 * 3934509 * 2
def baseEnd_3934509 : Nat := 49883808801008690102297

theorem tailTrace_3934509 : CollatzResearch.WordTrace tailWord_3934509 prefixEnd_3934509 49883808801008690102297 := by
  unfold tailWord_3934509
  simp only [CollatzResearch.WordTrace]
  refine ⟨143503332502953328484790581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95668888335302218989860387 143503332502953328484790581)
  ·
    refine ⟨13453437422151874545449117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143503332502953328484790581 13453437422151874545449117)
    ·
      refine ⟨5045039033306952954543419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13453437422151874545449117 5045039033306952954543419)
      ·
        refine ⟨7567558549960429431815129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5045039033306952954543419 7567558549960429431815129)
        ·
          refine ⟨5675668912470322073861347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7567558549960429431815129 5675668912470322073861347)
          ·
            refine ⟨8513503368705483110792021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675668912470322073861347 8513503368705483110792021)
            ·
              refine ⟨49883808801008690102297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8513503368705483110792021 49883808801008690102297)
              ·
                rfl

theorem cell22_3934509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 9].length) (baseStart_3934509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934509 prefixEnd_3934509 := by exact prefixLift 3934509
  have htrace : WordTrace (prefixWord ++ tailWord_3934509) baseStart_3934509 baseEnd_3934509 := by
    simpa [prefixWord, tailWord_3934509, baseEnd_3934509] using wordTrace_append hprefix tailTrace_3934509
  have hstable : (prefixWord ++ tailWord_3934509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934509).length < 2 ^ (prefixWord ++ tailWord_3934509).sum := by decide
  have hdescent : baseEnd_3934509 < baseStart_3934509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934513 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 2, 3]
def baseStart_3934513 : Nat := 118140960795 + 3934513 * 2 ^ 59
def prefixEnd_3934513 : Nat := 4983230072969 + 3 ^ 40 * 3934513 * 2
def baseEnd_3934513 : Nat := 1346864206908979955662007

theorem tailTrace_3934513 : CollatzResearch.WordTrace tailWord_3934513 prefixEnd_3934513 1346864206908979955662007 := by
  unfold tailWord_3934513
  simp only [CollatzResearch.WordTrace]
  refine ⟨143503478394938837167936193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95668985596625891445290795 143503478394938837167936193)
  ·
    refine ⟨107627608796204127875952145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143503478394938837167936193 107627608796204127875952145)
    ·
      refine ⟨80720706597153095906964109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107627608796204127875952145 80720706597153095906964109)
      ·
        refine ⟨30270264973932410965111541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80720706597153095906964109 30270264973932410965111541)
        ·
          refine ⟨2837837341306163527979207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30270264973932410965111541 2837837341306163527979207)
          ·
            refine ⟨4256756011959245291968811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837837341306163527979207 4256756011959245291968811)
            ·
              refine ⟨6385134017938867937953217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256756011959245291968811 6385134017938867937953217)
              ·
                refine ⟨4788850513454150953464913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6385134017938867937953217 4788850513454150953464913)
                ·
                  refine ⟨3591637885090613215098685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4788850513454150953464913 3591637885090613215098685)
                  ·
                    refine ⟨1346864206908979955662007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591637885090613215098685 1346864206908979955662007)
                    ·
                      rfl

theorem cell22_3934513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_3934513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934513 prefixEnd_3934513 := by exact prefixLift 3934513
  have htrace : WordTrace (prefixWord ++ tailWord_3934513) baseStart_3934513 baseEnd_3934513 := by
    simpa [prefixWord, tailWord_3934513, baseEnd_3934513] using wordTrace_append hprefix tailTrace_3934513
  have hstable : (prefixWord ++ tailWord_3934513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934513).length < 2 ^ (prefixWord ++ tailWord_3934513).sum := by decide
  have hdescent : baseEnd_3934513 < baseStart_3934513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934524 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 3, 3]
def baseStart_3934524 : Nat := 118140960795 + 3934524 * 2 ^ 59
def prefixEnd_3934524 : Nat := 4983230072969 + 3 ^ 40 * 3934524 * 2
def baseEnd_3934524 : Nat := 1346867972433779593636973

theorem tailTrace_3934524 : CollatzResearch.WordTrace tailWord_3934524 prefixEnd_3934524 1346867972433779593636973 := by
  unfold tailWord_3934524
  simp only [CollatzResearch.WordTrace]
  refine ⟨71751939798949493023293313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95669253065265990697724417 71751939798949493023293313)
  ·
    refine ⟨53813954849212119767469985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71751939798949493023293313 53813954849212119767469985)
    ·
      refine ⟨40360466136909089825602489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53813954849212119767469985 40360466136909089825602489)
      ·
        refine ⟨30270349602681817369201867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40360466136909089825602489 30270349602681817369201867)
        ·
          refine ⟨45405524404022726053802801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30270349602681817369201867 45405524404022726053802801)
          ·
            refine ⟨34054143303017044540352101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45405524404022726053802801 34054143303017044540352101)
            ·
              refine ⟨6385151869315695851316019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34054143303017044540352101 6385151869315695851316019)
              ·
                refine ⟨9577727803973543776974029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6385151869315695851316019 9577727803973543776974029)
                ·
                  refine ⟨3591647926490078916365261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9577727803973543776974029 3591647926490078916365261)
                  ·
                    refine ⟨1346867972433779593636973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591647926490078916365261 1346867972433779593636973)
                    ·
                      rfl

theorem cell22_3934524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_3934524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934524 prefixEnd_3934524 := by exact prefixLift 3934524
  have htrace : WordTrace (prefixWord ++ tailWord_3934524) baseStart_3934524 baseEnd_3934524 := by
    simpa [prefixWord, tailWord_3934524, baseEnd_3934524] using wordTrace_append hprefix tailTrace_3934524
  have hstable : (prefixWord ++ tailWord_3934524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934524).length < 2 ^ (prefixWord ++ tailWord_3934524).sum := by decide
  have hdescent : baseEnd_3934524 < baseStart_3934524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934597 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_3934597 : Nat := 118140960795 + 3934597 * 2 ^ 59
def prefixEnd_3934597 : Nat := 4983230072969 + 3 ^ 40 * 3934597 * 2
def baseEnd_3934597 : Nat := 1346892961825631736561749

theorem tailTrace_3934597 : CollatzResearch.WordTrace tailWord_3934597 prefixEnd_3934597 1346892961825631736561749 := by
  unfold tailWord_3934597
  simp only [CollatzResearch.WordTrace]
  refine ⟨143506542126634519513994045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95671028084423013009329363 143506542126634519513994045)
  ·
    refine ⟨53814953297487944817747767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143506542126634519513994045 53814953297487944817747767)
    ·
      refine ⟨80722429946231917226621651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53814953297487944817747767 80722429946231917226621651)
      ·
        refine ⟨121083644919347875839932477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80722429946231917226621651 121083644919347875839932477)
        ·
          refine ⟨45406366844755453439974679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121083644919347875839932477 45406366844755453439974679)
          ·
            refine ⟨68109550267133180159962019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45406366844755453439974679 68109550267133180159962019)
            ·
              refine ⟨102164325400699770239943029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68109550267133180159962019 102164325400699770239943029)
              ·
                refine ⟨9577905506315603459994659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102164325400699770239943029 9577905506315603459994659)
                ·
                  refine ⟨14366858259473405189991989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9577905506315603459994659 14366858259473405189991989)
                  ·
                    refine ⟨1346892961825631736561749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14366858259473405189991989 1346892961825631736561749)
                    ·
                      rfl

theorem cell22_3934597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_3934597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934597 prefixEnd_3934597 := by exact prefixLift 3934597
  have htrace : WordTrace (prefixWord ++ tailWord_3934597) baseStart_3934597 baseEnd_3934597 := by
    simpa [prefixWord, tailWord_3934597, baseEnd_3934597] using wordTrace_append hprefix tailTrace_3934597
  have hstable : (prefixWord ++ tailWord_3934597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934597).length < 2 ^ (prefixWord ++ tailWord_3934597).sum := by decide
  have hdescent : baseEnd_3934597 < baseStart_3934597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934601 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 1, 4]
def baseStart_3934601 : Nat := 118140960795 + 3934601 * 2 ^ 59
def prefixEnd_3934601 : Nat := 4983230072969 + 3 ^ 40 * 3934601 * 2
def baseEnd_3934601 : Nat := 1346894331107377059461737

theorem tailTrace_3934601 : CollatzResearch.WordTrace tailWord_3934601 prefixEnd_3934601 1346894331107377059461737 := by
  unfold tailWord_3934601
  simp only [CollatzResearch.WordTrace]
  refine ⟨143506688018620028197139657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95671125345746685464759771 143506688018620028197139657)
  ·
    refine ⟨107630016013965021147854743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143506688018620028197139657 107630016013965021147854743)
    ·
      refine ⟨161445024020947531721782115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107630016013965021147854743 161445024020947531721782115)
      ·
        refine ⟨242167536031421297582673173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161445024020947531721782115 242167536031421297582673173)
        ·
          refine ⟨11351603251472873324187805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 242167536031421297582673173 11351603251472873324187805)
          ·
            refine ⟨4256851219302327496570427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11351603251472873324187805 4256851219302327496570427)
            ·
              refine ⟨6385276828953491244855641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256851219302327496570427 6385276828953491244855641)
              ·
                refine ⟨4788957621715118433641731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6385276828953491244855641 4788957621715118433641731)
                ·
                  refine ⟨7183436432572677650462597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788957621715118433641731 7183436432572677650462597)
                  ·
                    refine ⟨1346894331107377059461737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7183436432572677650462597 1346894331107377059461737)
                    ·
                      rfl

theorem cell22_3934601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 4].length) (baseStart_3934601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934601 prefixEnd_3934601 := by exact prefixLift 3934601
  have htrace : WordTrace (prefixWord ++ tailWord_3934601) baseStart_3934601 baseEnd_3934601 := by
    simpa [prefixWord, tailWord_3934601, baseEnd_3934601] using wordTrace_append hprefix tailTrace_3934601
  have hstable : (prefixWord ++ tailWord_3934601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934601).length < 2 ^ (prefixWord ++ tailWord_3934601).sum := by decide
  have hdescent : baseEnd_3934601 < baseStart_3934601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934631 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3934631 : Nat := 118140960795 + 3934631 * 2 ^ 59
def prefixEnd_3934631 : Nat := 4983230072969 + 3 ^ 40 * 3934631 * 2
def baseEnd_3934631 : Nat := 1346904600720466981211645

theorem tailTrace_3934631 : CollatzResearch.WordTrace tailWord_3934631 prefixEnd_3934631 1346904600720466981211645 := by
  unfold tailWord_3934631
  simp only [CollatzResearch.WordTrace]
  refine ⟨143507782208511343320731747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95671854805674228880487831 143507782208511343320731747)
  ·
    refine ⟨215261673312767014981097621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143507782208511343320731747 215261673312767014981097621)
    ·
      refine ⟨10090390936535953827238951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215261673312767014981097621 10090390936535953827238951)
      ·
        refine ⟨15135586404803930740858427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10090390936535953827238951 15135586404803930740858427)
        ·
          refine ⟨22703379607205896111287641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15135586404803930740858427 22703379607205896111287641)
          ·
            refine ⟨17027534705404422083465731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22703379607205896111287641 17027534705404422083465731)
            ·
              refine ⟨25541302058106633125198597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17027534705404422083465731 25541302058106633125198597)
              ·
                refine ⟨4788994135894993710974737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25541302058106633125198597 4788994135894993710974737)
                ·
                  refine ⟨3591745601921245283231053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4788994135894993710974737 3591745601921245283231053)
                  ·
                    refine ⟨1346904600720466981211645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591745601921245283231053 1346904600720466981211645)
                    ·
                      rfl

theorem cell22_3934631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3934631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934631 prefixEnd_3934631 := by exact prefixLift 3934631
  have htrace : WordTrace (prefixWord ++ tailWord_3934631) baseStart_3934631 baseEnd_3934631 := by
    simpa [prefixWord, tailWord_3934631, baseEnd_3934631] using wordTrace_append hprefix tailTrace_3934631
  have hstable : (prefixWord ++ tailWord_3934631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934631).length < 2 ^ (prefixWord ++ tailWord_3934631).sum := by decide
  have hdescent : baseEnd_3934631 < baseStart_3934631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934693 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 3, 3]
def baseStart_3934693 : Nat := 118140960795 + 3934693 * 2 ^ 59
def prefixEnd_3934693 : Nat := 4983230072969 + 3 ^ 40 * 3934693 * 2
def baseEnd_3934693 : Nat := 1346925824587519486161455

theorem tailTrace_3934693 : CollatzResearch.WordTrace tailWord_3934693 prefixEnd_3934693 1346925824587519486161455 := by
  unfold tailWord_3934693
  simp only [CollatzResearch.WordTrace]
  refine ⟨143510043534286727909488733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95673362356191151939659155 143510043534286727909488733)
  ·
    refine ⟨53816266325357522966058275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143510043534286727909488733 53816266325357522966058275)
    ·
      refine ⟨80724399488036284449087413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53816266325357522966058275 80724399488036284449087413)
      ·
        refine ⟨7567912452003401667101945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80724399488036284449087413 7567912452003401667101945)
        ·
          refine ⟨5675934339002551250326459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7567912452003401667101945 5675934339002551250326459)
          ·
            refine ⟨8513901508503826875489689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675934339002551250326459 8513901508503826875489689)
            ·
              refine ⟨6385426131377870156617267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8513901508503826875489689 6385426131377870156617267)
              ·
                refine ⟨9578139197066805234925901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6385426131377870156617267 9578139197066805234925901)
                ·
                  refine ⟨3591802198900051963097213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9578139197066805234925901 3591802198900051963097213)
                  ·
                    refine ⟨1346925824587519486161455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591802198900051963097213 1346925824587519486161455)
                    ·
                      rfl

theorem cell22_3934693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_3934693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934693 prefixEnd_3934693 := by exact prefixLift 3934693
  have htrace : WordTrace (prefixWord ++ tailWord_3934693) baseStart_3934693 baseEnd_3934693 := by
    simpa [prefixWord, tailWord_3934693, baseEnd_3934693] using wordTrace_append hprefix tailTrace_3934693
  have hstable : (prefixWord ++ tailWord_3934693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934693).length < 2 ^ (prefixWord ++ tailWord_3934693).sum := by decide
  have hdescent : baseEnd_3934693 < baseStart_3934693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934727 : List Nat := [1, 1, 4, 3, 4, 1, 1, 3, 1, 3]
def baseStart_3934727 : Nat := 118140960795 + 3934727 * 2 ^ 59
def prefixEnd_3934727 : Nat := 4983230072969 + 3 ^ 40 * 3934727 * 2
def baseEnd_3934727 : Nat := 1346937463482354730811351

theorem tailTrace_3934727 : CollatzResearch.WordTrace tailWord_3934727 prefixEnd_3934727 1346937463482354730811351 := by
  unfold tailWord_3934727
  simp only [CollatzResearch.WordTrace]
  refine ⟨143511283616163551716226435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95674189077442367810817623 143511283616163551716226435)
  ·
    refine ⟨215266925424245327574339653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143511283616163551716226435 215266925424245327574339653)
    ·
      refine ⟨40362548517045998920188685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215266925424245327574339653 40362548517045998920188685)
      ·
        refine ⟨15135955693892249595070757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40362548517045998920188685 15135955693892249595070757)
        ·
          refine ⟨2837991692604796799075767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15135955693892249595070757 2837991692604796799075767)
          ·
            refine ⟨4256987538907195198613651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837991692604796799075767 4256987538907195198613651)
            ·
              refine ⟨6385481308360792797920477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256987538907195198613651 6385481308360792797920477)
              ·
                refine ⟨2394555490635297299220179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6385481308360792797920477 2394555490635297299220179)
                ·
                  refine ⟨3591833235952945948830269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394555490635297299220179 3591833235952945948830269)
                  ·
                    refine ⟨1346937463482354730811351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591833235952945948830269 1346937463482354730811351)
                    ·
                      rfl

theorem cell22_3934727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_3934727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934727 prefixEnd_3934727 := by exact prefixLift 3934727
  have htrace : WordTrace (prefixWord ++ tailWord_3934727) baseStart_3934727 baseEnd_3934727 := by
    simpa [prefixWord, tailWord_3934727, baseEnd_3934727] using wordTrace_append hprefix tailTrace_3934727
  have hstable : (prefixWord ++ tailWord_3934727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934727).length < 2 ^ (prefixWord ++ tailWord_3934727).sum := by decide
  have hdescent : baseEnd_3934727 < baseStart_3934727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934747 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 2, 10]
def baseStart_3934747 : Nat := 118140960795 + 3934747 * 2 ^ 59
def prefixEnd_3934747 : Nat := 4983230072969 + 3 ^ 40 * 3934747 * 2
def baseEnd_3934747 : Nat := 1346944309891081345311289

theorem tailTrace_3934747 : CollatzResearch.WordTrace tailWord_3934747 prefixEnd_3934747 1346944309891081345311289 := by
  unfold tailWord_3934747
  simp only [CollatzResearch.WordTrace]
  refine ⟨143512013076091095131954495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95674675384060730087969663 143512013076091095131954495)
  ·
    refine ⟨215268019614136642697931743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143512013076091095131954495 215268019614136642697931743)
    ·
      refine ⟨322902029421204964046897615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215268019614136642697931743 322902029421204964046897615)
      ·
        refine ⟨484353044131807446070346423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322902029421204964046897615 484353044131807446070346423)
        ·
          refine ⟨726529566197711169105519635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484353044131807446070346423 726529566197711169105519635)
          ·
            refine ⟨1089794349296566753658279453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726529566197711169105519635 1089794349296566753658279453)
            ·
              refine ⟨408672880986212532621854795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1089794349296566753658279453 408672880986212532621854795)
              ·
                refine ⟨613009321479318798932782193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408672880986212532621854795 613009321479318798932782193)
                ·
                  refine ⟨459756991109489099199586645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613009321479318798932782193 459756991109489099199586645)
                  ·
                    refine ⟨1346944309891081345311289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 459756991109489099199586645 1346944309891081345311289)
                    ·
                      rfl

theorem cell22_3934747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_3934747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934747 prefixEnd_3934747 := by exact prefixLift 3934747
  have htrace : WordTrace (prefixWord ++ tailWord_3934747) baseStart_3934747 baseEnd_3934747 := by
    simpa [prefixWord, tailWord_3934747, baseEnd_3934747] using wordTrace_append hprefix tailTrace_3934747
  have hstable : (prefixWord ++ tailWord_3934747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934747).length < 2 ^ (prefixWord ++ tailWord_3934747).sum := by decide
  have hdescent : baseEnd_3934747 < baseStart_3934747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934781 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_3934781 : Nat := 118140960795 + 3934781 * 2 ^ 59
def prefixEnd_3934781 : Nat := 4983230072969 + 3 ^ 40 * 3934781 * 2
def baseEnd_3934781 : Nat := 1346955948785916589961185

theorem tailTrace_3934781 : CollatzResearch.WordTrace tailWord_3934781 prefixEnd_3934781 1346955948785916589961185 := by
  unfold tailWord_3934781
  simp only [CollatzResearch.WordTrace]
  refine ⟨143513253157967918938692197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95675502105311945959128131 143513253157967918938692197)
  ·
    refine ⟨26908734967118984801004787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143513253157967918938692197 26908734967118984801004787)
    ·
      refine ⟨40363102450678477201507181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26908734967118984801004787 40363102450678477201507181)
      ·
        refine ⟨15136163419004428950565193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40363102450678477201507181 15136163419004428950565193)
        ·
          refine ⟨11352122564253321712923895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15136163419004428950565193 11352122564253321712923895)
          ·
            refine ⟨17028183846379982569385843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11352122564253321712923895 17028183846379982569385843)
            ·
              refine ⟨25542275769569973854078765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17028183846379982569385843 25542275769569973854078765)
              ·
                refine ⟨9578353413588740195279537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25542275769569973854078765 9578353413588740195279537)
                ·
                  refine ⟨7183765060191555146459653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9578353413588740195279537 7183765060191555146459653)
                  ·
                    refine ⟨1346955948785916589961185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7183765060191555146459653 1346955948785916589961185)
                    ·
                      rfl

theorem cell22_3934781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_3934781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934781 prefixEnd_3934781 := by exact prefixLift 3934781
  have htrace : WordTrace (prefixWord ++ tailWord_3934781) baseStart_3934781 baseEnd_3934781 := by
    simpa [prefixWord, tailWord_3934781, baseEnd_3934781] using wordTrace_append hprefix tailTrace_3934781
  have hstable : (prefixWord ++ tailWord_3934781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934781).length < 2 ^ (prefixWord ++ tailWord_3934781).sum := by decide
  have hdescent : baseEnd_3934781 < baseStart_3934781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934920 : List Nat := [2, 1, 3, 1, 2, 4, 3, 2, 4]
def baseStart_3934920 : Nat := 118140960795 + 3934920 * 2 ^ 59
def prefixEnd_3934920 : Nat := 4983230072969 + 3 ^ 40 * 3934920 * 2
def baseEnd_3934920 : Nat := 449001177108855520245253

theorem tailTrace_3934920 : CollatzResearch.WordTrace tailWord_3934920 prefixEnd_3934920 449001177108855520245253 := by
  unfold tailWord_3934920
  simp only [CollatzResearch.WordTrace]
  refine ⟨71759161452232172839001107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95678881936309563785334809 71759161452232172839001107)
  ·
    refine ⟨107638742178348259258501661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71759161452232172839001107 107638742178348259258501661)
    ·
      refine ⟨40364528316880597221938123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107638742178348259258501661 40364528316880597221938123)
      ·
        refine ⟨60546792475320895832907185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40364528316880597221938123 60546792475320895832907185)
        ·
          refine ⟨45410094356490671874680389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60546792475320895832907185 45410094356490671874680389)
          ·
            refine ⟨8514392691842000976502573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45410094356490671874680389 8514392691842000976502573)
            ·
              refine ⟨3192897259440750366188465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8514392691842000976502573 3192897259440750366188465)
              ·
                refine ⟨2394672944580562774641349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192897259440750366188465 2394672944580562774641349)
                ·
                  refine ⟨449001177108855520245253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2394672944580562774641349 449001177108855520245253)
                  ·
                    rfl

theorem cell22_3934920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 4].length) (baseStart_3934920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934920 prefixEnd_3934920 := by exact prefixLift 3934920
  have htrace : WordTrace (prefixWord ++ tailWord_3934920) baseStart_3934920 baseEnd_3934920 := by
    simpa [prefixWord, tailWord_3934920, baseEnd_3934920] using wordTrace_append hprefix tailTrace_3934920
  have hstable : (prefixWord ++ tailWord_3934920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934920).length < 2 ^ (prefixWord ++ tailWord_3934920).sum := by decide
  have hdescent : baseEnd_3934920 < baseStart_3934920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934935 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 2, 3]
def baseStart_3934935 : Nat := 118140960795 + 3934935 * 2 ^ 59
def prefixEnd_3934935 : Nat := 4983230072969 + 3 ^ 40 * 3934935 * 2
def baseEnd_3934935 : Nat := 1347008666133111521610713

theorem tailTrace_3934935 : CollatzResearch.WordTrace tailWord_3934935 prefixEnd_3934935 1347008666133111521610713 := by
  unfold tailWord_3934935
  simp only [CollatzResearch.WordTrace]
  refine ⟨143518869999410003239798259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95679246666273335493198839 143518869999410003239798259)
  ·
    refine ⟨215278304999115004859697389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143518869999410003239798259 215278304999115004859697389)
    ·
      refine ⟨80729364374668126822386521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215278304999115004859697389 80729364374668126822386521)
      ·
        refine ⟨60547023281001095116789891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80729364374668126822386521 60547023281001095116789891)
        ·
          refine ⟨90820534921501642675184837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60547023281001095116789891 90820534921501642675184837)
          ·
            refine ⟨17028850297781558001597157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90820534921501642675184837 17028850297781558001597157)
            ·
              refine ⟨3192909430834042125299467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17028850297781558001597157 3192909430834042125299467)
              ·
                refine ⟨4789364146251063187949201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192909430834042125299467 4789364146251063187949201)
                ·
                  refine ⟨3592023109688297390961901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4789364146251063187949201 3592023109688297390961901)
                  ·
                    refine ⟨1347008666133111521610713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592023109688297390961901 1347008666133111521610713)
                    ·
                      rfl

theorem cell22_3934935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_3934935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934935 prefixEnd_3934935 := by exact prefixLift 3934935
  have htrace : WordTrace (prefixWord ++ tailWord_3934935) baseStart_3934935 baseEnd_3934935 := by
    simpa [prefixWord, tailWord_3934935, baseEnd_3934935] using wordTrace_append hprefix tailTrace_3934935
  have hstable : (prefixWord ++ tailWord_3934935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934935).length < 2 ^ (prefixWord ++ tailWord_3934935).sum := by decide
  have hdescent : baseEnd_3934935 < baseStart_3934935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934965 : List Nat := [1, 3, 6, 1, 1, 10]
def baseStart_3934965 : Nat := 118140960795 + 3934965 * 2 ^ 59
def prefixEnd_3934965 : Nat := 4983230072969 + 3 ^ 40 * 3934965 * 2
def baseEnd_3934965 : Nat := 16629863404274091893341

theorem tailTrace_3934965 : CollatzResearch.WordTrace tailWord_3934965 prefixEnd_3934965 16629863404274091893341 := by
  unfold tailWord_3934965
  simp only [CollatzResearch.WordTrace]
  refine ⟨143519964189301318363390349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95679976126200878908926899 143519964189301318363390349)
  ·
    refine ⟨53819986570987994386271381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143519964189301318363390349 53819986570987994386271381)
    ·
      refine ⟨2522811870515062236856471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53819986570987994386271381 2522811870515062236856471)
      ·
        refine ⟨3784217805772593355284707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522811870515062236856471 3784217805772593355284707)
        ·
          refine ⟨5676326708658890032927061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784217805772593355284707 5676326708658890032927061)
          ·
            refine ⟨16629863404274091893341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5676326708658890032927061 16629863404274091893341)
            ·
              rfl

theorem cell22_3934965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 10].length) (baseStart_3934965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934965 prefixEnd_3934965 := by exact prefixLift 3934965
  have htrace : WordTrace (prefixWord ++ tailWord_3934965) baseStart_3934965 baseEnd_3934965 := by
    simpa [prefixWord, tailWord_3934965, baseEnd_3934965] using wordTrace_append hprefix tailTrace_3934965
  have hstable : (prefixWord ++ tailWord_3934965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934965).length < 2 ^ (prefixWord ++ tailWord_3934965).sum := by decide
  have hdescent : baseEnd_3934965 < baseStart_3934965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934978 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3934978 : Nat := 118140960795 + 3934978 * 2 ^ 59
def prefixEnd_3934978 : Nat := 4983230072969 + 3 ^ 40 * 3934978 * 2
def baseEnd_3934978 : Nat := 1347023385911873742785581

theorem tailTrace_3934978 : CollatzResearch.WordTrace tailWord_3934978 prefixEnd_3934978 1347023385911873742785581 := by
  unfold tailWord_3934978
  simp only [CollatzResearch.WordTrace]
  refine ⟨35880109584563555395903397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95680292225502814389075725 35880109584563555395903397)
  ·
    refine ⟨6727520547105666636731887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35880109584563555395903397 6727520547105666636731887)
    ·
      refine ⟨10091280820658499955097831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6727520547105666636731887 10091280820658499955097831)
      ·
        refine ⟨15136921230987749932646747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10091280820658499955097831 15136921230987749932646747)
        ·
          refine ⟨22705381846481624898970121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15136921230987749932646747 22705381846481624898970121)
          ·
            refine ⟨17029036384861218674227591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22705381846481624898970121 17029036384861218674227591)
            ·
              refine ⟨25543554577291828011341387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17029036384861218674227591 25543554577291828011341387)
              ·
                refine ⟨38315331865937742017012081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25543554577291828011341387 38315331865937742017012081)
                ·
                  refine ⟨28736498899453306512759061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38315331865937742017012081 28736498899453306512759061)
                  ·
                    refine ⟨1347023385911873742785581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28736498899453306512759061 1347023385911873742785581)
                    ·
                      rfl

theorem cell22_3934978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3934978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934978 prefixEnd_3934978 := by exact prefixLift 3934978
  have htrace : WordTrace (prefixWord ++ tailWord_3934978) baseStart_3934978 baseEnd_3934978 := by
    simpa [prefixWord, tailWord_3934978, baseEnd_3934978] using wordTrace_append hprefix tailTrace_3934978
  have hstable : (prefixWord ++ tailWord_3934978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934978).length < 2 ^ (prefixWord ++ tailWord_3934978).sum := by decide
  have hdescent : baseEnd_3934978 < baseStart_3934978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3934991 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 2, 5]
def baseStart_3934991 : Nat := 118140960795 + 3934991 * 2 ^ 59
def prefixEnd_3934991 : Nat := 4983230072969 + 3 ^ 40 * 3934991 * 2
def baseEnd_3934991 : Nat := 1347027836077546042210541

theorem tailTrace_3934991 : CollatzResearch.WordTrace tailWord_3934991 prefixEnd_3934991 1347027836077546042210541 := by
  unfold tailWord_3934991
  simp only [CollatzResearch.WordTrace]
  refine ⟨143520912487207124803836827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95680608324804749869224551 143520912487207124803836827)
  ·
    refine ⟨215281368730810687205755241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143520912487207124803836827 215281368730810687205755241)
    ·
      refine ⟨161461026548108015404316431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215281368730810687205755241 161461026548108015404316431)
      ·
        refine ⟨242191539822162023106474647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161461026548108015404316431 242191539822162023106474647)
        ·
          refine ⟨363287309733243034659711971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242191539822162023106474647 363287309733243034659711971)
          ·
            refine ⟨544930964599864551989567957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363287309733243034659711971 544930964599864551989567957)
            ·
              refine ⟨12771819482809325437255499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 544930964599864551989567957 12771819482809325437255499)
              ·
                refine ⟨19157729224213988155883249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12771819482809325437255499 19157729224213988155883249)
                ·
                  refine ⟨14368296918160491116912437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19157729224213988155883249 14368296918160491116912437)
                  ·
                    refine ⟨1347027836077546042210541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14368296918160491116912437 1347027836077546042210541)
                    ·
                      rfl

theorem cell22_3934991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_3934991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3934991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3934991 prefixEnd_3934991 := by exact prefixLift 3934991
  have htrace : WordTrace (prefixWord ++ tailWord_3934991) baseStart_3934991 baseEnd_3934991 := by
    simpa [prefixWord, tailWord_3934991, baseEnd_3934991] using wordTrace_append hprefix tailTrace_3934991
  have hstable : (prefixWord ++ tailWord_3934991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3934991).length < 2 ^ (prefixWord ++ tailWord_3934991).sum := by decide
  have hdescent : baseEnd_3934991 < baseStart_3934991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3934991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935044 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 5]
def baseStart_3935044 : Nat := 118140960795 + 3935044 * 2 ^ 59
def prefixEnd_3935044 : Nat := 4983230072969 + 3 ^ 40 * 3935044 * 2
def baseEnd_3935044 : Nat := 449015326353557190211793

theorem tailTrace_3935044 : CollatzResearch.WordTrace tailWord_3935044 prefixEnd_3935044 449015326353557190211793 := by
  unfold tailWord_3935044
  simp only [CollatzResearch.WordTrace]
  refine ⟨71761422778007557427758093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95681897037343409903677457 71761422778007557427758093)
  ·
    refine ⟨26910533541752834035409285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71761422778007557427758093 26910533541752834035409285)
    ·
      refine ⟨5045725039078656381639241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26910533541752834035409285 5045725039078656381639241)
      ·
        refine ⟨3784293779308992286229431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5045725039078656381639241 3784293779308992286229431)
        ·
          refine ⟨5676440668963488429344147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784293779308992286229431 5676440668963488429344147)
          ·
            refine ⟨8514661003445232644016221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676440668963488429344147 8514661003445232644016221)
            ·
              refine ⟨3192997876291962241506083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8514661003445232644016221 3192997876291962241506083)
              ·
                refine ⟨4789496814437943362259125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192997876291962241506083 4789496814437943362259125)
                ·
                  refine ⟨449015326353557190211793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4789496814437943362259125 449015326353557190211793)
                  ·
                    rfl

theorem cell22_3935044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_3935044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935044 prefixEnd_3935044 := by exact prefixLift 3935044
  have htrace : WordTrace (prefixWord ++ tailWord_3935044) baseStart_3935044 baseEnd_3935044 := by
    simpa [prefixWord, tailWord_3935044, baseEnd_3935044] using wordTrace_append hprefix tailTrace_3935044
  have hstable : (prefixWord ++ tailWord_3935044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935044).length < 2 ^ (prefixWord ++ tailWord_3935044).sum := by decide
  have hdescent : baseEnd_3935044 < baseStart_3935044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935192 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 1, 4]
def baseStart_3935192 : Nat := 118140960795 + 3935192 * 2 ^ 59
def prefixEnd_3935192 : Nat := 4983230072969 + 3 ^ 40 * 3935192 * 2
def baseEnd_3935192 : Nat := 1347096642485248517934925

theorem tailTrace_3935192 : CollatzResearch.WordTrace tailWord_3935192 prefixEnd_3935192 1347096642485248517934925 := by
  unfold tailWord_3935192
  simp only [CollatzResearch.WordTrace]
  refine ⟨71764121779739468065951915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95685495706319290754602553 71764121779739468065951915)
  ·
    refine ⟨107646182669609202098927873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71764121779739468065951915 107646182669609202098927873)
    ·
      refine ⟨80734637002206901574195905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107646182669609202098927873 80734637002206901574195905)
      ·
        refine ⟨60550977751655176180646929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80734637002206901574195905 60550977751655176180646929)
        ·
          refine ⟨45413233313741382135485197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60550977751655176180646929 45413233313741382135485197)
          ·
            refine ⟨17029962492653018300806949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45413233313741382135485197 17029962492653018300806949)
            ·
              refine ⟨3193117967372440931401303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17029962492653018300806949 3193117967372440931401303)
              ·
                refine ⟨4789676951058661397101955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193117967372440931401303 4789676951058661397101955)
                ·
                  refine ⟨7184515426587992095652933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789676951058661397101955 7184515426587992095652933)
                  ·
                    refine ⟨1347096642485248517934925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7184515426587992095652933 1347096642485248517934925)
                    ·
                      rfl

theorem cell22_3935192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_3935192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935192 prefixEnd_3935192 := by exact prefixLift 3935192
  have htrace : WordTrace (prefixWord ++ tailWord_3935192) baseStart_3935192 baseEnd_3935192 := by
    simpa [prefixWord, tailWord_3935192, baseEnd_3935192] using wordTrace_append hprefix tailTrace_3935192
  have hstable : (prefixWord ++ tailWord_3935192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935192).length < 2 ^ (prefixWord ++ tailWord_3935192).sum := by decide
  have hdescent : baseEnd_3935192 < baseStart_3935192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935207 : List Nat := [1, 1, 5, 2, 2, 1, 2, 4, 4]
def baseStart_3935207 : Nat := 118140960795 + 3935207 * 2 ^ 59
def prefixEnd_3935207 : Nat := 4983230072969 + 3 ^ 40 * 3935207 * 2
def baseEnd_3935207 : Nat := 449033925763931159603293

theorem tailTrace_3935207 : CollatzResearch.WordTrace tailWord_3935207 prefixEnd_3935207 449033925763931159603293 := by
  unfold tailWord_3935207
  simp only [CollatzResearch.WordTrace]
  refine ⟨143528790654424593693699875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95685860436283062462466583 143528790654424593693699875)
  ·
    refine ⟨215293185981636890540549813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143528790654424593693699875 215293185981636890540549813)
    ·
      refine ⟨20183736185778458488176545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215293185981636890540549813 20183736185778458488176545)
      ·
        refine ⟨15137802139333843866132409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20183736185778458488176545 15137802139333843866132409)
        ·
          refine ⟨11353351604500382899599307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15137802139333843866132409 11353351604500382899599307)
          ·
            refine ⟨17030027406750574349398961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11353351604500382899599307 17030027406750574349398961)
            ·
              refine ⟨12772520555062930762049221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17030027406750574349398961 12772520555062930762049221)
              ·
                refine ⟨2394847604074299517884229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12772520555062930762049221 2394847604074299517884229)
                ·
                  refine ⟨449033925763931159603293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2394847604074299517884229 449033925763931159603293)
                  ·
                    rfl

theorem cell22_3935207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 4].length) (baseStart_3935207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935207 prefixEnd_3935207 := by exact prefixLift 3935207
  have htrace : WordTrace (prefixWord ++ tailWord_3935207) baseStart_3935207 baseEnd_3935207 := by
    simpa [prefixWord, tailWord_3935207, baseEnd_3935207] using wordTrace_append hprefix tailTrace_3935207
  have hstable : (prefixWord ++ tailWord_3935207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935207).length < 2 ^ (prefixWord ++ tailWord_3935207).sum := by decide
  have hdescent : baseEnd_3935207 < baseStart_3935207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935222 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3935222 : Nat := 118140960795 + 3935222 * 2 ^ 59
def prefixEnd_3935222 : Nat := 4983230072969 + 3 ^ 40 * 3935222 * 2
def baseEnd_3935222 : Nat := 1347106912098338439684833

theorem tailTrace_3935222 : CollatzResearch.WordTrace tailWord_3935222 prefixEnd_3935222 1347106912098338439684833 := by
  unfold tailWord_3935222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8970583609335640703468495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95686225166246834170330613 8970583609335640703468495)
  ·
    refine ⟨13455875414003461055202743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8970583609335640703468495 13455875414003461055202743)
    ·
      refine ⟨20183813121005191582804115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13455875414003461055202743 20183813121005191582804115)
      ·
        refine ⟨30275719681507787374206173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20183813121005191582804115 30275719681507787374206173)
        ·
          refine ⟨11353394880565420265327315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30275719681507787374206173 11353394880565420265327315)
          ·
            refine ⟨17030092320848130397990973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11353394880565420265327315 17030092320848130397990973)
            ·
              refine ⟨6386284620318048899246615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17030092320848130397990973 6386284620318048899246615)
              ·
                refine ⟨9579426930477073348869923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386284620318048899246615 9579426930477073348869923)
                ·
                  refine ⟨14369140395715610023304885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9579426930477073348869923 14369140395715610023304885)
                  ·
                    refine ⟨1347106912098338439684833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14369140395715610023304885 1347106912098338439684833)
                    ·
                      rfl

theorem cell22_3935222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3935222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935222 prefixEnd_3935222 := by exact prefixLift 3935222
  have htrace : WordTrace (prefixWord ++ tailWord_3935222) baseStart_3935222 baseEnd_3935222 := by
    simpa [prefixWord, tailWord_3935222, baseEnd_3935222] using wordTrace_append hprefix tailTrace_3935222
  have hstable : (prefixWord ++ tailWord_3935222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935222).length < 2 ^ (prefixWord ++ tailWord_3935222).sum := by decide
  have hdescent : baseEnd_3935222 < baseStart_3935222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935267 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 3, 3]
def baseStart_3935267 : Nat := 118140960795 + 3935267 * 2 ^ 59
def prefixEnd_3935267 : Nat := 4983230072969 + 3 ^ 40 * 3935267 * 2
def baseEnd_3935267 : Nat := 1347122316517973322309695

theorem tailTrace_3935267 : CollatzResearch.WordTrace tailWord_3935267 prefixEnd_3935267 1347122316517973322309695 := by
  unfold tailWord_3935267
  simp only [CollatzResearch.WordTrace]
  refine ⟨143530979034207223940884055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95687319356138149293922703 143530979034207223940884055)
  ·
    refine ⟨215296468551310835911326083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143530979034207223940884055 215296468551310835911326083)
    ·
      refine ⟨322944702826966253866989125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215296468551310835911326083 322944702826966253866989125)
      ·
        refine ⟨60552131780056172600060461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322944702826966253866989125 60552131780056172600060461)
        ·
          refine ⟨22707049417521064725022673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60552131780056172600060461 22707049417521064725022673)
          ·
            refine ⟨17030287063140798543767005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22707049417521064725022673 17030287063140798543767005)
            ·
              refine ⟨6386357648677799453912627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17030287063140798543767005 6386357648677799453912627)
              ·
                refine ⟨9579536473016699180868941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386357648677799453912627 9579536473016699180868941)
                ·
                  refine ⟨3592326177381262192825853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9579536473016699180868941 3592326177381262192825853)
                  ·
                    refine ⟨1347122316517973322309695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592326177381262192825853 1347122316517973322309695)
                    ·
                      rfl

theorem cell22_3935267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 3].length) (baseStart_3935267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935267 prefixEnd_3935267 := by exact prefixLift 3935267
  have htrace : WordTrace (prefixWord ++ tailWord_3935267) baseStart_3935267 baseEnd_3935267 := by
    simpa [prefixWord, tailWord_3935267, baseEnd_3935267] using wordTrace_append hprefix tailTrace_3935267
  have hstable : (prefixWord ++ tailWord_3935267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935267).length < 2 ^ (prefixWord ++ tailWord_3935267).sum := by decide
  have hdescent : baseEnd_3935267 < baseStart_3935267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935280 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 5]
def baseStart_3935280 : Nat := 118140960795 + 3935280 * 2 ^ 59
def prefixEnd_3935280 : Nat := 4983230072969 + 3 ^ 40 * 3935280 * 2
def baseEnd_3935280 : Nat := 449042255561215207244885

theorem tailTrace_3935280 : CollatzResearch.WordTrace tailWord_3935280 prefixEnd_3935280 449042255561215207244885 := by
  unfold tailWord_3935280
  simp only [CollatzResearch.WordTrace]
  refine ⟨71765726591580063580553647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95687635455440084774071529 71765726591580063580553647)
  ·
    refine ⟨107648589887370095370830471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71765726591580063580553647 107648589887370095370830471)
    ·
      refine ⟨161472884831055143056245707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107648589887370095370830471 161472884831055143056245707)
      ·
        refine ⟨242209327246582714584368561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161472884831055143056245707 242209327246582714584368561)
        ·
          refine ⟨181656995434937035938276421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242209327246582714584368561 181656995434937035938276421)
          ·
            refine ⟨34060686644050694238426829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181656995434937035938276421 34060686644050694238426829)
            ·
              refine ⟨12772757491519010339410061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34060686644050694238426829 12772757491519010339410061)
              ·
                refine ⟨4789784059319628877278773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12772757491519010339410061 4789784059319628877278773)
                ·
                  refine ⟨449042255561215207244885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4789784059319628877278773 449042255561215207244885)
                  ·
                    rfl

theorem cell22_3935280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_3935280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935280 prefixEnd_3935280 := by exact prefixLift 3935280
  have htrace : WordTrace (prefixWord ++ tailWord_3935280) baseStart_3935280 baseEnd_3935280 := by
    simpa [prefixWord, tailWord_3935280, baseEnd_3935280] using wordTrace_append hprefix tailTrace_3935280
  have hstable : (prefixWord ++ tailWord_3935280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935280).length < 2 ^ (prefixWord ++ tailWord_3935280).sum := by decide
  have hdescent : baseEnd_3935280 < baseStart_3935280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935342 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_3935342 : Nat := 118140960795 + 3935342 * 2 ^ 59
def prefixEnd_3935342 : Nat := 4983230072969 + 3 ^ 40 * 3935342 * 2
def baseEnd_3935342 : Nat := 449049330183566042228155

theorem tailTrace_3935342 : CollatzResearch.WordTrace tailWord_3935342 prefixEnd_3935342 449049330183566042228155 := by
  unfold tailWord_3935342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17941714313616938968733035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95689143005957007833242853 17941714313616938968733035)
  ·
    refine ⟨26912571470425408453099553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17941714313616938968733035 26912571470425408453099553)
    ·
      refine ⟨20184428602819056339824665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26912571470425408453099553 20184428602819056339824665)
      ·
        refine ⟨15138321452114292254868499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20184428602819056339824665 15138321452114292254868499)
        ·
          refine ⟨22707482178171438382302749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15138321452114292254868499 22707482178171438382302749)
          ·
            refine ⟨8515305816814289393363531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22707482178171438382302749 8515305816814289393363531)
            ·
              refine ⟨12772958725221434090045297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8515305816814289393363531 12772958725221434090045297)
              ·
                refine ⟨9579719043916075567533973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12772958725221434090045297 9579719043916075567533973)
                ·
                  refine ⟨449049330183566042228155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9579719043916075567533973 449049330183566042228155)
                  ·
                    rfl

theorem cell22_3935342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_3935342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935342 prefixEnd_3935342 := by exact prefixLift 3935342
  have htrace : WordTrace (prefixWord ++ tailWord_3935342) baseStart_3935342 baseEnd_3935342 := by
    simpa [prefixWord, tailWord_3935342, baseEnd_3935342] using wordTrace_append hprefix tailTrace_3935342
  have hstable : (prefixWord ++ tailWord_3935342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935342).length < 2 ^ (prefixWord ++ tailWord_3935342).sum := by decide
  have hdescent : baseEnd_3935342 < baseStart_3935342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935357 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_3935357 : Nat := 118140960795 + 3935357 * 2 ^ 59
def prefixEnd_3935357 : Nat := 4983230072969 + 3 ^ 40 * 3935357 * 2
def baseEnd_3935357 : Nat := 1347153125357243087559419

theorem tailTrace_3935357 : CollatzResearch.WordTrace tailWord_3935357 prefixEnd_3935357 1347153125357243087559419 := by
  unfold tailWord_3935357
  simp only [CollatzResearch.WordTrace]
  refine ⟨143534261603881169311660325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95689507735920779541106883 143534261603881169311660325)
  ·
    refine ⟨26912674050727719245936311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143534261603881169311660325 26912674050727719245936311)
    ·
      refine ⟨40369011076091578868904467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26912674050727719245936311 40369011076091578868904467)
      ·
        refine ⟨60553516614137368303356701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40369011076091578868904467 60553516614137368303356701)
        ·
          refine ⟨22707568730301513113758763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60553516614137368303356701 22707568730301513113758763)
          ·
            refine ⟨34061353095452269670638145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22707568730301513113758763 34061353095452269670638145)
            ·
              refine ⟨25546014821589202252978609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34061353095452269670638145 25546014821589202252978609)
              ·
                refine ⟨19159511116191901689733957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25546014821589202252978609 19159511116191901689733957)
                ·
                  refine ⟨3592408334285981566825117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19159511116191901689733957 3592408334285981566825117)
                  ·
                    refine ⟨1347153125357243087559419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592408334285981566825117 1347153125357243087559419)
                    ·
                      rfl

theorem cell22_3935357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_3935357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935357 prefixEnd_3935357 := by exact prefixLift 3935357
  have htrace : WordTrace (prefixWord ++ tailWord_3935357) baseStart_3935357 baseEnd_3935357 := by
    simpa [prefixWord, tailWord_3935357, baseEnd_3935357] using wordTrace_append hprefix tailTrace_3935357
  have hstable : (prefixWord ++ tailWord_3935357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935357).length < 2 ^ (prefixWord ++ tailWord_3935357).sum := by decide
  have hdescent : baseEnd_3935357 < baseStart_3935357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935361 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3935361 : Nat := 118140960795 + 3935361 * 2 ^ 59
def prefixEnd_3935361 : Nat := 4983230072969 + 3 ^ 40 * 3935361 * 2
def baseEnd_3935361 : Nat := 1347154494638988410459407

theorem tailTrace_3935361 : CollatzResearch.WordTrace tailWord_3935361 prefixEnd_3935361 1347154494638988410459407 := by
  unfold tailWord_3935361
  simp only [CollatzResearch.WordTrace]
  refine ⟨143534407495866677994805937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95689604997244451996537291 143534407495866677994805937)
  ·
    refine ⟨107650805621900008496104453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143534407495866677994805937 107650805621900008496104453)
    ·
      refine ⟨20184526054106251593019585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107650805621900008496104453 20184526054106251593019585)
      ·
        refine ⟨15138394540579688694764689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20184526054106251593019585 15138394540579688694764689)
        ·
          refine ⟨11353795905434766521073517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15138394540579688694764689 11353795905434766521073517)
          ·
            refine ⟨4257673464538037445402569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11353795905434766521073517 4257673464538037445402569)
            ·
              refine ⟨3193255098403528084051927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257673464538037445402569 3193255098403528084051927)
              ·
                refine ⟨4789882647605292126077891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193255098403528084051927 4789882647605292126077891)
                ·
                  refine ⟨7184823971407938189116837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789882647605292126077891 7184823971407938189116837)
                  ·
                    refine ⟨1347154494638988410459407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7184823971407938189116837 1347154494638988410459407)
                    ·
                      rfl

theorem cell22_3935361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3935361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935361 prefixEnd_3935361 := by exact prefixLift 3935361
  have htrace : WordTrace (prefixWord ++ tailWord_3935361) baseStart_3935361 baseEnd_3935361 := by
    simpa [prefixWord, tailWord_3935361, baseEnd_3935361] using wordTrace_append hprefix tailTrace_3935361
  have hstable : (prefixWord ++ tailWord_3935361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935361).length < 2 ^ (prefixWord ++ tailWord_3935361).sum := by decide
  have hdescent : baseEnd_3935361 < baseStart_3935361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935370 : List Nat := [3, 1, 2, 3, 1, 1, 11]
def baseStart_3935370 : Nat := 118140960795 + 3935370 * 2 ^ 59
def prefixEnd_3935370 : Nat := 4983230072969 + 3 ^ 40 * 3935370 * 2
def baseEnd_3935370 : Nat := 49894725019367236554977

theorem tailTrace_3935370 : CollatzResearch.WordTrace tailWord_3935370 prefixEnd_3935370 49894725019367236554977 := by
  unfold tailWord_3935370
  simp only [CollatzResearch.WordTrace]
  refine ⟨35883683938208518132970891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95689823835222715021255709 35883683938208518132970891)
  ·
    refine ⟨53825525907312777199456337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35883683938208518132970891 53825525907312777199456337)
    ·
      refine ⟨40369144430484582899592253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53825525907312777199456337 40369144430484582899592253)
      ·
        refine ⟨15138429161431718587347095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40369144430484582899592253 15138429161431718587347095)
        ·
          refine ⟨22707643742147577881020643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15138429161431718587347095 22707643742147577881020643)
          ·
            refine ⟨34061465613221366821530965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22707643742147577881020643 34061465613221366821530965)
            ·
              refine ⟨49894725019367236554977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34061465613221366821530965 49894725019367236554977)
              ·
                rfl

theorem cell22_3935370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 11].length) (baseStart_3935370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935370 prefixEnd_3935370 := by exact prefixLift 3935370
  have htrace : WordTrace (prefixWord ++ tailWord_3935370) baseStart_3935370 baseEnd_3935370 := by
    simpa [prefixWord, tailWord_3935370, baseEnd_3935370] using wordTrace_append hprefix tailTrace_3935370
  have hstable : (prefixWord ++ tailWord_3935370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935370).length < 2 ^ (prefixWord ++ tailWord_3935370).sum := by decide
  have hdescent : baseEnd_3935370 < baseStart_3935370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935374 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_3935374 : Nat := 118140960795 + 3935374 * 2 ^ 59
def prefixEnd_3935374 : Nat := 4983230072969 + 3 ^ 40 * 3935374 * 2
def baseEnd_3935374 : Nat := 1347158944804660709884367

theorem tailTrace_3935374 : CollatzResearch.WordTrace tailWord_3935374 prefixEnd_3935374 1347158944804660709884367 := by
  unfold tailWord_3935374
  simp only [CollatzResearch.WordTrace]
  refine ⟨17941860205602447651878647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95689921096546387476686117 17941860205602447651878647)
  ·
    refine ⟨26912790308403671477817971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17941860205602447651878647 26912790308403671477817971)
    ·
      refine ⟨40369185462605507216726957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26912790308403671477817971 40369185462605507216726957)
      ·
        refine ⟨15138444548477065206272609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40369185462605507216726957 15138444548477065206272609)
        ·
          refine ⟨11353833411357798904704457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15138444548477065206272609 11353833411357798904704457)
          ·
            refine ⟨8515375058518349178528343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11353833411357798904704457 8515375058518349178528343)
            ·
              refine ⟨12773062587777523767792515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8515375058518349178528343 12773062587777523767792515)
              ·
                refine ⟨19159593881666285651688773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12773062587777523767792515 19159593881666285651688773)
                ·
                  refine ⟨3592423852812428559691645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19159593881666285651688773 3592423852812428559691645)
                  ·
                    refine ⟨1347158944804660709884367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592423852812428559691645 1347158944804660709884367)
                    ·
                      rfl

theorem cell22_3935374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_3935374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935374 prefixEnd_3935374 := by exact prefixLift 3935374
  have htrace : WordTrace (prefixWord ++ tailWord_3935374) baseStart_3935374 baseEnd_3935374 := by
    simpa [prefixWord, tailWord_3935374, baseEnd_3935374] using wordTrace_append hprefix tailTrace_3935374
  have hstable : (prefixWord ++ tailWord_3935374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935374).length < 2 ^ (prefixWord ++ tailWord_3935374).sum := by decide
  have hdescent : baseEnd_3935374 < baseStart_3935374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935391 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 1, 5]
def baseStart_3935391 : Nat := 118140960795 + 3935391 * 2 ^ 59
def prefixEnd_3935391 : Nat := 4983230072969 + 3 ^ 40 * 3935391 * 2
def baseEnd_3935391 : Nat := 1347164764252078332209315

theorem tailTrace_3935391 : CollatzResearch.WordTrace tailWord_3935391 prefixEnd_3935391 1347164764252078332209315 := by
  unfold tailWord_3935391
  simp only [CollatzResearch.WordTrace]
  refine ⟨143535501685757993118398027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95690334457171995412265351 143535501685757993118398027)
  ·
    refine ⟨215303252528636989677597041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143535501685757993118398027 215303252528636989677597041)
    ·
      refine ⟨161477439396477742258197781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215303252528636989677597041 161477439396477742258197781)
      ·
        refine ⟨7569254971709894168353021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161477439396477742258197781 7569254971709894168353021)
        ·
          refine ⟨2838470614391210313132383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7569254971709894168353021 2838470614391210313132383)
          ·
            refine ⟨4257705921586815469698575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838470614391210313132383 4257705921586815469698575)
            ·
              refine ⟨6386558882380223204547863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257705921586815469698575 6386558882380223204547863)
              ·
                refine ⟨9579838323570334806821795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386558882380223204547863 9579838323570334806821795)
                ·
                  refine ⟨14369757485355502210232693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9579838323570334806821795 14369757485355502210232693)
                  ·
                    refine ⟨1347164764252078332209315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14369757485355502210232693 1347164764252078332209315)
                    ·
                      rfl

theorem cell22_3935391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 5].length) (baseStart_3935391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935391 prefixEnd_3935391 := by exact prefixLift 3935391
  have htrace : WordTrace (prefixWord ++ tailWord_3935391) baseStart_3935391 baseEnd_3935391 := by
    simpa [prefixWord, tailWord_3935391, baseEnd_3935391] using wordTrace_append hprefix tailTrace_3935391
  have hstable : (prefixWord ++ tailWord_3935391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935391).length < 2 ^ (prefixWord ++ tailWord_3935391).sum := by decide
  have hdescent : baseEnd_3935391 < baseStart_3935391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935415 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 9]
def baseStart_3935415 : Nat := 118140960795 + 3935415 * 2 ^ 59
def prefixEnd_3935415 : Nat := 4983230072969 + 3 ^ 40 * 3935415 * 2
def baseEnd_3935415 : Nat := 449057659980850089869747

theorem tailTrace_3935415 : CollatzResearch.WordTrace tailWord_3935415 prefixEnd_3935415 449057659980850089869747 := by
  unfold tailWord_3935415
  simp only [CollatzResearch.WordTrace]
  refine ⟨143536377037671045217271699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95690918025114030144847799 143536377037671045217271699)
  ·
    refine ⟨215304565556506567825907549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143536377037671045217271699 215304565556506567825907549)
    ·
      refine ⟨80739212083689962934715331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215304565556506567825907549 80739212083689962934715331)
      ·
        refine ⟨121108818125534944402072997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80739212083689962934715331 121108818125534944402072997)
        ·
          refine ⟨22707903398537802075388687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121108818125534944402072997 22707903398537802075388687)
          ·
            refine ⟨34061855097806703113083031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22707903398537802075388687 34061855097806703113083031)
            ·
              refine ⟨51092782646710054669624547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34061855097806703113083031 51092782646710054669624547)
              ·
                refine ⟨76639173970065082004436821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51092782646710054669624547 76639173970065082004436821)
                ·
                  refine ⟨449057659980850089869747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76639173970065082004436821 449057659980850089869747)
                  ·
                    rfl

theorem cell22_3935415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 9].length) (baseStart_3935415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935415 prefixEnd_3935415 := by exact prefixLift 3935415
  have htrace : WordTrace (prefixWord ++ tailWord_3935415) baseStart_3935415 baseEnd_3935415 := by
    simpa [prefixWord, tailWord_3935415, baseEnd_3935415] using wordTrace_append hprefix tailTrace_3935415
  have hstable : (prefixWord ++ tailWord_3935415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935415).length < 2 ^ (prefixWord ++ tailWord_3935415).sum := by decide
  have hdescent : baseEnd_3935415 < baseStart_3935415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935419 : List Nat := [1, 1, 1, 1, 1, 2, 4, 7, 1, 3]
def baseStart_3935419 : Nat := 118140960795 + 3935419 * 2 ^ 59
def prefixEnd_3935419 : Nat := 4983230072969 + 3 ^ 40 * 3935419 * 2
def baseEnd_3935419 : Nat := 1347174349224295592509229

theorem tailTrace_3935419 : CollatzResearch.WordTrace tailWord_3935419 prefixEnd_3935419 1347174349224295592509229 := by
  unfold tailWord_3935419
  simp only [CollatzResearch.WordTrace]
  refine ⟨143536522929656553900417311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95691015286437702600278207 143536522929656553900417311)
  ·
    refine ⟨215304784394484830850625967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143536522929656553900417311 215304784394484830850625967)
    ·
      refine ⟨322957176591727246275938951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215304784394484830850625967 322957176591727246275938951)
      ·
        refine ⟨484435764887590869413908427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322957176591727246275938951 484435764887590869413908427)
        ·
          refine ⟨726653647331386304120862641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484435764887590869413908427 726653647331386304120862641)
          ·
            refine ⟨544990235498539728090646981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726653647331386304120862641 544990235498539728090646981)
            ·
              refine ⟨102185669155976199016996309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 544990235498539728090646981 102185669155976199016996309)
              ·
                refine ⟨2394976620843192164460851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102185669155976199016996309 2394976620843192164460851)
                ·
                  refine ⟨3592464931264788246691277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394976620843192164460851 3592464931264788246691277)
                  ·
                    refine ⟨1347174349224295592509229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592464931264788246691277 1347174349224295592509229)
                    ·
                      rfl

theorem cell22_3935419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 1, 3].length) (baseStart_3935419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935419 prefixEnd_3935419 := by exact prefixLift 3935419
  have htrace : WordTrace (prefixWord ++ tailWord_3935419) baseStart_3935419 baseEnd_3935419 := by
    simpa [prefixWord, tailWord_3935419, baseEnd_3935419] using wordTrace_append hprefix tailTrace_3935419
  have hstable : (prefixWord ++ tailWord_3935419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935419).length < 2 ^ (prefixWord ++ tailWord_3935419).sum := by decide
  have hdescent : baseEnd_3935419 < baseStart_3935419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935588 : List Nat := [2, 3, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_3935588 : Nat := 118140960795 + 3935588 * 2 ^ 59
def prefixEnd_3935588 : Nat := 4983230072969 + 3 ^ 40 * 3935588 * 2
def baseEnd_3935588 : Nat := 1347232201378035485033711

theorem tailTrace_3935588 : CollatzResearch.WordTrace tailWord_3935588 prefixEnd_3935588 1347232201378035485033711 := by
  unfold tailWord_3935588
  simp only [CollatzResearch.WordTrace]
  refine ⟨71771343433022147881659709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95695124577362863842212945 71771343433022147881659709)
  ·
    refine ⟨26914253787383305455622391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71771343433022147881659709 26914253787383305455622391)
    ·
      refine ⟨40371380681074958183433587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26914253787383305455622391 40371380681074958183433587)
      ·
        refine ⟨60557071021612437275150381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40371380681074958183433587 60557071021612437275150381)
        ·
          refine ⟨22708901633104663978181393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60557071021612437275150381 22708901633104663978181393)
          ·
            refine ⟨17031676224828497983636045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22708901633104663978181393 17031676224828497983636045)
            ·
              refine ⟨6386878584310686743863517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17031676224828497983636045 6386878584310686743863517)
              ·
                refine ⟨2395079469116507528948819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6386878584310686743863517 2395079469116507528948819)
                ·
                  refine ⟨3592619203674761293423229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395079469116507528948819 3592619203674761293423229)
                  ·
                    refine ⟨1347232201378035485033711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592619203674761293423229 1347232201378035485033711)
                    ·
                      rfl

theorem cell22_3935588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_3935588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935588 prefixEnd_3935588 := by exact prefixLift 3935588
  have htrace : WordTrace (prefixWord ++ tailWord_3935588) baseStart_3935588 baseEnd_3935588 := by
    simpa [prefixWord, tailWord_3935588, baseEnd_3935588] using wordTrace_append hprefix tailTrace_3935588
  have hstable : (prefixWord ++ tailWord_3935588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935588).length < 2 ^ (prefixWord ++ tailWord_3935588).sum := by decide
  have hdescent : baseEnd_3935588 < baseStart_3935588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935605 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3935605 : Nat := 118140960795 + 3935605 * 2 ^ 59
def prefixEnd_3935605 : Nat := 4983230072969 + 3 ^ 40 * 3935605 * 2
def baseEnd_3935605 : Nat := 1347238020825453107358659

theorem tailTrace_3935605 : CollatzResearch.WordTrace tailWord_3935605 prefixEnd_3935605 1347238020825453107358659 := by
  unfold tailWord_3935605
  simp only [CollatzResearch.WordTrace]
  refine ⟨143543306906982707666688269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95695537937988471777792179 143543306906982707666688269)
  ·
    refine ⟨53828740090118515375008101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143543306906982707666688269 53828740090118515375008101)
    ·
      refine ⟨10092888766897221632814019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53828740090118515375008101 10092888766897221632814019)
      ·
        refine ⟨15139333150345832449221029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10092888766897221632814019 15139333150345832449221029)
        ·
          refine ⟨2838624965689843584228943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15139333150345832449221029 2838624965689843584228943)
          ·
            refine ⟨4257937448534765376343415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838624965689843584228943 4257937448534765376343415)
            ·
              refine ⟨6386906172802148064515123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257937448534765376343415 6386906172802148064515123)
              ·
                refine ⟨9580359259203222096772685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386906172802148064515123 9580359259203222096772685)
                ·
                  refine ⟨3592634722201208286289757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9580359259203222096772685 3592634722201208286289757)
                  ·
                    refine ⟨1347238020825453107358659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592634722201208286289757 1347238020825453107358659)
                    ·
                      rfl

theorem cell22_3935605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3935605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935605 prefixEnd_3935605 := by exact prefixLift 3935605
  have htrace : WordTrace (prefixWord ++ tailWord_3935605) baseStart_3935605 baseEnd_3935605 := by
    simpa [prefixWord, tailWord_3935605, baseEnd_3935605] using wordTrace_append hprefix tailTrace_3935605
  have hstable : (prefixWord ++ tailWord_3935605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935605).length < 2 ^ (prefixWord ++ tailWord_3935605).sum := by decide
  have hdescent : baseEnd_3935605 < baseStart_3935605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935618 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3935618 : Nat := 118140960795 + 3935618 * 2 ^ 59
def prefixEnd_3935618 : Nat := 4983230072969 + 3 ^ 40 * 3935618 * 2
def baseEnd_3935618 : Nat := 449080823663708468927873

theorem tailTrace_3935618 : CollatzResearch.WordTrace tailWord_3935618 prefixEnd_3935618 449080823663708468927873 := by
  unfold tailWord_3935618
  simp only [CollatzResearch.WordTrace]
  refine ⟨35885945263983902721727877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95695854037290407257941005 35885945263983902721727877)
  ·
    refine ⟨6728614736996981760323977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35885945263983902721727877 6728614736996981760323977)
    ·
      refine ⟨5046461052747736320242983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6728614736996981760323977 5046461052747736320242983)
      ·
        refine ⟨7569691579121604480364475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5046461052747736320242983 7569691579121604480364475)
        ·
          refine ⟨11354537368682406720546713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7569691579121604480364475 11354537368682406720546713)
          ·
            refine ⟨8515903026511805040410035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11354537368682406720546713 8515903026511805040410035)
            ·
              refine ⟨12773854539767707560615053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8515903026511805040410035 12773854539767707560615053)
              ·
                refine ⟨4790195452412890335230645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12773854539767707560615053 4790195452412890335230645)
                ·
                  refine ⟨449080823663708468927873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4790195452412890335230645 449080823663708468927873)
                  ·
                    rfl

theorem cell22_3935618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3935618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935618 prefixEnd_3935618 := by exact prefixLift 3935618
  have htrace : WordTrace (prefixWord ++ tailWord_3935618) baseStart_3935618 baseEnd_3935618 := by
    simpa [prefixWord, tailWord_3935618, baseEnd_3935618] using wordTrace_append hprefix tailTrace_3935618
  have hstable : (prefixWord ++ tailWord_3935618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935618).length < 2 ^ (prefixWord ++ tailWord_3935618).sum := by decide
  have hdescent : baseEnd_3935618 < baseStart_3935618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935742 : List Nat := [4, 2, 2, 3, 2, 1, 2, 6]
def baseStart_3935742 : Nat := 118140960795 + 3935742 * 2 ^ 59
def prefixEnd_3935742 : Nat := 4983230072969 + 3 ^ 40 * 3935742 * 2
def baseEnd_3935742 : Nat := 149698324302803379631471

theorem tailTrace_3935742 : CollatzResearch.WordTrace tailWord_3935742 prefixEnd_3935742 149698324302803379631471 := by
  unfold tailWord_3935742
  simp only [CollatzResearch.WordTrace]
  refine ⟨17943537963435797508053185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95698869138324253376283653 17943537963435797508053185)
  ·
    refine ⟨13457653472576848131039889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17943537963435797508053185 13457653472576848131039889)
    ·
      refine ⟨10093240104432636098279917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13457653472576848131039889 10093240104432636098279917)
      ·
        refine ⟨3784965039162238536854969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10093240104432636098279917 3784965039162238536854969)
        ·
          refine ⟨2838723779371678902641227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3784965039162238536854969 2838723779371678902641227)
          ·
            refine ⟨4258085669057518353961841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838723779371678902641227 4258085669057518353961841)
            ·
              refine ⟨3193564251793138765471381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4258085669057518353961841 3193564251793138765471381)
              ·
                refine ⟨149698324302803379631471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3193564251793138765471381 149698324302803379631471)
                ·
                  rfl

theorem cell22_3935742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_3935742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935742 prefixEnd_3935742 := by exact prefixLift 3935742
  have htrace : WordTrace (prefixWord ++ tailWord_3935742) baseStart_3935742 baseEnd_3935742 := by
    simpa [prefixWord, tailWord_3935742, baseEnd_3935742] using wordTrace_append hprefix tailTrace_3935742
  have hstable : (prefixWord ++ tailWord_3935742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935742).length < 2 ^ (prefixWord ++ tailWord_3935742).sum := by decide
  have hdescent : baseEnd_3935742 < baseStart_3935742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935858 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_3935858 : Nat := 118140960795 + 3935858 * 2 ^ 59
def prefixEnd_3935858 : Nat := 4983230072969 + 3 ^ 40 * 3935858 * 2
def baseEnd_3935858 : Nat := 1347324627895844780782883

theorem tailTrace_3935858 : CollatzResearch.WordTrace tailWord_3935858 prefixEnd_3935858 1347324627895844780782883 := by
  unfold tailWord_3935858
  simp only [CollatzResearch.WordTrace]
  refine ⟨35888133643766532968912057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95701689716710754583765485 35888133643766532968912057)
  ·
    refine ⟨26916100232824899726684043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35888133643766532968912057 26916100232824899726684043)
    ·
      refine ⟨40374150349237349590026065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26916100232824899726684043 40374150349237349590026065)
      ·
        refine ⟨30280612761928012192519549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40374150349237349590026065 30280612761928012192519549)
        ·
          refine ⟨11355229785723004572194831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30280612761928012192519549 11355229785723004572194831)
          ·
            refine ⟨17032844678584506858292247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11355229785723004572194831 17032844678584506858292247)
            ·
              refine ⟨25549267017876760287438371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17032844678584506858292247 25549267017876760287438371)
              ·
                refine ⟨38323900526815140431157557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25549267017876760287438371 38323900526815140431157557)
                ·
                  refine ⟨3592865674388919415421021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38323900526815140431157557 3592865674388919415421021)
                  ·
                    refine ⟨1347324627895844780782883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592865674388919415421021 1347324627895844780782883)
                    ·
                      rfl

theorem cell22_3935858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_3935858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935858 prefixEnd_3935858 := by exact prefixLift 3935858
  have htrace : WordTrace (prefixWord ++ tailWord_3935858) baseStart_3935858 baseEnd_3935858 := by
    simpa [prefixWord, tailWord_3935858, baseEnd_3935858] using wordTrace_append hprefix tailTrace_3935858
  have hstable : (prefixWord ++ tailWord_3935858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935858).length < 2 ^ (prefixWord ++ tailWord_3935858).sum := by decide
  have hdescent : baseEnd_3935858 < baseStart_3935858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935892 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3935892 : Nat := 118140960795 + 3935892 * 2 ^ 59
def prefixEnd_3935892 : Nat := 4983230072969 + 3 ^ 40 * 3935892 * 2
def baseEnd_3935892 : Nat := 1347336266790680025432779

theorem tailTrace_3935892 : CollatzResearch.WordTrace tailWord_3935892 prefixEnd_3935892 1347336266790680025432779 := by
  unfold tailWord_3935892
  simp only [CollatzResearch.WordTrace]
  refine ⟨71776887328471477841192965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95702516437961970454923953 71776887328471477841192965)
  ·
    refine ⟨13458166374088402095223681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71776887328471477841192965 13458166374088402095223681)
    ·
      refine ⟨10093624780566301571417761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13458166374088402095223681 10093624780566301571417761)
      ·
        refine ⟨7570218585424726178563321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10093624780566301571417761 7570218585424726178563321)
        ·
          refine ⟨5677663939068544633922491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7570218585424726178563321 5677663939068544633922491)
          ·
            refine ⟨8516495908602816950883737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677663939068544633922491 8516495908602816950883737)
            ·
              refine ⟨6387371931452112713162803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8516495908602816950883737 6387371931452112713162803)
              ·
                refine ⟨9581057897178169069744205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6387371931452112713162803 9581057897178169069744205)
                ·
                  refine ⟨3592896711441813401154077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9581057897178169069744205 3592896711441813401154077)
                  ·
                    refine ⟨1347336266790680025432779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592896711441813401154077 1347336266790680025432779)
                    ·
                      rfl

theorem cell22_3935892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3935892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935892 prefixEnd_3935892 := by exact prefixLift 3935892
  have htrace : WordTrace (prefixWord ++ tailWord_3935892) baseStart_3935892 baseEnd_3935892 := by
    simpa [prefixWord, tailWord_3935892, baseEnd_3935892] using wordTrace_append hprefix tailTrace_3935892
  have hstable : (prefixWord ++ tailWord_3935892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935892).length < 2 ^ (prefixWord ++ tailWord_3935892).sum := by decide
  have hdescent : baseEnd_3935892 < baseStart_3935892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935905 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 5]
def baseStart_3935905 : Nat := 118140960795 + 3935905 * 2 ^ 59
def prefixEnd_3935905 : Nat := 4983230072969 + 3 ^ 40 * 3935905 * 2
def baseEnd_3935905 : Nat := 449113572318784108285913

theorem tailTrace_3935905 : CollatzResearch.WordTrace tailWord_3935905 prefixEnd_3935905 449113572318784108285913 := by
  unfold tailWord_3935905
  simp only [CollatzResearch.WordTrace]
  refine ⟨143554248805895858902609169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95702832537263905935072779 143554248805895858902609169)
  ·
    refine ⟨107665686604421894176956877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143554248805895858902609169 107665686604421894176956877)
    ·
      refine ⟨40374632476658210316358829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107665686604421894176956877 40374632476658210316358829)
      ·
        refine ⟨15140487178746828868634561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40374632476658210316358829 15140487178746828868634561)
        ·
          refine ⟨11355365384060121651475921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15140487178746828868634561 11355365384060121651475921)
          ·
            refine ⟨8516524038045091238606941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11355365384060121651475921 8516524038045091238606941)
            ·
              refine ⟨3193696514266909214477603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8516524038045091238606941 3193696514266909214477603)
              ·
                refine ⟨4790544771400363821716405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193696514266909214477603 4790544771400363821716405)
                ·
                  refine ⟨449113572318784108285913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4790544771400363821716405 449113572318784108285913)
                  ·
                    rfl

theorem cell22_3935905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 5].length) (baseStart_3935905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935905 prefixEnd_3935905 := by exact prefixLift 3935905
  have htrace : WordTrace (prefixWord ++ tailWord_3935905) baseStart_3935905 baseEnd_3935905 := by
    simpa [prefixWord, tailWord_3935905, baseEnd_3935905] using wordTrace_append hprefix tailTrace_3935905
  have hstable : (prefixWord ++ tailWord_3935905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935905).length < 2 ^ (prefixWord ++ tailWord_3935905).sum := by decide
  have hdescent : baseEnd_3935905 < baseStart_3935905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935926 : List Nat := [5, 1, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3935926 : Nat := 118140960795 + 3935926 * 2 ^ 59
def prefixEnd_3935926 : Nat := 4983230072969 + 3 ^ 40 * 3935926 * 2
def baseEnd_3935926 : Nat := 1347347905685515270082675

theorem tailTrace_3935926 : CollatzResearch.WordTrace tailWord_3935926 prefixEnd_3935926 1347347905685515270082675 := by
  unfold tailWord_3935926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8972188421176236218070227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95703343159213186326082421 8972188421176236218070227)
  ·
    refine ⟨13458282631764354327105341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8972188421176236218070227 13458282631764354327105341)
    ·
      refine ⟨5046855986911632872664503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13458282631764354327105341 5046855986911632872664503)
      ·
        refine ⟨7570283980367449308996755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5046855986911632872664503 7570283980367449308996755)
        ·
          refine ⟨11355425970551173963495133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7570283980367449308996755 11355425970551173963495133)
          ·
            refine ⟨4258284738956690236310675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11355425970551173963495133 4258284738956690236310675)
            ·
              refine ⟨6387427108435035354466013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258284738956690236310675 6387427108435035354466013)
              ·
                refine ⟨2395285165663138257924755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6387427108435035354466013 2395285165663138257924755)
                ·
                  refine ⟨3592927748494707386887133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395285165663138257924755 3592927748494707386887133)
                  ·
                    refine ⟨1347347905685515270082675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592927748494707386887133 1347347905685515270082675)
                    ·
                      rfl

theorem cell22_3935926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3935926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935926 prefixEnd_3935926 := by exact prefixLift 3935926
  have htrace : WordTrace (prefixWord ++ tailWord_3935926) baseStart_3935926 baseEnd_3935926 := by
    simpa [prefixWord, tailWord_3935926, baseEnd_3935926] using wordTrace_append hprefix tailTrace_3935926
  have hstable : (prefixWord ++ tailWord_3935926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935926).length < 2 ^ (prefixWord ++ tailWord_3935926).sum := by decide
  have hdescent : baseEnd_3935926 < baseStart_3935926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935931 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 1, 5]
def baseStart_3935931 : Nat := 118140960795 + 3935931 * 2 ^ 59
def prefixEnd_3935931 : Nat := 4983230072969 + 3 ^ 40 * 3935931 * 2
def baseEnd_3935931 : Nat := 1347349617287696923707659

theorem tailTrace_3935931 : CollatzResearch.WordTrace tailWord_3935931 prefixEnd_3935931 1347349617287696923707659 := by
  unfold tailWord_3935931
  simp only [CollatzResearch.WordTrace]
  refine ⟨143555197103801665343055647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95703464735867776895370431 143555197103801665343055647)
  ·
    refine ⟨215332795655702498014583471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143555197103801665343055647 215332795655702498014583471)
    ·
      refine ⟨322999193483553747021875207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215332795655702498014583471 322999193483553747021875207)
      ·
        refine ⟨484498790225330620532812811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322999193483553747021875207 484498790225330620532812811)
        ·
          refine ⟨726748185337995930799219217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484498790225330620532812811 726748185337995930799219217)
          ·
            refine ⟨545061139003496948099414413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726748185337995930799219217 545061139003496948099414413)
            ·
              refine ⟨204397927126311355537280405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545061139003496948099414413 204397927126311355537280405)
              ·
                refine ⟨9581152834045844790810019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204397927126311355537280405 9581152834045844790810019)
                ·
                  refine ⟨14371729251068767186215029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9581152834045844790810019 14371729251068767186215029)
                  ·
                    refine ⟨1347349617287696923707659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14371729251068767186215029 1347349617287696923707659)
                    ·
                      rfl

theorem cell22_3935931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 5].length) (baseStart_3935931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935931 prefixEnd_3935931 := by exact prefixLift 3935931
  have htrace : WordTrace (prefixWord ++ tailWord_3935931) baseStart_3935931 baseEnd_3935931 := by
    simpa [prefixWord, tailWord_3935931, baseEnd_3935931] using wordTrace_append hprefix tailTrace_3935931
  have hstable : (prefixWord ++ tailWord_3935931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935931).length < 2 ^ (prefixWord ++ tailWord_3935931).sum := by decide
  have hdescent : baseEnd_3935931 < baseStart_3935931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3935961 : List Nat := [1, 2, 1, 2, 3, 3, 1, 9]
def baseStart_3935961 : Nat := 118140960795 + 3935961 * 2 ^ 59
def prefixEnd_3935961 : Nat := 4983230072969 + 3 ^ 40 * 3935961 * 2
def baseEnd_3935961 : Nat := 149706654100087427273063

theorem tailTrace_3935961 : CollatzResearch.WordTrace tailWord_3935961 prefixEnd_3935961 149706654100087427273063 := by
  unfold tailWord_3935961
  simp only [CollatzResearch.WordTrace]
  refine ⟨143556291293692980466647737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95704194195795320311098491 143556291293692980466647737)
  ·
    refine ⟨107667218470269735349985803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143556291293692980466647737 107667218470269735349985803)
    ·
      refine ⟨161500827705404603024978705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107667218470269735349985803 161500827705404603024978705)
      ·
        refine ⟨121125620779053452268734029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161500827705404603024978705 121125620779053452268734029)
        ·
          refine ⟨45422107792145044600775261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121125620779053452268734029 45422107792145044600775261)
          ·
            refine ⟨17033290422054391725290723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45422107792145044600775261 17033290422054391725290723)
            ·
              refine ⟨25549935633081587587936085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17033290422054391725290723 25549935633081587587936085)
              ·
                refine ⟨149706654100087427273063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25549935633081587587936085 149706654100087427273063)
                ·
                  rfl

theorem cell22_3935961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 9].length) (baseStart_3935961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3935961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3935961 prefixEnd_3935961 := by exact prefixLift 3935961
  have htrace : WordTrace (prefixWord ++ tailWord_3935961) baseStart_3935961 baseEnd_3935961 := by
    simpa [prefixWord, tailWord_3935961, baseEnd_3935961] using wordTrace_append hprefix tailTrace_3935961
  have hstable : (prefixWord ++ tailWord_3935961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3935961).length < 2 ^ (prefixWord ++ tailWord_3935961).sum := by decide
  have hdescent : baseEnd_3935961 < baseStart_3935961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3935961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936087 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 1, 4]
def baseStart_3936087 : Nat := 118140960795 + 3936087 * 2 ^ 59
def prefixEnd_3936087 : Nat := 4983230072969 + 3 ^ 40 * 3936087 * 2
def baseEnd_3936087 : Nat := 1347403019275764516807181

theorem tailTrace_3936087 : CollatzResearch.WordTrace tailWord_3936087 prefixEnd_3936087 1347403019275764516807181 := by
  unfold tailWord_3936087
  simp only [CollatzResearch.WordTrace]
  refine ⟨143560886891236503985734515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95707257927491002657156343 143560886891236503985734515)
  ·
    refine ⟨215341330336854755978601773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143560886891236503985734515 215341330336854755978601773)
    ·
      refine ⟨80752998876320533491975665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215341330336854755978601773 80752998876320533491975665)
      ·
        refine ⟨60564749157240400118981749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80752998876320533491975665 60564749157240400118981749)
        ·
          refine ⟨5677945233491287511154539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60564749157240400118981749 5677945233491287511154539)
          ·
            refine ⟨8516917850236931266731809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677945233491287511154539 8516917850236931266731809)
            ·
              refine ⟨6387688387677698450048857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8516917850236931266731809 6387688387677698450048857)
              ·
                refine ⟨4790766290758273837536643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6387688387677698450048857 4790766290758273837536643)
                ·
                  refine ⟨7186149436137410756304965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790766290758273837536643 7186149436137410756304965)
                  ·
                    refine ⟨1347403019275764516807181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7186149436137410756304965 1347403019275764516807181)
                    ·
                      rfl

theorem cell22_3936087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_3936087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936087 prefixEnd_3936087 := by exact prefixLift 3936087
  have htrace : WordTrace (prefixWord ++ tailWord_3936087) baseStart_3936087 baseEnd_3936087 := by
    simpa [prefixWord, tailWord_3936087, baseEnd_3936087] using wordTrace_append hprefix tailTrace_3936087
  have hstable : (prefixWord ++ tailWord_3936087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936087).length < 2 ^ (prefixWord ++ tailWord_3936087).sum := by decide
  have hdescent : baseEnd_3936087 < baseStart_3936087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936117 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3936117 : Nat := 118140960795 + 3936117 * 2 ^ 59
def prefixEnd_3936117 : Nat := 4983230072969 + 3 ^ 40 * 3936117 * 2
def baseEnd_3936117 : Nat := 1347413288888854438557089

theorem tailTrace_3936117 : CollatzResearch.WordTrace tailWord_3936117 prefixEnd_3936117 1347413288888854438557089 := by
  unfold tailWord_3936117
  simp only [CollatzResearch.WordTrace]
  refine ⟨143561981081127819109326605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95707987387418546072884403 143561981081127819109326605)
  ·
    refine ⟨53835742905422932165997477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143561981081127819109326605 53835742905422932165997477)
    ·
      refine ⟨10094201794766799781124527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53835742905422932165997477 10094201794766799781124527)
      ·
        refine ⟨15141302692150199671686791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10094201794766799781124527 15141302692150199671686791)
        ·
          refine ⟨22711954038225299507530187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15141302692150199671686791 22711954038225299507530187)
          ·
            refine ⟨34067931057337949261295281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22711954038225299507530187 34067931057337949261295281)
            ·
              refine ⟨25550948293003461945971461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34067931057337949261295281 25550948293003461945971461)
              ·
                refine ⟨4790802804938149114869649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25550948293003461945971461 4790802804938149114869649)
                ·
                  refine ⟨3593102103703611836152237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4790802804938149114869649 3593102103703611836152237)
                  ·
                    refine ⟨1347413288888854438557089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593102103703611836152237 1347413288888854438557089)
                    ·
                      rfl

theorem cell22_3936117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3936117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936117 prefixEnd_3936117 := by exact prefixLift 3936117
  have htrace : WordTrace (prefixWord ++ tailWord_3936117) baseStart_3936117 baseEnd_3936117 := by
    simpa [prefixWord, tailWord_3936117, baseEnd_3936117] using wordTrace_append hprefix tailTrace_3936117
  have hstable : (prefixWord ++ tailWord_3936117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936117).length < 2 ^ (prefixWord ++ tailWord_3936117).sum := by decide
  have hdescent : baseEnd_3936117 < baseStart_3936117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936145 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 3, 3]
def baseStart_3936145 : Nat := 118140960795 + 3936145 * 2 ^ 59
def prefixEnd_3936145 : Nat := 4983230072969 + 3 ^ 40 * 3936145 * 2
def baseEnd_3936145 : Nat := 1347422873861071698857003

theorem tailTrace_3936145 : CollatzResearch.WordTrace tailWord_3936145 prefixEnd_3936145 1347422873861071698857003 := by
  unfold tailWord_3936145
  simp only [CollatzResearch.WordTrace]
  refine ⟨143563002325026379891345889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95708668216684253260897259 143563002325026379891345889)
  ·
    refine ⟨107672251743769784918509417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143563002325026379891345889 107672251743769784918509417)
    ·
      refine ⟨80754188807827338688882063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107672251743769784918509417 80754188807827338688882063)
      ·
        refine ⟨121131283211741008033323095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80754188807827338688882063 121131283211741008033323095)
        ·
          refine ⟨181696924817611512049984643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121131283211741008033323095 181696924817611512049984643)
          ·
            refine ⟨272545387226417268074976965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181696924817611512049984643 272545387226417268074976965)
            ·
              refine ⟨51102260104953237764058181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272545387226417268074976965 51102260104953237764058181)
              ·
                refine ⟨9581673769678732080760909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51102260104953237764058181 9581673769678732080760909)
                ·
                  refine ⟨3593127663629524530285341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9581673769678732080760909 3593127663629524530285341)
                  ·
                    refine ⟨1347422873861071698857003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593127663629524530285341 1347422873861071698857003)
                    ·
                      rfl

theorem cell22_3936145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_3936145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936145 prefixEnd_3936145 := by exact prefixLift 3936145
  have htrace : WordTrace (prefixWord ++ tailWord_3936145) baseStart_3936145 baseEnd_3936145 := by
    simpa [prefixWord, tailWord_3936145, baseEnd_3936145] using wordTrace_append hprefix tailTrace_3936145
  have hstable : (prefixWord ++ tailWord_3936145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936145).length < 2 ^ (prefixWord ++ tailWord_3936145).sum := by decide
  have hdescent : baseEnd_3936145 < baseStart_3936145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936175 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 5]
def baseStart_3936175 : Nat := 118140960795 + 3936175 * 2 ^ 59
def prefixEnd_3936175 : Nat := 4983230072969 + 3 ^ 40 * 3936175 * 2
def baseEnd_3936175 : Nat := 449144381158053873535637

theorem tailTrace_3936175 : CollatzResearch.WordTrace tailWord_3936175 prefixEnd_3936175 449144381158053873535637 := by
  unfold tailWord_3936175
  simp only [CollatzResearch.WordTrace]
  refine ⟨143564096514917695014937979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95709397676611796676625319 143564096514917695014937979)
  ·
    refine ⟨215346144772376542522406969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143564096514917695014937979 215346144772376542522406969)
    ·
      refine ⟨161509608579282406891805227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215346144772376542522406969 161509608579282406891805227)
      ·
        refine ⟨242264412868923610337707841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161509608579282406891805227 242264412868923610337707841)
        ·
          refine ⟨181698309651692707753280881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242264412868923610337707841 181698309651692707753280881)
          ·
            refine ⟨136273732238769530814960661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181698309651692707753280881 136273732238769530814960661)
            ·
              refine ⟨6387831198692321756951281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136273732238769530814960661 6387831198692321756951281)
              ·
                refine ⟨4790873399019241317713461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6387831198692321756951281 4790873399019241317713461)
                ·
                  refine ⟨449144381158053873535637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4790873399019241317713461 449144381158053873535637)
                  ·
                    rfl

theorem cell22_3936175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 5].length) (baseStart_3936175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936175 prefixEnd_3936175 := by exact prefixLift 3936175
  have htrace : WordTrace (prefixWord ++ tailWord_3936175) baseStart_3936175 baseEnd_3936175 := by
    simpa [prefixWord, tailWord_3936175, baseEnd_3936175] using wordTrace_append hprefix tailTrace_3936175
  have hstable : (prefixWord ++ tailWord_3936175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936175).length < 2 ^ (prefixWord ++ tailWord_3936175).sum := by decide
  have hdescent : baseEnd_3936175 < baseStart_3936175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936190 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3936190 : Nat := 118140960795 + 3936190 * 2 ^ 59
def prefixEnd_3936190 : Nat := 4983230072969 + 3 ^ 40 * 3936190 * 2
def baseEnd_3936190 : Nat := 1347438278280706581481865

theorem tailTrace_3936190 : CollatzResearch.WordTrace tailWord_3936190 prefixEnd_3936190 1347438278280706581481865 := by
  unfold tailWord_3936190
  simp only [CollatzResearch.WordTrace]
  refine ⟨17945580451232919072091753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95709762406575568384489349 17945580451232919072091753)
  ·
    refine ⟨13459185338424689304068815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17945580451232919072091753 13459185338424689304068815)
    ·
      refine ⟨20188778007637033956103223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13459185338424689304068815 20188778007637033956103223)
      ·
        refine ⟨30283167011455550934154835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20188778007637033956103223 30283167011455550934154835)
        ·
          refine ⟨45424750517183326401232253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30283167011455550934154835 45424750517183326401232253)
          ·
            refine ⟨17034281443943747400462095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45424750517183326401232253 17034281443943747400462095)
            ·
              refine ⟨25551422165915621100693143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17034281443943747400462095 25551422165915621100693143)
              ·
                refine ⟨38327133248873431651039715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25551422165915621100693143 38327133248873431651039715)
                ·
                  refine ⟨57490699873310147476559573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38327133248873431651039715 57490699873310147476559573)
                  ·
                    refine ⟨1347438278280706581481865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57490699873310147476559573 1347438278280706581481865)
                    ·
                      rfl

theorem cell22_3936190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3936190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936190 prefixEnd_3936190 := by exact prefixLift 3936190
  have htrace : WordTrace (prefixWord ++ tailWord_3936190) baseStart_3936190 baseEnd_3936190 := by
    simpa [prefixWord, tailWord_3936190, baseEnd_3936190] using wordTrace_append hprefix tailTrace_3936190
  have hstable : (prefixWord ++ tailWord_3936190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936190).length < 2 ^ (prefixWord ++ tailWord_3936190).sum := by decide
  have hdescent : baseEnd_3936190 < baseStart_3936190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936226 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_3936226 : Nat := 118140960795 + 3936226 * 2 ^ 59
def prefixEnd_3936226 : Nat := 4983230072969 + 3 ^ 40 * 3936226 * 2
def baseEnd_3936226 : Nat := 449150200605471495860585

theorem tailTrace_3936226 : CollatzResearch.WordTrace tailWord_3936226 prefixEnd_3936226 449150200605471495860585 := by
  unfold tailWord_3936226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35891489159433232681261133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95710637758488620483363021 35891489159433232681261133)
  ·
    refine ⟨13459308434787462255472925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35891489159433232681261133 13459308434787462255472925)
    ·
      refine ⟨5047240663045298345802347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13459308434787462255472925 5047240663045298345802347)
      ·
        refine ⟨7570860994567947518703521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5047240663045298345802347 7570860994567947518703521)
        ·
          refine ⟨5678145745925960639027641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7570860994567947518703521 5678145745925960639027641)
          ·
            refine ⟨4258609309444470479270731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5678145745925960639027641 4258609309444470479270731)
            ·
              refine ⟨6387913964166705718906097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258609309444470479270731 6387913964166705718906097)
              ·
                refine ⟨4790935473125029289179573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6387913964166705718906097 4790935473125029289179573)
                ·
                  refine ⟨449150200605471495860585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4790935473125029289179573 449150200605471495860585)
                  ·
                    rfl

theorem cell22_3936226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_3936226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936226 prefixEnd_3936226 := by exact prefixLift 3936226
  have htrace : WordTrace (prefixWord ++ tailWord_3936226) baseStart_3936226 baseEnd_3936226 := by
    simpa [prefixWord, tailWord_3936226, baseEnd_3936226] using wordTrace_append hprefix tailTrace_3936226
  have hstable : (prefixWord ++ tailWord_3936226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936226).length < 2 ^ (prefixWord ++ tailWord_3936226).sum := by decide
  have hdescent : baseEnd_3936226 < baseStart_3936226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936325 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_3936325 : Nat := 118140960795 + 3936325 * 2 ^ 59
def prefixEnd_3936325 : Nat := 4983230072969 + 3 ^ 40 * 3936325 * 2
def baseEnd_3936325 : Nat := 1347484491539611229356451

theorem tailTrace_3936325 : CollatzResearch.WordTrace tailWord_3936325 prefixEnd_3936325 1347484491539611229356451 := by
  unfold tailWord_3936325
  simp only [CollatzResearch.WordTrace]
  refine ⟨143569567464374270632898429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95713044976249513755265619 143569567464374270632898429)
  ·
    refine ⟨53838587799140351487336911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143569567464374270632898429 53838587799140351487336911)
    ·
      refine ⟨80757881698710527231005367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53838587799140351487336911 80757881698710527231005367)
      ·
        refine ⟨121136822548065790846508051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80757881698710527231005367 121136822548065790846508051)
        ·
          refine ⟨181705233822098686269762077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121136822548065790846508051 181705233822098686269762077)
          ·
            refine ⟨68139462683287007351160779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181705233822098686269762077 68139462683287007351160779)
            ·
              refine ⟨102209194024930511026741169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68139462683287007351160779 102209194024930511026741169)
              ·
                refine ⟨76656895518697883270055877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102209194024930511026741169 76656895518697883270055877)
                ·
                  refine ⟨14373167909755853113135477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76656895518697883270055877 14373167909755853113135477)
                  ·
                    refine ⟨1347484491539611229356451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14373167909755853113135477 1347484491539611229356451)
                    ·
                      rfl

theorem cell22_3936325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_3936325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936325 prefixEnd_3936325 := by exact prefixLift 3936325
  have htrace : WordTrace (prefixWord ++ tailWord_3936325) baseStart_3936325 baseEnd_3936325 := by
    simpa [prefixWord, tailWord_3936325, baseEnd_3936325] using wordTrace_append hprefix tailTrace_3936325
  have hstable : (prefixWord ++ tailWord_3936325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936325).length < 2 ^ (prefixWord ++ tailWord_3936325).sum := by decide
  have hdescent : baseEnd_3936325 < baseStart_3936325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936348 : List Nat := [2, 2, 4, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3936348 : Nat := 118140960795 + 3936348 * 2 ^ 59
def prefixEnd_3936348 : Nat := 4983230072969 + 3 ^ 40 * 3936348 * 2
def baseEnd_3936348 : Nat := 1347492364909646836031381

theorem tailTrace_3936348 : CollatzResearch.WordTrace tailWord_3936348 prefixEnd_3936348 1347492364909646836031381 := by
  unfold tailWord_3936348
  simp only [CollatzResearch.WordTrace]
  refine ⟨71785203171645472780492849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95713604228860630373990465 71785203171645472780492849)
  ·
    refine ⟨53838902378734104585369637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71785203171645472780492849 53838902378734104585369637)
    ·
      refine ⟨10094794196012644609756807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53838902378734104585369637 10094794196012644609756807)
      ·
        refine ⟨15142191294018966914635211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10094794196012644609756807 15142191294018966914635211)
        ·
          refine ⟨22713286941028450371952817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15142191294018966914635211 22713286941028450371952817)
          ·
            refine ⟨17034965205771337778964613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22713286941028450371952817 17034965205771337778964613)
            ·
              refine ⟨3194055976082125833555865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17034965205771337778964613 3194055976082125833555865)
              ·
                refine ⟨2395541982061594375166899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3194055976082125833555865 2395541982061594375166899)
                ·
                  refine ⟨3593312973092391562750349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395541982061594375166899 3593312973092391562750349)
                  ·
                    refine ⟨1347492364909646836031381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593312973092391562750349 1347492364909646836031381)
                    ·
                      rfl

theorem cell22_3936348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3936348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936348 prefixEnd_3936348 := by exact prefixLift 3936348
  have htrace : WordTrace (prefixWord ++ tailWord_3936348) baseStart_3936348 baseEnd_3936348 := by
    simpa [prefixWord, tailWord_3936348, baseEnd_3936348] using wordTrace_append hprefix tailTrace_3936348
  have hstable : (prefixWord ++ tailWord_3936348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936348).length < 2 ^ (prefixWord ++ tailWord_3936348).sum := by decide
  have hdescent : baseEnd_3936348 < baseStart_3936348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936357 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_3936357 : Nat := 118140960795 + 3936357 * 2 ^ 59
def prefixEnd_3936357 : Nat := 4983230072969 + 3 ^ 40 * 3936357 * 2
def baseEnd_3936357 : Nat := 1347495445793573812556353

theorem tailTrace_3936357 : CollatzResearch.WordTrace tailWord_3936357 prefixEnd_3936357 1347495445793573812556353 := by
  unfold tailWord_3936357
  simp only [CollatzResearch.WordTrace]
  refine ⟨143570734600258340098063325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95713823066838893398708883 143570734600258340098063325)
  ·
    refine ⟨53839025475096877536773747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143570734600258340098063325 53839025475096877536773747)
    ·
      refine ⟨80758538212645316305160621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53839025475096877536773747 80758538212645316305160621)
      ·
        refine ⟨30284451829741993614435233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80758538212645316305160621 30284451829741993614435233)
        ·
          refine ⟨22713338872306495210826425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30284451829741993614435233 22713338872306495210826425)
          ·
            refine ⟨17035004154229871408119819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22713338872306495210826425 17035004154229871408119819)
            ·
              refine ⟨25552506231344807112179729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17035004154229871408119819 25552506231344807112179729)
              ·
                refine ⟨19164379673508605334134797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25552506231344807112179729 19164379673508605334134797)
                ·
                  refine ⟨7186642377565727000300549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19164379673508605334134797 7186642377565727000300549)
                  ·
                    refine ⟨1347495445793573812556353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7186642377565727000300549 1347495445793573812556353)
                    ·
                      rfl

theorem cell22_3936357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_3936357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936357 prefixEnd_3936357 := by exact prefixLift 3936357
  have htrace : WordTrace (prefixWord ++ tailWord_3936357) baseStart_3936357 baseEnd_3936357 := by
    simpa [prefixWord, tailWord_3936357, baseEnd_3936357] using wordTrace_append hprefix tailTrace_3936357
  have hstable : (prefixWord ++ tailWord_3936357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936357).length < 2 ^ (prefixWord ++ tailWord_3936357).sum := by decide
  have hdescent : baseEnd_3936357 < baseStart_3936357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936374 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3936374 : Nat := 118140960795 + 3936374 * 2 ^ 59
def prefixEnd_3936374 : Nat := 4983230072969 + 3 ^ 40 * 3936374 * 2
def baseEnd_3936374 : Nat := 1347501265240991434881301

theorem tailTrace_3936374 : CollatzResearch.WordTrace tailWord_3936374 prefixEnd_3936374 1347501265240991434881301 := by
  unfold tailWord_3936374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973209665074797000089511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95714236427464501334288117 8973209665074797000089511)
  ·
    refine ⟨13459814497612195500134267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8973209665074797000089511 13459814497612195500134267)
    ·
      refine ⟨20189721746418293250201401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13459814497612195500134267 20189721746418293250201401)
      ·
        refine ⟨15142291309813719937651051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20189721746418293250201401 15142291309813719937651051)
        ·
          refine ⟨22713436964720579906476577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15142291309813719937651051 22713436964720579906476577)
          ·
            refine ⟨17035077723540434929857433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22713436964720579906476577 17035077723540434929857433)
            ·
              refine ⟨12776308292655326197393075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17035077723540434929857433 12776308292655326197393075)
              ·
                refine ⟨19164462438982989296089613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12776308292655326197393075 19164462438982989296089613)
                ·
                  refine ⟨7186673414618620986033605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19164462438982989296089613 7186673414618620986033605)
                  ·
                    refine ⟨1347501265240991434881301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7186673414618620986033605 1347501265240991434881301)
                    ·
                      rfl

theorem cell22_3936374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3936374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936374 prefixEnd_3936374 := by exact prefixLift 3936374
  have htrace : WordTrace (prefixWord ++ tailWord_3936374) baseStart_3936374 baseEnd_3936374 := by
    simpa [prefixWord, tailWord_3936374, baseEnd_3936374] using wordTrace_append hprefix tailTrace_3936374
  have hstable : (prefixWord ++ tailWord_3936374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936374).length < 2 ^ (prefixWord ++ tailWord_3936374).sum := by decide
  have hdescent : baseEnd_3936374 < baseStart_3936374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936387 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 1, 5]
def baseStart_3936387 : Nat := 118140960795 + 3936387 * 2 ^ 59
def prefixEnd_3936387 : Nat := 4983230072969 + 3 ^ 40 * 3936387 * 2
def baseEnd_3936387 : Nat := 1347505715406663734306261

theorem tailTrace_3936387 : CollatzResearch.WordTrace tailWord_3936387 prefixEnd_3936387 1347505715406663734306261 := by
  unfold tailWord_3936387
  simp only [CollatzResearch.WordTrace]
  refine ⟨143571828790149655221655415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95714552526766436814436943 143571828790149655221655415)
  ·
    refine ⟨215357743185224482832483123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143571828790149655221655415 215357743185224482832483123)
    ·
      refine ⟨323036614777836724248724685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215357743185224482832483123 323036614777836724248724685)
      ·
        refine ⟨121138730541688771593271757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323036614777836724248724685 121138730541688771593271757)
        ·
          refine ⟨45427023953133289347476909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121138730541688771593271757 45427023953133289347476909)
          ·
            refine ⟨17035133982424983505303841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45427023953133289347476909 17035133982424983505303841)
            ·
              refine ⟨12776350486818737628977881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17035133982424983505303841 12776350486818737628977881)
              ·
                refine ⟨9582262865114053221733411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12776350486818737628977881 9582262865114053221733411)
                ·
                  refine ⟨14373394297671079832600117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9582262865114053221733411 14373394297671079832600117)
                  ·
                    refine ⟨1347505715406663734306261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14373394297671079832600117 1347505715406663734306261)
                    ·
                      rfl

theorem cell22_3936387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 5].length) (baseStart_3936387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936387 prefixEnd_3936387 := by exact prefixLift 3936387
  have htrace : WordTrace (prefixWord ++ tailWord_3936387) baseStart_3936387 baseEnd_3936387 := by
    simpa [prefixWord, tailWord_3936387, baseEnd_3936387] using wordTrace_append hprefix tailTrace_3936387
  have hstable : (prefixWord ++ tailWord_3936387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936387).length < 2 ^ (prefixWord ++ tailWord_3936387).sum := by decide
  have hdescent : baseEnd_3936387 < baseStart_3936387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936389 : List Nat := [1, 3, 1, 1, 5, 1, 1, 5, 4]
def baseStart_3936389 : Nat := 118140960795 + 3936389 * 2 ^ 59
def prefixEnd_3936389 : Nat := 4983230072969 + 3 ^ 40 * 3936389 * 2
def baseEnd_3936389 : Nat := 449168800015845465252085

theorem tailTrace_3936389 : CollatzResearch.WordTrace tailWord_3936389 prefixEnd_3936389 449168800015845465252085 := by
  unfold tailWord_3936389
  simp only [CollatzResearch.WordTrace]
  refine ⟨143571901736142409563228221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95714601157428273042152147 143571901736142409563228221)
  ·
    refine ⟨53839463151053403586210583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143571901736142409563228221 53839463151053403586210583)
    ·
      refine ⟨80759194726580105379315875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53839463151053403586210583 80759194726580105379315875)
      ·
        refine ⟨121138792089870158068973813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80759194726580105379315875 121138792089870158068973813)
        ·
          refine ⟨11356761758425327318966295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121138792089870158068973813 11356761758425327318966295)
          ·
            refine ⟨17035142637637990978449443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11356761758425327318966295 17035142637637990978449443)
            ·
              refine ⟨25552713956456986467674165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17035142637637990978449443 25552713956456986467674165)
              ·
                refine ⟨2395566933417842481344453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25552713956456986467674165 2395566933417842481344453)
                ·
                  refine ⟨449168800015845465252085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2395566933417842481344453 449168800015845465252085)
                  ·
                    rfl

theorem cell22_3936389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_3936389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936389 prefixEnd_3936389 := by exact prefixLift 3936389
  have htrace : WordTrace (prefixWord ++ tailWord_3936389) baseStart_3936389 baseEnd_3936389 := by
    simpa [prefixWord, tailWord_3936389, baseEnd_3936389] using wordTrace_append hprefix tailTrace_3936389
  have hstable : (prefixWord ++ tailWord_3936389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936389).length < 2 ^ (prefixWord ++ tailWord_3936389).sum := by decide
  have hdescent : baseEnd_3936389 < baseStart_3936389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936400 : List Nat := [2, 1, 1, 1, 1, 1, 15]
def baseStart_3936400 : Nat := 118140960795 + 3936400 * 2 ^ 59
def prefixEnd_3936400 : Nat := 4983230072969 + 3 ^ 40 * 3936400 * 2
def baseEnd_3936400 : Nat := 49907783910086519767823

theorem tailTrace_3936400 : CollatzResearch.WordTrace tailWord_3936400 prefixEnd_3936400 49907783910086519767823 := by
  unfold tailWord_3936400
  simp only [CollatzResearch.WordTrace]
  refine ⟨71786151469551279220939327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95714868626068372294585769 71786151469551279220939327)
  ·
    refine ⟨107679227204326918831408991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71786151469551279220939327 107679227204326918831408991)
    ·
      refine ⟨161518840806490378247113487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107679227204326918831408991 161518840806490378247113487)
      ·
        refine ⟨242278261209735567370670231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161518840806490378247113487 242278261209735567370670231)
        ·
          refine ⟨363417391814603351056005347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242278261209735567370670231 363417391814603351056005347)
          ·
            refine ⟨545126087721905026584008021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363417391814603351056005347 545126087721905026584008021)
            ·
              refine ⟨49907783910086519767823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 545126087721905026584008021 49907783910086519767823)
              ·
                rfl

theorem cell22_3936400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 15].length) (baseStart_3936400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936400 prefixEnd_3936400 := by exact prefixLift 3936400
  have htrace : WordTrace (prefixWord ++ tailWord_3936400) baseStart_3936400 baseEnd_3936400 := by
    simpa [prefixWord, tailWord_3936400, baseEnd_3936400] using wordTrace_append hprefix tailTrace_3936400
  have hstable : (prefixWord ++ tailWord_3936400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936400).length < 2 ^ (prefixWord ++ tailWord_3936400).sum := by decide
  have hdescent : baseEnd_3936400 < baseStart_3936400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936421 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 2, 3]
def baseStart_3936421 : Nat := 118140960795 + 3936421 * 2 ^ 59
def prefixEnd_3936421 : Nat := 4983230072969 + 3 ^ 40 * 3936421 * 2
def baseEnd_3936421 : Nat := 1347517354301498978956157

theorem tailTrace_3936421 : CollatzResearch.WordTrace tailWord_3936421 prefixEnd_3936421 1347517354301498978956157 := by
  unfold tailWord_3936421
  simp only [CollatzResearch.WordTrace]
  refine ⟨143573068872026479028393117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95715379248017652685595411 143573068872026479028393117)
  ·
    refine ⟨53839900827009929635647419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143573068872026479028393117 53839900827009929635647419)
    ·
      refine ⟨80759851240514894453471129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53839900827009929635647419 80759851240514894453471129)
      ·
        refine ⟨60569888430386170840103347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80759851240514894453471129 60569888430386170840103347)
        ·
          refine ⟨90854832645579256260155021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60569888430386170840103347 90854832645579256260155021)
          ·
            refine ⟨34070562242092221097558133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90854832645579256260155021 34070562242092221097558133)
            ·
              refine ⟨3194115210196145727896075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34070562242092221097558133 3194115210196145727896075)
              ·
                refine ⟨4791172815294218591844113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194115210196145727896075 4791172815294218591844113)
                ·
                  refine ⟨3593379611470663943883085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4791172815294218591844113 3593379611470663943883085)
                  ·
                    refine ⟨1347517354301498978956157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593379611470663943883085 1347517354301498978956157)
                    ·
                      rfl

theorem cell22_3936421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_3936421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936421 prefixEnd_3936421 := by exact prefixLift 3936421
  have htrace : WordTrace (prefixWord ++ tailWord_3936421) baseStart_3936421 baseEnd_3936421 := by
    simpa [prefixWord, tailWord_3936421, baseEnd_3936421] using wordTrace_append hprefix tailTrace_3936421
  have hstable : (prefixWord ++ tailWord_3936421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936421).length < 2 ^ (prefixWord ++ tailWord_3936421).sum := by decide
  have hdescent : baseEnd_3936421 < baseStart_3936421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936466 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_3936466 : Nat := 118140960795 + 3936466 * 2 ^ 59
def prefixEnd_3936466 : Nat := 4983230072969 + 3 ^ 40 * 3936466 * 2
def baseEnd_3936466 : Nat := 1347532758721133861581019

theorem tailTrace_3936466 : CollatzResearch.WordTrace tailWord_3936466 prefixEnd_3936466 1347532758721133861581019 := by
  unfold tailWord_3936466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35893677539215862928445313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95716473437908967809187501 35893677539215862928445313)
  ·
    refine ⟨26920258154411897196333985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35893677539215862928445313 26920258154411897196333985)
    ·
      refine ⟨20190193615808922897250489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26920258154411897196333985 20190193615808922897250489)
      ·
        refine ⟨15142645211856692172937867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20190193615808922897250489 15142645211856692172937867)
        ·
          refine ⟨22713967817785038259406801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15142645211856692172937867 22713967817785038259406801)
          ·
            refine ⟨17035475863338778694555101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22713967817785038259406801 17035475863338778694555101)
            ·
              refine ⟨6388303448752042010458163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17035475863338778694555101 6388303448752042010458163)
              ·
                refine ⟨9582455173128063015687245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388303448752042010458163 9582455173128063015687245)
                ·
                  refine ⟨3593420689923023630882717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9582455173128063015687245 3593420689923023630882717)
                  ·
                    refine ⟨1347532758721133861581019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593420689923023630882717 1347532758721133861581019)
                    ·
                      rfl

theorem cell22_3936466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_3936466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936466 prefixEnd_3936466 := by exact prefixLift 3936466
  have htrace : WordTrace (prefixWord ++ tailWord_3936466) baseStart_3936466 baseEnd_3936466 := by
    simpa [prefixWord, tailWord_3936466, baseEnd_3936466] using wordTrace_append hprefix tailTrace_3936466
  have hstable : (prefixWord ++ tailWord_3936466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936466).length < 2 ^ (prefixWord ++ tailWord_3936466).sum := by decide
  have hdescent : baseEnd_3936466 < baseStart_3936466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936509 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_3936509 : Nat := 118140960795 + 3936509 * 2 ^ 59
def prefixEnd_3936509 : Nat := 4983230072969 + 3 ^ 40 * 3936509 * 2
def baseEnd_3936509 : Nat := 1347547478499896082755887

theorem tailTrace_3936509 : CollatzResearch.WordTrace tailWord_3936509 prefixEnd_3936509 1347547478499896082755887 := by
  unfold tailWord_3936509
  simp only [CollatzResearch.WordTrace]
  refine ⟨143576278495707670057596581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95717518997138446705064387 143576278495707670057596581)
  ·
    refine ⟨26920552217945188135799359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143576278495707670057596581 26920552217945188135799359)
    ·
      refine ⟨40380828326917782203699039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26920552217945188135799359 40380828326917782203699039)
      ·
        refine ⟨60571242490376673305548559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40380828326917782203699039 60571242490376673305548559)
        ·
          refine ⟨90856863735565009958322839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60571242490376673305548559 90856863735565009958322839)
          ·
            refine ⟨136285295603347514937484259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90856863735565009958322839 136285295603347514937484259)
            ·
              refine ⟨204427943405021272406226389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136285295603347514937484259 204427943405021272406226389)
              ·
                refine ⟨4791279923555186072020931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 204427943405021272406226389 4791279923555186072020931)
                ·
                  refine ⟨7186919885332779108031397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791279923555186072020931 7186919885332779108031397)
                  ·
                    refine ⟨1347547478499896082755887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7186919885332779108031397 1347547478499896082755887)
                    ·
                      rfl

theorem cell22_3936509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_3936509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936509 prefixEnd_3936509 := by exact prefixLift 3936509
  have htrace : WordTrace (prefixWord ++ tailWord_3936509) baseStart_3936509 baseEnd_3936509 := by
    simpa [prefixWord, tailWord_3936509, baseEnd_3936509] using wordTrace_append hprefix tailTrace_3936509
  have hstable : (prefixWord ++ tailWord_3936509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936509).length < 2 ^ (prefixWord ++ tailWord_3936509).sum := by decide
  have hdescent : baseEnd_3936509 < baseStart_3936509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936541 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 6]
def baseStart_3936541 : Nat := 118140960795 + 3936541 * 2 ^ 59
def prefixEnd_3936541 : Nat := 4983230072969 + 3 ^ 40 * 3936541 * 2
def baseEnd_3936541 : Nat := 449186144251286221985263

theorem tailTrace_3936541 : CollatzResearch.WordTrace tailWord_3936541 prefixEnd_3936541 449186144251286221985263 := by
  unfold tailWord_3936541
  simp only [CollatzResearch.WordTrace]
  refine ⟨143577445631591739522761477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95718297087727826348507651 143577445631591739522761477)
  ·
    refine ⟨26920771055923451160517777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143577445631591739522761477 26920771055923451160517777)
    ·
      refine ⟨20190578291942588370388333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26920771055923451160517777 20190578291942588370388333)
      ·
        refine ⟨7571466859478470638895625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20190578291942588370388333 7571466859478470638895625)
        ·
          refine ⟨5678600144608852979171719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7571466859478470638895625 5678600144608852979171719)
          ·
            refine ⟨8517900216913279468757579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678600144608852979171719 8517900216913279468757579)
            ·
              refine ⟨12776850325369919203136369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8517900216913279468757579 12776850325369919203136369)
              ·
                refine ⟨9582637744027439402352277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12776850325369919203136369 9582637744027439402352277)
                ·
                  refine ⟨449186144251286221985263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9582637744027439402352277 449186144251286221985263)
                  ·
                    rfl

theorem cell22_3936541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_3936541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936541 prefixEnd_3936541 := by exact prefixLift 3936541
  have htrace : WordTrace (prefixWord ++ tailWord_3936541) baseStart_3936541 baseEnd_3936541 := by
    simpa [prefixWord, tailWord_3936541, baseEnd_3936541] using wordTrace_append hprefix tailTrace_3936541
  have hstable : (prefixWord ++ tailWord_3936541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936541).length < 2 ^ (prefixWord ++ tailWord_3936541).sum := by decide
  have hdescent : baseEnd_3936541 < baseStart_3936541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936567 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 1, 9]
def baseStart_3936567 : Nat := 118140960795 + 3936567 * 2 ^ 59
def prefixEnd_3936567 : Nat := 4983230072969 + 3 ^ 40 * 3936567 * 2
def baseEnd_3936567 : Nat := 1347567333085203264805709

theorem tailTrace_3936567 : CollatzResearch.WordTrace tailWord_3936567 prefixEnd_3936567 1347567333085203264805709 := by
  unfold tailWord_3936567
  simp only [CollatzResearch.WordTrace]
  refine ⟨143578393929497545963207955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95718929286331697308805303 143578393929497545963207955)
  ·
    refine ⟨215367590894246318944811933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143578393929497545963207955 215367590894246318944811933)
    ·
      refine ⟨80762846585342369604304475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215367590894246318944811933 80762846585342369604304475)
      ·
        refine ⟨121144269878013554406456713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80762846585342369604304475 121144269878013554406456713)
        ·
          refine ⟨90858202408510165804842535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121144269878013554406456713 90858202408510165804842535)
          ·
            refine ⟨136287303612765248707263803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90858202408510165804842535 136287303612765248707263803)
            ·
              refine ⟨204430955419147873060895705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136287303612765248707263803 204430955419147873060895705)
              ·
                refine ⟨153323216564360904795671779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204430955419147873060895705 153323216564360904795671779)
                ·
                  refine ⟨229984824846541357193507669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153323216564360904795671779 229984824846541357193507669)
                  ·
                    refine ⟨1347567333085203264805709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 229984824846541357193507669 1347567333085203264805709)
                    ·
                      rfl

theorem cell22_3936567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_3936567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936567 prefixEnd_3936567 := by exact prefixLift 3936567
  have htrace : WordTrace (prefixWord ++ tailWord_3936567) baseStart_3936567 baseEnd_3936567 := by
    simpa [prefixWord, tailWord_3936567, baseEnd_3936567] using wordTrace_append hprefix tailTrace_3936567
  have hstable : (prefixWord ++ tailWord_3936567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936567).length < 2 ^ (prefixWord ++ tailWord_3936567).sum := by decide
  have hdescent : baseEnd_3936567 < baseStart_3936567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936569 : List Nat := [1, 2, 1, 6, 1, 2, 9]
def baseStart_3936569 : Nat := 118140960795 + 3936569 * 2 ^ 59
def prefixEnd_3936569 : Nat := 4983230072969 + 3 ^ 40 * 3936569 * 2
def baseEnd_3936569 : Nat := 49909926582447256527989

theorem tailTrace_3936569 : CollatzResearch.WordTrace tailWord_3936569 prefixEnd_3936569 49909926582447256527989 := by
  unfold tailWord_3936569
  simp only [CollatzResearch.WordTrace]
  refine ⟨143578466875490300304780761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95718977916993533536520507 143578466875490300304780761)
  ·
    refine ⟨107683850156617725228585571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143578466875490300304780761 107683850156617725228585571)
    ·
      refine ⟨161525775234926587842878357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107683850156617725228585571 161525775234926587842878357)
      ·
        refine ⟨7571520714137183805134923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161525775234926587842878357 7571520714137183805134923)
        ·
          refine ⟨11357281071205775707702385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7571520714137183805134923 11357281071205775707702385)
          ·
            refine ⟨8517960803404331780776789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11357281071205775707702385 8517960803404331780776789)
            ·
              refine ⟨49909926582447256527989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8517960803404331780776789 49909926582447256527989)
              ·
                rfl

theorem cell22_3936569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 9].length) (baseStart_3936569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936569 prefixEnd_3936569 := by exact prefixLift 3936569
  have htrace : WordTrace (prefixWord ++ tailWord_3936569) baseStart_3936569 baseEnd_3936569 := by
    simpa [prefixWord, tailWord_3936569, baseEnd_3936569] using wordTrace_append hprefix tailTrace_3936569
  have hstable : (prefixWord ++ tailWord_3936569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936569).length < 2 ^ (prefixWord ++ tailWord_3936569).sum := by decide
  have hdescent : baseEnd_3936569 < baseStart_3936569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936635 : List Nat := [1, 1, 1, 1, 1, 8, 3, 2, 1, 3]
def baseStart_3936635 : Nat := 118140960795 + 3936635 * 2 ^ 59
def prefixEnd_3936635 : Nat := 4983230072969 + 3 ^ 40 * 3936635 * 2
def baseEnd_3936635 : Nat := 1347590610874873754105501

theorem tailTrace_3936635 : CollatzResearch.WordTrace tailWord_3936635 prefixEnd_3936635 1347590610874873754105501 := by
  unfold tailWord_3936635
  simp only [CollatzResearch.WordTrace]
  refine ⟨143580874093251193576683359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95720582728834129051122239 143580874093251193576683359)
  ·
    refine ⟨215371311139876790365025039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143580874093251193576683359 215371311139876790365025039)
    ·
      refine ⟨323056966709815185547537559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215371311139876790365025039 323056966709815185547537559)
      ·
        refine ⟨484585450064722778321306339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323056966709815185547537559 484585450064722778321306339)
        ·
          refine ⟨726878175097084167481959509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484585450064722778321306339 726878175097084167481959509)
          ·
            refine ⟨8518103614418955087679213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 726878175097084167481959509 8518103614418955087679213)
            ·
              refine ⟨3194288855407108157879705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8518103614418955087679213 3194288855407108157879705)
              ·
                refine ⟨2395716641555331118409779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3194288855407108157879705 2395716641555331118409779)
                ·
                  refine ⟨3593574962332996677614669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395716641555331118409779 3593574962332996677614669)
                  ·
                    refine ⟨1347590610874873754105501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593574962332996677614669 1347590610874873754105501)
                    ·
                      rfl

theorem cell22_3936635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 1, 3].length) (baseStart_3936635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936635 prefixEnd_3936635 := by exact prefixLift 3936635
  have htrace : WordTrace (prefixWord ++ tailWord_3936635) baseStart_3936635 baseEnd_3936635 := by
    simpa [prefixWord, tailWord_3936635, baseEnd_3936635] using wordTrace_append hprefix tailTrace_3936635
  have hstable : (prefixWord ++ tailWord_3936635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936635).length < 2 ^ (prefixWord ++ tailWord_3936635).sum := by decide
  have hdescent : baseEnd_3936635 < baseStart_3936635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936682 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_3936682 : Nat := 118140960795 + 3936682 * 2 ^ 59
def prefixEnd_3936682 : Nat := 4983230072969 + 3 ^ 40 * 3936682 * 2
def baseEnd_3936682 : Nat := 449202233311793766060119

theorem tailTrace_3936682 : CollatzResearch.WordTrace tailWord_3936682 prefixEnd_3936682 449202233311793766060119 := by
  unfold tailWord_3936682
  simp only [CollatzResearch.WordTrace]
  refine ⟨35895647081020230150911075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95721725549387280402429533 35895647081020230150911075)
  ·
    refine ⟨53843470621530345226366613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35895647081020230150911075 53843470621530345226366613)
    ·
      refine ⟨2523912685384234932485935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53843470621530345226366613 2523912685384234932485935)
      ·
        refine ⟨3785869028076352398728903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523912685384234932485935 3785869028076352398728903)
        ·
          refine ⟨5678803542114528598093355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3785869028076352398728903 5678803542114528598093355)
          ·
            refine ⟨8518205313171792897140033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678803542114528598093355 8518205313171792897140033)
            ·
              refine ⟨6388653984878844672855025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8518205313171792897140033 6388653984878844672855025)
              ·
                refine ⟨4791490488659133504641269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6388653984878844672855025 4791490488659133504641269)
                ·
                  refine ⟨449202233311793766060119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4791490488659133504641269 449202233311793766060119)
                  ·
                    rfl

theorem cell22_3936682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_3936682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936682 prefixEnd_3936682 := by exact prefixLift 3936682
  have htrace : WordTrace (prefixWord ++ tailWord_3936682) baseStart_3936682 baseEnd_3936682 := by
    simpa [prefixWord, tailWord_3936682, baseEnd_3936682] using wordTrace_append hprefix tailTrace_3936682
  have hstable : (prefixWord ++ tailWord_3936682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936682).length < 2 ^ (prefixWord ++ tailWord_3936682).sum := by decide
  have hdescent : baseEnd_3936682 < baseStart_3936682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936736 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 5, 3]
def baseStart_3936736 : Nat := 118140960795 + 3936736 * 2 ^ 59
def prefixEnd_3936736 : Nat := 4983230072969 + 3 ^ 40 * 3936736 * 2
def baseEnd_3936736 : Nat := 1347625185238943157330191

theorem tailTrace_3936736 : CollatzResearch.WordTrace tailWord_3936736 prefixEnd_3936736 1347625185238943157330191 := by
  unfold tailWord_3936736
  simp only [CollatzResearch.WordTrace]
  refine ⟨71792278932942643913055031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95723038577256858550740041 71792278932942643913055031)
  ·
    refine ⟨107688418399413965869582547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71792278932942643913055031 107688418399413965869582547)
    ·
      refine ⟨161532627599120948804373821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107688418399413965869582547 161532627599120948804373821)
      ·
        refine ⟨60574735349670355801640183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161532627599120948804373821 60574735349670355801640183)
        ·
          refine ⟨90862103024505533702460275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60574735349670355801640183 90862103024505533702460275)
          ·
            refine ⟨136293154536758300553690413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90862103024505533702460275 136293154536758300553690413)
            ·
              refine ⟨51109932951284362707633905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136293154536758300553690413 51109932951284362707633905)
              ·
                refine ⟨38332449713463272030725429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51109932951284362707633905 38332449713463272030725429)
                ·
                  refine ⟨3593667160637181752880509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38332449713463272030725429 3593667160637181752880509)
                  ·
                    refine ⟨1347625185238943157330191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593667160637181752880509 1347625185238943157330191)
                    ·
                      rfl

theorem cell22_3936736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5, 3].length) (baseStart_3936736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936736 prefixEnd_3936736 := by exact prefixLift 3936736
  have htrace : WordTrace (prefixWord ++ tailWord_3936736) baseStart_3936736 baseEnd_3936736 := by
    simpa [prefixWord, tailWord_3936736, baseEnd_3936736] using wordTrace_append hprefix tailTrace_3936736
  have hstable : (prefixWord ++ tailWord_3936736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936736).length < 2 ^ (prefixWord ++ tailWord_3936736).sum := by decide
  have hdescent : baseEnd_3936736 < baseStart_3936736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936753 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 3, 3]
def baseStart_3936753 : Nat := 118140960795 + 3936753 * 2 ^ 59
def prefixEnd_3936753 : Nat := 4983230072969 + 3 ^ 40 * 3936753 * 2
def baseEnd_3936753 : Nat := 1347631004686360779655139

theorem tailTrace_3936753 : CollatzResearch.WordTrace tailWord_3936753 prefixEnd_3936753 1347631004686360779655139 := by
  unfold tailWord_3936753
  simp only [CollatzResearch.WordTrace]
  refine ⟨143585177906823699729478913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95723451937882466486319275 143585177906823699729478913)
  ·
    refine ⟨107688883430117774797109185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143585177906823699729478913 107688883430117774797109185)
    ·
      refine ⟨80766662572588331097831889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107688883430117774797109185 80766662572588331097831889)
      ·
        refine ⟨60574996929441248323373917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80766662572588331097831889 60574996929441248323373917)
        ·
          refine ⟨22715623848540468121265219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60574996929441248323373917 22715623848540468121265219)
          ·
            refine ⟨34073435772810702181897829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22715623848540468121265219 34073435772810702181897829)
            ·
              refine ⟨6388769207402006659105843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34073435772810702181897829 6388769207402006659105843)
              ·
                refine ⟨9583153811103009988658765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388769207402006659105843 9583153811103009988658765)
                ·
                  refine ⟨3593682679163628745747037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9583153811103009988658765 3593682679163628745747037)
                  ·
                    refine ⟨1347631004686360779655139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593682679163628745747037 1347631004686360779655139)
                    ·
                      rfl

theorem cell22_3936753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_3936753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936753 prefixEnd_3936753 := by exact prefixLift 3936753
  have htrace : WordTrace (prefixWord ++ tailWord_3936753) baseStart_3936753 baseEnd_3936753 := by
    simpa [prefixWord, tailWord_3936753, baseEnd_3936753] using wordTrace_append hprefix tailTrace_3936753
  have hstable : (prefixWord ++ tailWord_3936753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936753).length < 2 ^ (prefixWord ++ tailWord_3936753).sum := by decide
  have hdescent : baseEnd_3936753 < baseStart_3936753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936804 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_3936804 : Nat := 118140960795 + 3936804 * 2 ^ 59
def prefixEnd_3936804 : Nat := 4983230072969 + 3 ^ 40 * 3936804 * 2
def baseEnd_3936804 : Nat := 1347648463028613646629983

theorem tailTrace_3936804 : CollatzResearch.WordTrace tailWord_3936804 prefixEnd_3936804 1347648463028613646629983 := by
  unfold tailWord_3936804
  simp only [CollatzResearch.WordTrace]
  refine ⟨71793519014819467719792733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95724692019759290293056977 71793519014819467719792733)
  ·
    refine ⟨26922569630557300394922275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71793519014819467719792733 26922569630557300394922275)
    ·
      refine ⟨40383854445835950592383413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26922569630557300394922275 40383854445835950592383413)
      ·
        refine ⟨3785986354297120368035945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40383854445835950592383413 3785986354297120368035945)
        ·
          refine ⟨2839489765722840276026959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3785986354297120368035945 2839489765722840276026959)
          ·
            refine ⟨4259234648584260414040439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839489765722840276026959 4259234648584260414040439)
            ·
              refine ⟨6388851972876390621060659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4259234648584260414040439 6388851972876390621060659)
              ·
                refine ⟨9583277959314585931590989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388851972876390621060659 9583277959314585931590989)
                ·
                  refine ⟨3593729234742969724346621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9583277959314585931590989 3593729234742969724346621)
                  ·
                    refine ⟨1347648463028613646629983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593729234742969724346621 1347648463028613646629983)
                    ·
                      rfl

theorem cell22_3936804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_3936804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936804 prefixEnd_3936804 := by exact prefixLift 3936804
  have htrace : WordTrace (prefixWord ++ tailWord_3936804) baseStart_3936804 baseEnd_3936804 := by
    simpa [prefixWord, tailWord_3936804, baseEnd_3936804] using wordTrace_append hprefix tailTrace_3936804
  have hstable : (prefixWord ++ tailWord_3936804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936804).length < 2 ^ (prefixWord ++ tailWord_3936804).sum := by decide
  have hdescent : baseEnd_3936804 < baseStart_3936804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936871 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3936871 : Nat := 118140960795 + 3936871 * 2 ^ 59
def prefixEnd_3936871 : Nat := 4983230072969 + 3 ^ 40 * 3936871 * 2
def baseEnd_3936871 : Nat := 1347671398497847805204777

theorem tailTrace_3936871 : CollatzResearch.WordTrace tailWord_3936871 prefixEnd_3936871 1347671398497847805204777 := by
  unfold tailWord_3936871
  simp only [CollatzResearch.WordTrace]
  refine ⟨143589481720396205882274467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95726321146930803921516311 143589481720396205882274467)
  ·
    refine ⟨215384222580594308823411701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143589481720396205882274467 215384222580594308823411701)
    ·
      refine ⟨20192270866930716452194847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215384222580594308823411701 20192270866930716452194847)
      ·
        refine ⟨30288406300396074678292271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20192270866930716452194847 30288406300396074678292271)
        ·
          refine ⟨45432609450594112017438407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30288406300396074678292271 45432609450594112017438407)
          ·
            refine ⟨68148914175891168026157611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45432609450594112017438407 68148914175891168026157611)
            ·
              refine ⟨102223371263836752039236417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68148914175891168026157611 102223371263836752039236417)
              ·
                refine ⟨76667528447877564029427313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102223371263836752039236417 76667528447877564029427313)
                ·
                  refine ⟨57500646335908173022070485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76667528447877564029427313 57500646335908173022070485)
                  ·
                    refine ⟨1347671398497847805204777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57500646335908173022070485 1347671398497847805204777)
                    ·
                      rfl

theorem cell22_3936871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3936871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936871 prefixEnd_3936871 := by exact prefixLift 3936871
  have htrace : WordTrace (prefixWord ++ tailWord_3936871) baseStart_3936871 baseEnd_3936871 := by
    simpa [prefixWord, tailWord_3936871, baseEnd_3936871] using wordTrace_append hprefix tailTrace_3936871
  have hstable : (prefixWord ++ tailWord_3936871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936871).length < 2 ^ (prefixWord ++ tailWord_3936871).sum := by decide
  have hdescent : baseEnd_3936871 < baseStart_3936871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936888 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 3, 3]
def baseStart_3936888 : Nat := 118140960795 + 3936888 * 2 ^ 59
def prefixEnd_3936888 : Nat := 4983230072969 + 3 ^ 40 * 3936888 * 2
def baseEnd_3936888 : Nat := 1347677217945265427529725

theorem tailTrace_3936888 : CollatzResearch.WordTrace tailWord_3936888 prefixEnd_3936888 1347677217945265427529725 := by
  unfold tailWord_3936888
  simp only [CollatzResearch.WordTrace]
  refine ⟨71795050880667308892821659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95726734507556411857095545 71795050880667308892821659)
  ·
    refine ⟨107692576321000963339232489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71795050880667308892821659 107692576321000963339232489)
    ·
      refine ⟨80769432240750722504424367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107692576321000963339232489 80769432240750722504424367)
      ·
        refine ⟨121154148361126083756636551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80769432240750722504424367 121154148361126083756636551)
        ·
          refine ⟨181731222541689125634954827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121154148361126083756636551 181731222541689125634954827)
          ·
            refine ⟨272596833812533688452432241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181731222541689125634954827 272596833812533688452432241)
            ·
              refine ⟨204447625359400266339324181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272596833812533688452432241 204447625359400266339324181)
              ·
                refine ⟨9583482438721887484655821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204447625359400266339324181 9583482438721887484655821)
                ·
                  refine ⟨3593805914520707806745933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9583482438721887484655821 3593805914520707806745933)
                  ·
                    refine ⟨1347677217945265427529725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593805914520707806745933 1347677217945265427529725)
                    ·
                      rfl

theorem cell22_3936888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_3936888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936888 prefixEnd_3936888 := by exact prefixLift 3936888
  have htrace : WordTrace (prefixWord ++ tailWord_3936888) baseStart_3936888 baseEnd_3936888 := by
    simpa [prefixWord, tailWord_3936888, baseEnd_3936888] using wordTrace_append hprefix tailTrace_3936888
  have hstable : (prefixWord ++ tailWord_3936888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936888).length < 2 ^ (prefixWord ++ tailWord_3936888).sum := by decide
  have hdescent : baseEnd_3936888 < baseStart_3936888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936898 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3936898 : Nat := 118140960795 + 3936898 * 2 ^ 59
def prefixEnd_3936898 : Nat := 4983230072969 + 3 ^ 40 * 3936898 * 2
def baseEnd_3936898 : Nat := 1347680641149628734779695

theorem tailTrace_3936898 : CollatzResearch.WordTrace tailWord_3936898 prefixEnd_3936898 1347680641149628734779695 := by
  unfold tailWord_3936898
  simp only [CollatzResearch.WordTrace]
  refine ⟨35897616622824597373376837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95726977660865592995671565 35897616622824597373376837)
  ·
    refine ⟨6730803116779612007508157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35897616622824597373376837 6730803116779612007508157)
    ·
      refine ⟨2524051168792354502815559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6730803116779612007508157 2524051168792354502815559)
      ·
        refine ⟨3786076753188531754223339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2524051168792354502815559 3786076753188531754223339)
        ·
          refine ⟨5679115129782797631335009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3786076753188531754223339 5679115129782797631335009)
          ·
            refine ⟨4259336347337098223501257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5679115129782797631335009 4259336347337098223501257)
            ·
              refine ⟨3194502260502823667625943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259336347337098223501257 3194502260502823667625943)
              ·
                refine ⟨4791753390754235501438915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194502260502823667625943 4791753390754235501438915)
                ·
                  refine ⟨7187630086131353252158373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791753390754235501438915 7187630086131353252158373)
                  ·
                    refine ⟨1347680641149628734779695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7187630086131353252158373 1347680641149628734779695)
                    ·
                      rfl

theorem cell22_3936898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3936898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936898 prefixEnd_3936898 := by exact prefixLift 3936898
  have htrace : WordTrace (prefixWord ++ tailWord_3936898) baseStart_3936898 baseEnd_3936898 := by
    simpa [prefixWord, tailWord_3936898, baseEnd_3936898] using wordTrace_append hprefix tailTrace_3936898
  have hstable : (prefixWord ++ tailWord_3936898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936898).length < 2 ^ (prefixWord ++ tailWord_3936898).sum := by decide
  have hdescent : baseEnd_3936898 < baseStart_3936898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936931 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 2, 8]
def baseStart_3936931 : Nat := 118140960795 + 3936931 * 2 ^ 59
def prefixEnd_3936931 : Nat := 4983230072969 + 3 ^ 40 * 3936931 * 2
def baseEnd_3936931 : Nat := 1347691937724027648704593

theorem tailTrace_3936931 : CollatzResearch.WordTrace tailWord_3936931 prefixEnd_3936931 1347691937724027648704593 := by
  unfold tailWord_3936931
  simp only [CollatzResearch.WordTrace]
  refine ⟨143591670100178836129458647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95727780066785890752972431 143591670100178836129458647)
  ·
    refine ⟨215387505150268254194187971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143591670100178836129458647 215387505150268254194187971)
    ·
      refine ⟨323081257725402381291281957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215387505150268254194187971 323081257725402381291281957)
      ·
        refine ⟨60577735823512946492115367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323081257725402381291281957 60577735823512946492115367)
        ·
          refine ⟨90866603735269419738173051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60577735823512946492115367 90866603735269419738173051)
          ·
            refine ⟨136299905602904129607259577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90866603735269419738173051 136299905602904129607259577)
            ·
              refine ⟨102224929202178097205444683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136299905602904129607259577 102224929202178097205444683)
              ·
                refine ⟨153337393803267145808167025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102224929202178097205444683 153337393803267145808167025)
                ·
                  refine ⟨115003045352450359356125269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153337393803267145808167025 115003045352450359356125269)
                  ·
                    refine ⟨1347691937724027648704593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115003045352450359356125269 1347691937724027648704593)
                    ·
                      rfl

theorem cell22_3936931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_3936931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936931 prefixEnd_3936931 := by exact prefixLift 3936931
  have htrace : WordTrace (prefixWord ++ tailWord_3936931) baseStart_3936931 baseEnd_3936931 := by
    simpa [prefixWord, tailWord_3936931, baseEnd_3936931] using wordTrace_append hprefix tailTrace_3936931
  have hstable : (prefixWord ++ tailWord_3936931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936931).length < 2 ^ (prefixWord ++ tailWord_3936931).sum := by decide
  have hdescent : baseEnd_3936931 < baseStart_3936931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3936973 : List Nat := [1, 6, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3936973 : Nat := 118140960795 + 3936973 * 2 ^ 59
def prefixEnd_3936973 : Nat := 4983230072969 + 3 ^ 40 * 3936973 * 2
def baseEnd_3936973 : Nat := 1347706315182353539154465

theorem tailTrace_3936973 : CollatzResearch.WordTrace tailWord_3936973 prefixEnd_3936973 1347706315182353539154465 := by
  unfold tailWord_3936973
  simp only [CollatzResearch.WordTrace]
  refine ⟨143593201966026677302487573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95728801310684451534991715 143593201966026677302487573)
  ·
    refine ⟨6730931342157500498554105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143593201966026677302487573 6730931342157500498554105)
    ·
      refine ⟨5048198506618125373915579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6730931342157500498554105 5048198506618125373915579)
      ·
        refine ⟨7572297759927188060873369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048198506618125373915579 7572297759927188060873369)
        ·
          refine ⟨5679223319945391045655027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7572297759927188060873369 5679223319945391045655027)
          ·
            refine ⟨8518834979918086568482541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5679223319945391045655027 8518834979918086568482541)
            ·
              refine ⟨3194563117469282463180953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8518834979918086568482541 3194563117469282463180953)
              ·
                refine ⟨2395922338101961847385715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3194563117469282463180953 2395922338101961847385715)
                ·
                  refine ⟨3593883507152942771078573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395922338101961847385715 3593883507152942771078573)
                  ·
                    refine ⟨1347706315182353539154465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593883507152942771078573 1347706315182353539154465)
                    ·
                      rfl

theorem cell22_3936973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3936973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3936973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3936973 prefixEnd_3936973 := by exact prefixLift 3936973
  have htrace : WordTrace (prefixWord ++ tailWord_3936973) baseStart_3936973 baseEnd_3936973 := by
    simpa [prefixWord, tailWord_3936973, baseEnd_3936973] using wordTrace_append hprefix tailTrace_3936973
  have hstable : (prefixWord ++ tailWord_3936973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3936973).length < 2 ^ (prefixWord ++ tailWord_3936973).sum := by decide
  have hdescent : baseEnd_3936973 < baseStart_3936973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3936973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937010 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_3937010 : Nat := 118140960795 + 3937010 * 2 ^ 59
def prefixEnd_3937010 : Nat := 4983230072969 + 3 ^ 40 * 3937010 * 2
def baseEnd_3937010 : Nat := 1347718981038497775979351

theorem tailTrace_3937010 : CollatzResearch.WordTrace tailWord_3937010 prefixEnd_3937010 1347718981038497775979351 := by
  unfold tailWord_3937010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35898637866723158155396121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95729700977928421747722989 35898637866723158155396121)
  ·
    refine ⟨26923978400042368616547091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35898637866723158155396121 26923978400042368616547091)
    ·
      refine ⟨40385967600063552924820637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26923978400042368616547091 40385967600063552924820637)
      ·
        refine ⟨15144737850023832346807739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40385967600063552924820637 15144737850023832346807739)
        ·
          refine ⟨22717106775035748520211609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15144737850023832346807739 22717106775035748520211609)
          ·
            refine ⟨17037830081276811390158707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22717106775035748520211609 17037830081276811390158707)
            ·
              refine ⟨25556745121915217085238061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17037830081276811390158707 25556745121915217085238061)
              ·
                refine ⟨9583779420718206406964273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25556745121915217085238061 9583779420718206406964273)
                ·
                  refine ⟨7187834565538654805223205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9583779420718206406964273 7187834565538654805223205)
                  ·
                    refine ⟨1347718981038497775979351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7187834565538654805223205 1347718981038497775979351)
                    ·
                      rfl

theorem cell22_3937010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_3937010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937010 prefixEnd_3937010 := by exact prefixLift 3937010
  have htrace : WordTrace (prefixWord ++ tailWord_3937010) baseStart_3937010 baseEnd_3937010 := by
    simpa [prefixWord, tailWord_3937010, baseEnd_3937010] using wordTrace_append hprefix tailTrace_3937010
  have hstable : (prefixWord ++ tailWord_3937010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937010).length < 2 ^ (prefixWord ++ tailWord_3937010).sum := by decide
  have hdescent : baseEnd_3937010 < baseStart_3937010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937068 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_3937068 : Nat := 118140960795 + 3937068 * 2 ^ 59
def prefixEnd_3937068 : Nat := 4983230072969 + 3 ^ 40 * 3937068 * 2
def baseEnd_3937068 : Nat := 1347738835623804958029173

theorem tailTrace_3937068 : CollatzResearch.WordTrace tailWord_3937068 prefixEnd_3937068 1347738835623804958029173 := by
  unfold tailWord_3937068
  simp only [CollatzResearch.WordTrace]
  refine ⟨71798333450341254263597929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95731111267121672351463905 71798333450341254263597929)
  ·
    refine ⟨53848750087755940697698447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71798333450341254263597929 53848750087755940697698447)
    ·
      refine ⟨80773125131633911046547671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53848750087755940697698447 80773125131633911046547671)
      ·
        refine ⟨121159687697450866569821507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80773125131633911046547671 121159687697450866569821507)
        ·
          refine ⟨181739531546176299854732261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121159687697450866569821507 181739531546176299854732261)
          ·
            refine ⟨34076162164908056222762299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181739531546176299854732261 34076162164908056222762299)
            ·
              refine ⟨51114243247362084334143449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34076162164908056222762299 51114243247362084334143449)
              ·
                refine ⟨38335682435521563250607587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51114243247362084334143449 38335682435521563250607587)
                ·
                  refine ⟨57503523653282344875911381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38335682435521563250607587 57503523653282344875911381)
                  ·
                    refine ⟨1347738835623804958029173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57503523653282344875911381 1347738835623804958029173)
                    ·
                      rfl

theorem cell22_3937068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_3937068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937068 prefixEnd_3937068 := by exact prefixLift 3937068
  have htrace : WordTrace (prefixWord ++ tailWord_3937068) baseStart_3937068 baseEnd_3937068 := by
    simpa [prefixWord, tailWord_3937068, baseEnd_3937068] using wordTrace_append hprefix tailTrace_3937068
  have hstable : (prefixWord ++ tailWord_3937068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937068).length < 2 ^ (prefixWord ++ tailWord_3937068).sum := by decide
  have hdescent : baseEnd_3937068 < baseStart_3937068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937074 : List Nat := [3, 2, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_3937074 : Nat := 118140960795 + 3937074 * 2 ^ 59
def prefixEnd_3937074 : Nat := 4983230072969 + 3 ^ 40 * 3937074 * 2
def baseEnd_3937074 : Nat := 1347740889546422942379155

theorem tailTrace_3937074 : CollatzResearch.WordTrace tailWord_3937074 prefixEnd_3937074 1347740889546422942379155 := by
  unfold tailWord_3937074
  simp only [CollatzResearch.WordTrace]
  refine ⟨35899221434665192887978569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95731257159107181034609517 35899221434665192887978569)
  ·
    refine ⟨26924416075998894665983927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35899221434665192887978569 26924416075998894665983927)
    ·
      refine ⟨40386624113998341998975891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26924416075998894665983927 40386624113998341998975891)
      ·
        refine ⟨60579936170997512998463837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40386624113998341998975891 60579936170997512998463837)
        ·
          refine ⟨22717476064124067374423939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60579936170997512998463837 22717476064124067374423939)
          ·
            refine ⟨34076214096186101061635909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22717476064124067374423939 34076214096186101061635909)
            ·
              refine ⟨6389290143034893949056733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34076214096186101061635909 6389290143034893949056733)
              ·
                refine ⟨2395983803638085230896275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6389290143034893949056733 2395983803638085230896275)
                ·
                  refine ⟨3593975705457127846344413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395983803638085230896275 3593975705457127846344413)
                  ·
                    refine ⟨1347740889546422942379155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593975705457127846344413 1347740889546422942379155)
                    ·
                      rfl

theorem cell22_3937074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_3937074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937074 prefixEnd_3937074 := by exact prefixLift 3937074
  have htrace : WordTrace (prefixWord ++ tailWord_3937074) baseStart_3937074 baseEnd_3937074 := by
    simpa [prefixWord, tailWord_3937074, baseEnd_3937074] using wordTrace_append hprefix tailTrace_3937074
  have hstable : (prefixWord ++ tailWord_3937074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937074).length < 2 ^ (prefixWord ++ tailWord_3937074).sum := by decide
  have hdescent : baseEnd_3937074 < baseStart_3937074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937087 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 5]
def baseStart_3937087 : Nat := 118140960795 + 3937087 * 2 ^ 59
def prefixEnd_3937087 : Nat := 4983230072969 + 3 ^ 40 * 3937087 * 2
def baseEnd_3937087 : Nat := 449248446570698413934705

theorem tailTrace_3937087 : CollatzResearch.WordTrace tailWord_3937087 prefixEnd_3937087 449248446570698413934705 := by
  unfold tailWord_3937087
  simp only [CollatzResearch.WordTrace]
  refine ⟨143597359887613674772137515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95731573258409116514758343 143597359887613674772137515)
  ·
    refine ⟨215396039831420512158206273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143597359887613674772137515 215396039831420512158206273)
    ·
      refine ⟨161547029873565384118654705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215396039831420512158206273 161547029873565384118654705)
      ·
        refine ⟨121160272405174038088991029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161547029873565384118654705 121160272405174038088991029)
        ·
          refine ⟨11358775537985066070842909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121160272405174038088991029 11358775537985066070842909)
          ·
            refine ⟨4259540826744399776566091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11358775537985066070842909 4259540826744399776566091)
            ·
              refine ⟨6389311240116599664849137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4259540826744399776566091 6389311240116599664849137)
              ·
                refine ⟨4791983430087449748636853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6389311240116599664849137 4791983430087449748636853)
                ·
                  refine ⟨449248446570698413934705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4791983430087449748636853 449248446570698413934705)
                  ·
                    rfl

theorem cell22_3937087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 5].length) (baseStart_3937087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937087 prefixEnd_3937087 := by exact prefixLift 3937087
  have htrace : WordTrace (prefixWord ++ tailWord_3937087) baseStart_3937087 baseEnd_3937087 := by
    simpa [prefixWord, tailWord_3937087, baseEnd_3937087] using wordTrace_append hprefix tailTrace_3937087
  have hstable : (prefixWord ++ tailWord_3937087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937087).length < 2 ^ (prefixWord ++ tailWord_3937087).sum := by decide
  have hdescent : baseEnd_3937087 < baseStart_3937087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937145 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_3937145 : Nat := 118140960795 + 3937145 * 2 ^ 59
def prefixEnd_3937145 : Nat := 4983230072969 + 3 ^ 40 * 3937145 * 2
def baseEnd_3937145 : Nat := 1347765194297402423853937

theorem tailTrace_3937145 : CollatzResearch.WordTrace tailWord_3937145 prefixEnd_3937145 1347765194297402423853937 := by
  unfold tailWord_3937145
  simp only [CollatzResearch.WordTrace]
  refine ⟨143599475321403550677748889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95732983547602367118499259 143599475321403550677748889)
  ·
    refine ⟨107699606491052663008311667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143599475321403550677748889 107699606491052663008311667)
    ·
      refine ⟨161549409736578994512467501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107699606491052663008311667 161549409736578994512467501)
      ·
        refine ⟨60581028651217122942175313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161549409736578994512467501 60581028651217122942175313)
        ·
          refine ⟨45435771488412842206631485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60581028651217122942175313 45435771488412842206631485)
          ·
            refine ⟨17038414308154815827486807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45435771488412842206631485 17038414308154815827486807)
            ·
              refine ⟨25557621462232223741230211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17038414308154815827486807 25557621462232223741230211)
              ·
                refine ⟨38336432193348335611845317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25557621462232223741230211 38336432193348335611845317)
                ·
                  refine ⟨7188081036252812927220997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38336432193348335611845317 7188081036252812927220997)
                  ·
                    refine ⟨1347765194297402423853937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7188081036252812927220997 1347765194297402423853937)
                    ·
                      rfl

theorem cell22_3937145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_3937145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937145 prefixEnd_3937145 := by exact prefixLift 3937145
  have htrace : WordTrace (prefixWord ++ tailWord_3937145) baseStart_3937145 baseEnd_3937145 := by
    simpa [prefixWord, tailWord_3937145, baseEnd_3937145] using wordTrace_append hprefix tailTrace_3937145
  have hstable : (prefixWord ++ tailWord_3937145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937145).length < 2 ^ (prefixWord ++ tailWord_3937145).sum := by decide
  have hdescent : baseEnd_3937145 < baseStart_3937145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937160 : List Nat := [2, 1, 3, 3, 2, 1, 1, 9]
def baseStart_3937160 : Nat := 118140960795 + 3937160 * 2 ^ 59
def prefixEnd_3937160 : Nat := 4983230072969 + 3 ^ 40 * 3937160 * 2
def baseEnd_3937160 : Nat := 149752258789327487192099

theorem tailTrace_3937160 : CollatzResearch.WordTrace tailWord_3937160 prefixEnd_3937160 149752258789327487192099 := by
  unfold tailWord_3937160
  simp only [CollatzResearch.WordTrace]
  refine ⟨71800011208174604119772467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95733348277566138826363289 71800011208174604119772467)
  ·
    refine ⟨107700016812261906179658701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71800011208174604119772467 107700016812261906179658701)
    ·
      refine ⟨40387506304598214817372013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107700016812261906179658701 40387506304598214817372013)
      ·
        refine ⟨15145314864224330556514505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40387506304598214817372013 15145314864224330556514505)
        ·
          refine ⟨11358986148168247917385879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15145314864224330556514505 11358986148168247917385879)
          ·
            refine ⟨17038479222252371876078819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11358986148168247917385879 17038479222252371876078819)
            ·
              refine ⟨25557718833378557814118229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17038479222252371876078819 25557718833378557814118229)
              ·
                refine ⟨149752258789327487192099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25557718833378557814118229 149752258789327487192099)
                ·
                  rfl

theorem cell22_3937160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 9].length) (baseStart_3937160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937160 prefixEnd_3937160 := by exact prefixLift 3937160
  have htrace : WordTrace (prefixWord ++ tailWord_3937160) baseStart_3937160 baseEnd_3937160 := by
    simpa [prefixWord, tailWord_3937160, baseEnd_3937160] using wordTrace_append hprefix tailTrace_3937160
  have hstable : (prefixWord ++ tailWord_3937160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937160).length < 2 ^ (prefixWord ++ tailWord_3937160).sum := by decide
  have hdescent : baseEnd_3937160 < baseStart_3937160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937164 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 2, 3]
def baseStart_3937164 : Nat := 118140960795 + 3937164 * 2 ^ 59
def prefixEnd_3937164 : Nat := 4983230072969 + 3 ^ 40 * 3937164 * 2
def baseEnd_3937164 : Nat := 1347771698385692707628879

theorem tailTrace_3937164 : CollatzResearch.WordTrace tailWord_3937164 prefixEnd_3937164 1347771698385692707628879 := by
  unfold tailWord_3937164
  simp only [CollatzResearch.WordTrace]
  refine ⟨71800084154167358461345273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95733445538889811281793697 71800084154167358461345273)
  ·
    refine ⟨53850063115625518846008955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71800084154167358461345273 53850063115625518846008955)
    ·
      refine ⟨80775094673438278269013433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53850063115625518846008955 80775094673438278269013433)
      ·
        refine ⟨60581321005078708701760075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80775094673438278269013433 60581321005078708701760075)
        ·
          refine ⟨90871981507618063052640113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60581321005078708701760075 90871981507618063052640113)
          ·
            refine ⟨68153986130713547289480085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90871981507618063052640113 68153986130713547289480085)
            ·
              refine ⟨3194718099877197529194379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68153986130713547289480085 3194718099877197529194379)
              ·
                refine ⟨4792077149815796293791569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194718099877197529194379 4792077149815796293791569)
                ·
                  refine ⟨3594057862361847220343677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4792077149815796293791569 3594057862361847220343677)
                  ·
                    refine ⟨1347771698385692707628879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3594057862361847220343677 1347771698385692707628879)
                    ·
                      rfl

theorem cell22_3937164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_3937164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937164 prefixEnd_3937164 := by exact prefixLift 3937164
  have htrace : WordTrace (prefixWord ++ tailWord_3937164) baseStart_3937164 baseEnd_3937164 := by
    simpa [prefixWord, tailWord_3937164, baseEnd_3937164] using wordTrace_append hprefix tailTrace_3937164
  have hstable : (prefixWord ++ tailWord_3937164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937164).length < 2 ^ (prefixWord ++ tailWord_3937164).sum := by decide
  have hdescent : baseEnd_3937164 < baseStart_3937164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937301 : List Nat := [1, 3, 2, 1, 4, 3, 1, 3, 4]
def baseStart_3937301 : Nat := 118140960795 + 3937301 * 2 ^ 59
def prefixEnd_3937301 : Nat := 4983230072969 + 3 ^ 40 * 3937301 * 2
def baseEnd_3937301 : Nat := 449272865428490005651153

theorem tailTrace_3937301 : CollatzResearch.WordTrace tailWord_3937301 prefixEnd_3937301 449272865428490005651153 := by
  unfold tailWord_3937301
  simp only [CollatzResearch.WordTrace]
  refine ⟨143605165108838389320427757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95736776739225592880285171 143605165108838389320427757)
  ·
    refine ⟨53851936915814395995160409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143605165108838389320427757 53851936915814395995160409)
    ·
      refine ⟨40388952686860796996370307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53851936915814395995160409 40388952686860796996370307)
      ·
        refine ⟨60583429030291195494555461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40388952686860796996370307 60583429030291195494555461)
        ·
          refine ⟨11359392943179599155229149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60583429030291195494555461 11359392943179599155229149)
          ·
            refine ⟨4259772353692349683210931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11359392943179599155229149 4259772353692349683210931)
            ·
              refine ⟨6389658530538524524816397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4259772353692349683210931 6389658530538524524816397)
              ·
                refine ⟨2396121948951946696806149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6389658530538524524816397 2396121948951946696806149)
                ·
                  refine ⟨449272865428490005651153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396121948951946696806149 449272865428490005651153)
                  ·
                    rfl

theorem cell22_3937301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_3937301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937301 prefixEnd_3937301 := by exact prefixLift 3937301
  have htrace : WordTrace (prefixWord ++ tailWord_3937301) baseStart_3937301 baseEnd_3937301 := by
    simpa [prefixWord, tailWord_3937301, baseEnd_3937301] using wordTrace_append hprefix tailTrace_3937301
  have hstable : (prefixWord ++ tailWord_3937301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937301).length < 2 ^ (prefixWord ++ tailWord_3937301).sum := by decide
  have hdescent : baseEnd_3937301 < baseStart_3937301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937314 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_3937314 : Nat := 118140960795 + 3937314 * 2 ^ 59
def prefixEnd_3937314 : Nat := 4983230072969 + 3 ^ 40 * 3937314 * 2
def baseEnd_3937314 : Nat := 1347823046451142316378419

theorem tailTrace_3937314 : CollatzResearch.WordTrace tailWord_3937314 prefixEnd_3937314 1347823046451142316378419 := by
  unfold tailWord_3937314
  simp only [CollatzResearch.WordTrace]
  refine ⟨35901409814447823135162749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95737092838527528360433997 35901409814447823135162749)
  ·
    refine ⟨13463028680417933675686031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35901409814447823135162749 13463028680417933675686031)
    ·
      refine ⟨20194543020626900513529047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13463028680417933675686031 20194543020626900513529047)
      ·
        refine ⟨30291814530940350770293571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20194543020626900513529047 30291814530940350770293571)
        ·
          refine ⟨45437721796410526155440357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30291814530940350770293571 45437721796410526155440357)
          ·
            refine ⟨8519572836826973654145067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45437721796410526155440357 8519572836826973654145067)
            ·
              refine ⟨12779359255240460481217601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8519572836826973654145067 12779359255240460481217601)
              ·
                refine ⟨9584519441430345360913201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12779359255240460481217601 9584519441430345360913201)
                ·
                  refine ⟨7188389581072759020684901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9584519441430345360913201 7188389581072759020684901)
                  ·
                    refine ⟨1347823046451142316378419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7188389581072759020684901 1347823046451142316378419)
                    ·
                      rfl

theorem cell22_3937314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_3937314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937314 prefixEnd_3937314 := by exact prefixLift 3937314
  have htrace : WordTrace (prefixWord ++ tailWord_3937314) baseStart_3937314 baseEnd_3937314 := by
    simpa [prefixWord, tailWord_3937314, baseEnd_3937314] using wordTrace_append hprefix tailTrace_3937314
  have hstable : (prefixWord ++ tailWord_3937314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937314).length < 2 ^ (prefixWord ++ tailWord_3937314).sum := by decide
  have hdescent : baseEnd_3937314 < baseStart_3937314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937389 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3937389 : Nat := 118140960795 + 3937389 * 2 ^ 59
def prefixEnd_3937389 : Nat := 4983230072969 + 3 ^ 40 * 3937389 * 2
def baseEnd_3937389 : Nat := 1347848720483867120753189

theorem tailTrace_3937389 : CollatzResearch.WordTrace tailWord_3937389 prefixEnd_3937389 1347848720483867120753189 := by
  unfold tailWord_3937389
  simp only [CollatzResearch.WordTrace]
  refine ⟨143608374732519580349631221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95738916488346386899754147 143608374732519580349631221)
  ·
    refine ⟨13463285131173710657777927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143608374732519580349631221 13463285131173710657777927)
    ·
      refine ⟨20194927696760565986666891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13463285131173710657777927 20194927696760565986666891)
      ·
        refine ⟨30292391545140848980000337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20194927696760565986666891 30292391545140848980000337)
        ·
          refine ⟨22719293658855636735000253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30292391545140848980000337 22719293658855636735000253)
          ·
            refine ⟨8519735122070863775625095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22719293658855636735000253 8519735122070863775625095)
            ·
              refine ⟨12779602683106295663437643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8519735122070863775625095 12779602683106295663437643)
              ·
                refine ⟨19169404024659443495156465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12779602683106295663437643 19169404024659443495156465)
                ·
                  refine ⟨14377053018494582621367349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19169404024659443495156465 14377053018494582621367349)
                  ·
                    refine ⟨1347848720483867120753189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14377053018494582621367349 1347848720483867120753189)
                    ·
                      rfl

theorem cell22_3937389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3937389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937389 prefixEnd_3937389 := by exact prefixLift 3937389
  have htrace : WordTrace (prefixWord ++ tailWord_3937389) baseStart_3937389 baseEnd_3937389 := by
    simpa [prefixWord, tailWord_3937389, baseEnd_3937389] using wordTrace_append hprefix tailTrace_3937389
  have hstable : (prefixWord ++ tailWord_3937389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937389).length < 2 ^ (prefixWord ++ tailWord_3937389).sum := by decide
  have hdescent : baseEnd_3937389 < baseStart_3937389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937404 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_3937404 : Nat := 118140960795 + 3937404 * 2 ^ 59
def prefixEnd_3937404 : Nat := 4983230072969 + 3 ^ 40 * 3937404 * 2
def baseEnd_3937404 : Nat := 1347853855290412081628143

theorem tailTrace_3937404 : CollatzResearch.WordTrace tailWord_3937404 prefixEnd_3937404 1347853855290412081628143 := by
  unfold tailWord_3937404
  simp only [CollatzResearch.WordTrace]
  refine ⟨71804460913732618955713633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95739281218310158607618177 71804460913732618955713633)
  ·
    refine ⟨53853345685299464216785225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71804460913732618955713633 53853345685299464216785225)
    ·
      refine ⟨40390009263974598162588919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53853345685299464216785225 40390009263974598162588919)
      ·
        refine ⟨60585013895961897243883379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40390009263974598162588919 60585013895961897243883379)
        ·
          refine ⟨90877520843942845865825069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60585013895961897243883379 90877520843942845865825069)
          ·
            refine ⟨34079070316478567199684401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90877520843942845865825069 34079070316478567199684401)
            ·
              refine ⟨25559302737358925399763301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34079070316478567199684401 25559302737358925399763301)
              ·
                refine ⟨4792369263254798512455619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25559302737358925399763301 4792369263254798512455619)
                ·
                  refine ⟨7188553894882197768683429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792369263254798512455619 7188553894882197768683429)
                  ·
                    refine ⟨1347853855290412081628143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7188553894882197768683429 1347853855290412081628143)
                    ·
                      rfl

theorem cell22_3937404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_3937404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937404 prefixEnd_3937404 := by exact prefixLift 3937404
  have htrace : WordTrace (prefixWord ++ tailWord_3937404) baseStart_3937404 baseEnd_3937404 := by
    simpa [prefixWord, tailWord_3937404, baseEnd_3937404] using wordTrace_append hprefix tailTrace_3937404
  have hstable : (prefixWord ++ tailWord_3937404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937404).length < 2 ^ (prefixWord ++ tailWord_3937404).sum := by decide
  have hdescent : baseEnd_3937404 < baseStart_3937404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937436 : List Nat := [2, 2, 3, 2, 1, 2, 2, 4, 4]
def baseStart_3937436 : Nat := 118140960795 + 3937436 * 2 ^ 59
def prefixEnd_3937436 : Nat := 4983230072969 + 3 ^ 40 * 3937436 * 2
def baseEnd_3937436 : Nat := 449288269848124888276015

theorem tailTrace_3937436 : CollatzResearch.WordTrace tailWord_3937436 prefixEnd_3937436 449288269848124888276015 := by
  unfold tailWord_3937436
  simp only [CollatzResearch.WordTrace]
  refine ⟨71805044481674653688296081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95740059308899538251061441 71805044481674653688296081)
  ·
    refine ⟨53853783361255990266222061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71805044481674653688296081 53853783361255990266222061)
    ·
      refine ⟨20195168760470996349833273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53853783361255990266222061 20195168760470996349833273)
      ·
        refine ⟨15146376570353247262374955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20195168760470996349833273 15146376570353247262374955)
        ·
          refine ⟨22719564855529870893562433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15146376570353247262374955 22719564855529870893562433)
          ·
            refine ⟨17039673641647403170171825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22719564855529870893562433 17039673641647403170171825)
            ·
              refine ⟨12779755231235552377628869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17039673641647403170171825 12779755231235552377628869)
              ·
                refine ⟨2396204105856666070805413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12779755231235552377628869 2396204105856666070805413)
                ·
                  refine ⟨449288269848124888276015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396204105856666070805413 449288269848124888276015)
                  ·
                    rfl

theorem cell22_3937436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_3937436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937436 prefixEnd_3937436 := by exact prefixLift 3937436
  have htrace : WordTrace (prefixWord ++ tailWord_3937436) baseStart_3937436 baseEnd_3937436 := by
    simpa [prefixWord, tailWord_3937436, baseEnd_3937436] using wordTrace_append hprefix tailTrace_3937436
  have hstable : (prefixWord ++ tailWord_3937436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937436).length < 2 ^ (prefixWord ++ tailWord_3937436).sum := by decide
  have hdescent : baseEnd_3937436 < baseStart_3937436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937477 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_3937477 : Nat := 118140960795 + 3937477 * 2 ^ 59
def prefixEnd_3937477 : Nat := 4983230072969 + 3 ^ 40 * 3937477 * 2
def baseEnd_3937477 : Nat := 1347878844682264224552919

theorem tailTrace_3937477 : CollatzResearch.WordTrace tailWord_3937477 prefixEnd_3937477 1347878844682264224552919 := by
  unfold tailWord_3937477
  simp only [CollatzResearch.WordTrace]
  refine ⟨143611584356200771378834685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95741056237467180919223123 143611584356200771378834685)
  ·
    refine ⟨53854344133575289267063007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143611584356200771378834685 53854344133575289267063007)
    ·
      refine ⟨80781516200362933900594511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53854344133575289267063007 80781516200362933900594511)
      ·
        refine ⟨121172274300544400850891767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80781516200362933900594511 121172274300544400850891767)
        ·
          refine ⟨181758411450816601276337651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121172274300544400850891767 181758411450816601276337651)
          ·
            refine ⟨272637617176224901914506477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181758411450816601276337651 272637617176224901914506477)
            ·
              refine ⟨102239106441084338217939929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272637617176224901914506477 102239106441084338217939929)
              ·
                refine ⟨76679329830813253663454947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102239106441084338217939929 76679329830813253663454947)
                ·
                  refine ⟨115018994746219880495182421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76679329830813253663454947 115018994746219880495182421)
                  ·
                    refine ⟨1347878844682264224552919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115018994746219880495182421 1347878844682264224552919)
                    ·
                      rfl

theorem cell22_3937477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_3937477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937477 prefixEnd_3937477 := by exact prefixLift 3937477
  have htrace : WordTrace (prefixWord ++ tailWord_3937477) baseStart_3937477 baseEnd_3937477 := by
    simpa [prefixWord, tailWord_3937477, baseEnd_3937477] using wordTrace_append hprefix tailTrace_3937477
  have hstable : (prefixWord ++ tailWord_3937477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937477).length < 2 ^ (prefixWord ++ tailWord_3937477).sum := by decide
  have hdescent : baseEnd_3937477 < baseStart_3937477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937479 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 5, 3]
def baseStart_3937479 : Nat := 118140960795 + 3937479 * 2 ^ 59
def prefixEnd_3937479 : Nat := 4983230072969 + 3 ^ 40 * 3937479 * 2
def baseEnd_3937479 : Nat := 1347879529323136886002913

theorem tailTrace_3937479 : CollatzResearch.WordTrace tailWord_3937479 prefixEnd_3937479 1347879529323136886002913 := by
  unfold tailWord_3937479
  simp only [CollatzResearch.WordTrace]
  refine ⟨143611657302193525720407491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95741104868129017146938327 143611657302193525720407491)
  ·
    refine ⟨215417485953290288580611237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143611657302193525720407491 215417485953290288580611237)
    ·
      refine ⟨40390778616241929108864607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215417485953290288580611237 40390778616241929108864607)
      ·
        refine ⟨60586167924362893663296911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40390778616241929108864607 60586167924362893663296911)
        ·
          refine ⟨90879251886544340494945367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60586167924362893663296911 90879251886544340494945367)
          ·
            refine ⟨136318877829816510742418051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90879251886544340494945367 136318877829816510742418051)
            ·
              refine ⟨204478316744724766113627077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136318877829816510742418051 204478316744724766113627077)
              ·
                refine ⟨38339684389635893646305077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204478316744724766113627077 38339684389635893646305077)
                ·
                  refine ⟨3594345411528365029341101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38339684389635893646305077 3594345411528365029341101)
                  ·
                    refine ⟨1347879529323136886002913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3594345411528365029341101 1347879529323136886002913)
                    ·
                      rfl

theorem cell22_3937479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_3937479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937479 prefixEnd_3937479 := by exact prefixLift 3937479
  have htrace : WordTrace (prefixWord ++ tailWord_3937479) baseStart_3937479 baseEnd_3937479 := by
    simpa [prefixWord, tailWord_3937479, baseEnd_3937479] using wordTrace_append hprefix tailTrace_3937479
  have hstable : (prefixWord ++ tailWord_3937479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937479).length < 2 ^ (prefixWord ++ tailWord_3937479).sum := by decide
  have hdescent : baseEnd_3937479 < baseStart_3937479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937584 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_3937584 : Nat := 118140960795 + 3937584 * 2 ^ 59
def prefixEnd_3937584 : Nat := 4983230072969 + 3 ^ 40 * 3937584 * 2
def baseEnd_3937584 : Nat := 1347915472968951612127591

theorem tailTrace_3937584 : CollatzResearch.WordTrace tailWord_3937584 prefixEnd_3937584 1347915472968951612127591 := by
  unfold tailWord_3937584
  simp only [CollatzResearch.WordTrace]
  refine ⟨71807743483406564326489903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95743657977875419101986537 71807743483406564326489903)
  ·
    refine ⟨107711615225109846489734855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71807743483406564326489903 107711615225109846489734855)
    ·
      refine ⟨161567422837664769734602283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107711615225109846489734855 161567422837664769734602283)
      ·
        refine ⟨242351134256497154601903425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161567422837664769734602283 242351134256497154601903425)
        ·
          refine ⟨181763350692372865951427569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242351134256497154601903425 181763350692372865951427569)
          ·
            refine ⟨136322513019279649463570677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181763350692372865951427569 136322513019279649463570677)
            ·
              refine ⟨12780235595557467137209751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136322513019279649463570677 12780235595557467137209751)
              ·
                refine ⟨19170353393336200705814627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12780235595557467137209751 19170353393336200705814627)
                ·
                  refine ⟨28755530090004301058721941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19170353393336200705814627 28755530090004301058721941)
                  ·
                    refine ⟨1347915472968951612127591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28755530090004301058721941 1347915472968951612127591)
                    ·
                      rfl

theorem cell22_3937584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_3937584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937584 prefixEnd_3937584 := by exact prefixLift 3937584
  have htrace : WordTrace (prefixWord ++ tailWord_3937584) baseStart_3937584 baseEnd_3937584 := by
    simpa [prefixWord, tailWord_3937584, baseEnd_3937584] using wordTrace_append hprefix tailTrace_3937584
  have hstable : (prefixWord ++ tailWord_3937584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937584).length < 2 ^ (prefixWord ++ tailWord_3937584).sum := by decide
  have hdescent : baseEnd_3937584 < baseStart_3937584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937586 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_3937586 : Nat := 118140960795 + 3937586 * 2 ^ 59
def prefixEnd_3937586 : Nat := 4983230072969 + 3 ^ 40 * 3937586 * 2
def baseEnd_3937586 : Nat := 1347916157609824273577585

theorem tailTrace_3937586 : CollatzResearch.WordTrace tailWord_3937586 prefixEnd_3937586 1347916157609824273577585 := by
  unfold tailWord_3937586
  simp only [CollatzResearch.WordTrace]
  refine ⟨35903889978201470748638153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95743706608537255329701741 35903889978201470748638153)
  ·
    refine ⟨26927917483651103061478615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35903889978201470748638153 26927917483651103061478615)
    ·
      refine ⟨40391876225476654592217923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26927917483651103061478615 40391876225476654592217923)
      ·
        refine ⟨60587814338214981888326885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40391876225476654592217923 60587814338214981888326885)
        ·
          refine ⟨11360215188415309104061291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60587814338214981888326885 11360215188415309104061291)
          ·
            refine ⟨17040322782622963656091937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11360215188415309104061291 17040322782622963656091937)
            ·
              refine ⟨12780242086967222742068953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17040322782622963656091937 12780242086967222742068953)
              ·
                refine ⟨9585181565225417056551715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12780242086967222742068953 9585181565225417056551715)
                ·
                  refine ⟨14377772347838125584827573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9585181565225417056551715 14377772347838125584827573)
                  ·
                    refine ⟨1347916157609824273577585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14377772347838125584827573 1347916157609824273577585)
                    ·
                      rfl

theorem cell22_3937586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_3937586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937586 prefixEnd_3937586 := by exact prefixLift 3937586
  have htrace : WordTrace (prefixWord ++ tailWord_3937586) baseStart_3937586 baseEnd_3937586 := by
    simpa [prefixWord, tailWord_3937586, baseEnd_3937586] using wordTrace_append hprefix tailTrace_3937586
  have hstable : (prefixWord ++ tailWord_3937586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937586).length < 2 ^ (prefixWord ++ tailWord_3937586).sum := by decide
  have hdescent : baseEnd_3937586 < baseStart_3937586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937599 : List Nat := [1, 1, 2, 2, 4, 3, 9]
def baseStart_3937599 : Nat := 118140960795 + 3937599 * 2 ^ 59
def prefixEnd_3937599 : Nat := 4983230072969 + 3 ^ 40 * 3937599 * 2
def baseEnd_3937599 : Nat := 49922985473166539740835

theorem tailTrace_3937599 : CollatzResearch.WordTrace tailWord_3937599 prefixEnd_3937599 49922985473166539740835 := by
  unfold tailWord_3937599
  simp only [CollatzResearch.WordTrace]
  refine ⟨143616034061758786214775851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95744022707839190809850567 143616034061758786214775851)
  ·
    refine ⟨215424051092638179322163777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143616034061758786214775851 215424051092638179322163777)
    ·
      refine ⟨161568038319478634491622833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215424051092638179322163777 161568038319478634491622833)
      ·
        refine ⟨121176028739608975868717125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161568038319478634491622833 121176028739608975868717125)
        ·
          refine ⟨22720505388676682975384461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121176028739608975868717125 22720505388676682975384461)
          ·
            refine ⟨8520189520753756115769173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22720505388676682975384461 8520189520753756115769173)
            ·
              refine ⟨49922985473166539740835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8520189520753756115769173 49922985473166539740835)
              ·
                rfl

theorem cell22_3937599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 9].length) (baseStart_3937599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937599 prefixEnd_3937599 := by exact prefixLift 3937599
  have htrace : WordTrace (prefixWord ++ tailWord_3937599) baseStart_3937599 baseEnd_3937599 := by
    simpa [prefixWord, tailWord_3937599, baseEnd_3937599] using wordTrace_append hprefix tailTrace_3937599
  have hstable : (prefixWord ++ tailWord_3937599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937599).length < 2 ^ (prefixWord ++ tailWord_3937599).sum := by decide
  have hdescent : baseEnd_3937599 < baseStart_3937599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937620 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_3937620 : Nat := 118140960795 + 3937620 * 2 ^ 59
def prefixEnd_3937620 : Nat := 4983230072969 + 3 ^ 40 * 3937620 * 2
def baseEnd_3937620 : Nat := 1347927796504659518227481

theorem tailTrace_3937620 : CollatzResearch.WordTrace tailWord_3937620 prefixEnd_3937620 1347927796504659518227481 := by
  unfold tailWord_3937620
  simp only [CollatzResearch.WordTrace]
  refine ⟨71808399997341353400645157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95744533329788471200860209 71808399997341353400645157)
  ·
    refine ⟨13464074999501503762620967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71808399997341353400645157 13464074999501503762620967)
    ·
      refine ⟨20196112499252255643931451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13464074999501503762620967 20196112499252255643931451)
      ·
        refine ⟨30294168748878383465897177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20196112499252255643931451 30294168748878383465897177)
        ·
          refine ⟨22720626561658787599422883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30294168748878383465897177 22720626561658787599422883)
          ·
            refine ⟨34080939842488181399134325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22720626561658787599422883 34080939842488181399134325)
            ·
              refine ⟨3195088110233267006168843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34080939842488181399134325 3195088110233267006168843)
              ·
                refine ⟨4792632165349900509253265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3195088110233267006168843 4792632165349900509253265)
                ·
                  refine ⟨3594474124012425381939949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4792632165349900509253265 3594474124012425381939949)
                  ·
                    refine ⟨1347927796504659518227481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3594474124012425381939949 1347927796504659518227481)
                    ·
                      rfl

theorem cell22_3937620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_3937620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937620 prefixEnd_3937620 := by exact prefixLift 3937620
  have htrace : WordTrace (prefixWord ++ tailWord_3937620) baseStart_3937620 baseEnd_3937620 := by
    simpa [prefixWord, tailWord_3937620, baseEnd_3937620] using wordTrace_append hprefix tailTrace_3937620
  have hstable : (prefixWord ++ tailWord_3937620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937620).length < 2 ^ (prefixWord ++ tailWord_3937620).sum := by decide
  have hdescent : baseEnd_3937620 < baseStart_3937620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937661 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 5]
def baseStart_3937661 : Nat := 118140960795 + 3937661 * 2 ^ 59
def prefixEnd_3937661 : Nat := 4983230072969 + 3 ^ 40 * 3937661 * 2
def baseEnd_3937661 : Nat := 449313943880849692650785

theorem tailTrace_3937661 : CollatzResearch.WordTrace tailWord_3937661 prefixEnd_3937661 449313943880849692650785 := by
  unfold tailWord_3937661
  simp only [CollatzResearch.WordTrace]
  refine ⟨143618295387534170803532837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95745530258356113869021891 143618295387534170803532837)
  ·
    refine ⟨26928430385162657025662407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143618295387534170803532837 26928430385162657025662407)
    ·
      refine ⟨40392645577743985538493611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26928430385162657025662407 40392645577743985538493611)
      ·
        refine ⟨60588968366615978307740417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40392645577743985538493611 60588968366615978307740417)
        ·
          refine ⟨45441726274961983730805313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60588968366615978307740417 45441726274961983730805313)
          ·
            refine ⟨34081294706221487798103985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45441726274961983730805313 34081294706221487798103985)
            ·
              refine ⟨25560971029666115848577989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34081294706221487798103985 25560971029666115848577989)
              ·
                refine ⟨4792682068062396721608373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25560971029666115848577989 4792682068062396721608373)
                ·
                  refine ⟨449313943880849692650785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4792682068062396721608373 449313943880849692650785)
                  ·
                    rfl

theorem cell22_3937661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_3937661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937661 prefixEnd_3937661 := by exact prefixLift 3937661
  have htrace : WordTrace (prefixWord ++ tailWord_3937661) baseStart_3937661 baseEnd_3937661 := by
    simpa [prefixWord, tailWord_3937661, baseEnd_3937661] using wordTrace_append hprefix tailTrace_3937661
  have hstable : (prefixWord ++ tailWord_3937661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937661).length < 2 ^ (prefixWord ++ tailWord_3937661).sum := by decide
  have hdescent : baseEnd_3937661 < baseStart_3937661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937736 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_3937736 : Nat := 118140960795 + 3937736 * 2 ^ 59
def prefixEnd_3937736 : Nat := 4983230072969 + 3 ^ 40 * 3937736 * 2
def baseEnd_3937736 : Nat := 1347967505675273882327125

theorem tailTrace_3937736 : CollatzResearch.WordTrace tailWord_3937736 prefixEnd_3937736 1347967505675273882327125 := by
  unfold tailWord_3937736
  simp only [CollatzResearch.WordTrace]
  refine ⟨71810515431131229306256531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95747353908174972408342041 71810515431131229306256531)
  ·
    refine ⟨107715773146696843959384797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71810515431131229306256531 107715773146696843959384797)
    ·
      refine ⟨40393414930011316484769299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107715773146696843959384797 40393414930011316484769299)
      ·
        refine ⟨60590122395016974727153949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40393414930011316484769299 60590122395016974727153949)
        ·
          refine ⟨22721295898131365522682731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60590122395016974727153949 22721295898131365522682731)
          ·
            refine ⟨34081943847197048284024097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22721295898131365522682731 34081943847197048284024097)
            ·
              refine ⟨25561457885397786213018073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34081943847197048284024097 25561457885397786213018073)
              ·
                refine ⟨19171093414048339659763555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25561457885397786213018073 19171093414048339659763555)
                ·
                  refine ⟨28756640121072509489645333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19171093414048339659763555 28756640121072509489645333)
                  ·
                    refine ⟨1347967505675273882327125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28756640121072509489645333 1347967505675273882327125)
                    ·
                      rfl

theorem cell22_3937736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_3937736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937736 prefixEnd_3937736 := by exact prefixLift 3937736
  have htrace : WordTrace (prefixWord ++ tailWord_3937736) baseStart_3937736 baseEnd_3937736 := by
    simpa [prefixWord, tailWord_3937736, baseEnd_3937736] using wordTrace_append hprefix tailTrace_3937736
  have hstable : (prefixWord ++ tailWord_3937736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937736).length < 2 ^ (prefixWord ++ tailWord_3937736).sum := by decide
  have hdescent : baseEnd_3937736 < baseStart_3937736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937738 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_3937738 : Nat := 118140960795 + 3937738 * 2 ^ 59
def prefixEnd_3937738 : Nat := 4983230072969 + 3 ^ 40 * 3937738 * 2
def baseEnd_3937738 : Nat := 1347968190316146543777119

theorem tailTrace_3937738 : CollatzResearch.WordTrace tailWord_3937738 prefixEnd_3937738 1347968190316146543777119 := by
  unfold tailWord_3937738
  simp only [CollatzResearch.WordTrace]
  refine ⟨35905275952063803238521467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95747402538836808636057245 35905275952063803238521467)
  ·
    refine ⟨53857913928095704857782201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35905275952063803238521467 53857913928095704857782201)
    ·
      refine ⟨40393435446071778643336651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53857913928095704857782201 40393435446071778643336651)
      ·
        refine ⟨60590153169107667965004977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40393435446071778643336651 60590153169107667965004977)
        ·
          refine ⟨45442614876830750973753733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60590153169107667965004977 45442614876830750973753733)
          ·
            refine ⟨8520490289405765807578825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45442614876830750973753733 8520490289405765807578825)
            ·
              refine ⟨6390367717054324355684119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8520490289405765807578825 6390367717054324355684119)
              ·
                refine ⟨9585551575581486533526179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6390367717054324355684119 9585551575581486533526179)
                ·
                  refine ⟨14378327363372229800289269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9585551575581486533526179 14378327363372229800289269)
                  ·
                    refine ⟨1347968190316146543777119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14378327363372229800289269 1347968190316146543777119)
                    ·
                      rfl

theorem cell22_3937738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_3937738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937738 prefixEnd_3937738 := by exact prefixLift 3937738
  have htrace : WordTrace (prefixWord ++ tailWord_3937738) baseStart_3937738 baseEnd_3937738 := by
    simpa [prefixWord, tailWord_3937738, baseEnd_3937738] using wordTrace_append hprefix tailTrace_3937738
  have hstable : (prefixWord ++ tailWord_3937738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937738).length < 2 ^ (prefixWord ++ tailWord_3937738).sum := by decide
  have hdescent : baseEnd_3937738 < baseStart_3937738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937753 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 2, 4]
def baseStart_3937753 : Nat := 118140960795 + 3937753 * 2 ^ 59
def prefixEnd_3937753 : Nat := 4983230072969 + 3 ^ 40 * 3937753 * 2
def baseEnd_3937753 : Nat := 1347973325122691504652073

theorem tailTrace_3937753 : CollatzResearch.WordTrace tailWord_3937753 prefixEnd_3937753 1347973325122691504652073 := by
  unfold tailWord_3937753
  simp only [CollatzResearch.WordTrace]
  refine ⟨143621650903200870515881913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95747767268800580343921275 143621650903200870515881913)
  ·
    refine ⟨107716238177400652886911435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143621650903200870515881913 107716238177400652886911435)
    ·
      refine ⟨161574357266100979330367153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107716238177400652886911435 161574357266100979330367153)
      ·
        refine ⟨121180767949575734497775365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161574357266100979330367153 121180767949575734497775365)
        ·
          refine ⟨22721393990545450218332881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121180767949575734497775365 22721393990545450218332881)
          ·
            refine ⟨17041045492909087663749661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22721393990545450218332881 17041045492909087663749661)
            ·
              refine ⟨6390392059840907873906123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17041045492909087663749661 6390392059840907873906123)
              ·
                refine ⟨9585588089761361810859185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6390392059840907873906123 9585588089761361810859185)
                ·
                  refine ⟨7189191067321021358144389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9585588089761361810859185 7189191067321021358144389)
                  ·
                    refine ⟨1347973325122691504652073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7189191067321021358144389 1347973325122691504652073)
                    ·
                      rfl

theorem cell22_3937753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_3937753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937753 prefixEnd_3937753 := by exact prefixLift 3937753
  have htrace : WordTrace (prefixWord ++ tailWord_3937753) baseStart_3937753 baseEnd_3937753 := by
    simpa [prefixWord, tailWord_3937753, baseEnd_3937753] using wordTrace_append hprefix tailTrace_3937753
  have hstable : (prefixWord ++ tailWord_3937753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937753).length < 2 ^ (prefixWord ++ tailWord_3937753).sum := by decide
  have hdescent : baseEnd_3937753 < baseStart_3937753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937834 : List Nat := [3, 1, 4, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3937834 : Nat := 118140960795 + 3937834 * 2 ^ 59
def prefixEnd_3937834 : Nat := 4983230072969 + 3 ^ 40 * 3937834 * 2
def baseEnd_3937834 : Nat := 1348001053078034293376825

theorem tailTrace_3937834 : CollatzResearch.WordTrace tailWord_3937834 prefixEnd_3937834 1348001053078034293376825 := by
  unfold tailWord_3937834
  simp only [CollatzResearch.WordTrace]
  refine ⟨35906151303976855337395139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95749736810604947566387037 35906151303976855337395139)
  ·
    refine ⟨53859226955965283006092709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35906151303976855337395139 53859226955965283006092709)
    ·
      refine ⟨10098605054243490563642383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53859226955965283006092709 10098605054243490563642383)
      ·
        refine ⟨15147907581365235845463575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10098605054243490563642383 15147907581365235845463575)
        ·
          refine ⟨22721861372047853768195363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15147907581365235845463575 22721861372047853768195363)
          ·
            refine ⟨34082792058071780652293045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22721861372047853768195363 34082792058071780652293045)
            ·
              refine ⟨3195261755444229436152473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34082792058071780652293045 3195261755444229436152473)
              ·
                refine ⟨2396446316583172077114355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195261755444229436152473 2396446316583172077114355)
                ·
                  refine ⟨3594669474874758115671533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396446316583172077114355 3594669474874758115671533)
                  ·
                    refine ⟨1348001053078034293376825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3594669474874758115671533 1348001053078034293376825)
                    ·
                      rfl

theorem cell22_3937834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3937834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937834 prefixEnd_3937834 := by exact prefixLift 3937834
  have htrace : WordTrace (prefixWord ++ tailWord_3937834) baseStart_3937834 baseEnd_3937834 := by
    simpa [prefixWord, tailWord_3937834, baseEnd_3937834] using wordTrace_append hprefix tailTrace_3937834
  have hstable : (prefixWord ++ tailWord_3937834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937834).length < 2 ^ (prefixWord ++ tailWord_3937834).sum := by decide
  have hdescent : baseEnd_3937834 < baseStart_3937834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937873 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_3937873 : Nat := 118140960795 + 3937873 * 2 ^ 59
def prefixEnd_3937873 : Nat := 4983230072969 + 3 ^ 40 * 3937873 * 2
def baseEnd_3937873 : Nat := 1348014403575051191651705

theorem tailTrace_3937873 : CollatzResearch.WordTrace tailWord_3937873 prefixEnd_3937873 1348014403575051191651705 := by
  unfold tailWord_3937873
  simp only [CollatzResearch.WordTrace]
  refine ⟨143626027662766131010250273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95750685108510754006833515 143626027662766131010250273)
  ·
    refine ⟨107719520747074598257687705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143626027662766131010250273 107719520747074598257687705)
    ·
      refine ⟨80789640560305948693265779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107719520747074598257687705 80789640560305948693265779)
      ·
        refine ⟨121184460840458923039898669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80789640560305948693265779 121184460840458923039898669)
        ·
          refine ⟨45444172815172096139962001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121184460840458923039898669 45444172815172096139962001)
          ·
            refine ⟨34083129611379072104971501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45444172815172096139962001 34083129611379072104971501)
            ·
              refine ⟨12781173604267152039364313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34083129611379072104971501 12781173604267152039364313)
              ·
                refine ⟨9585880203200364029523235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12781173604267152039364313 9585880203200364029523235)
                ·
                  refine ⟨14378820304800546044284853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9585880203200364029523235 14378820304800546044284853)
                  ·
                    refine ⟨1348014403575051191651705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14378820304800546044284853 1348014403575051191651705)
                    ·
                      rfl

theorem cell22_3937873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_3937873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937873 prefixEnd_3937873 := by exact prefixLift 3937873
  have htrace : WordTrace (prefixWord ++ tailWord_3937873) baseStart_3937873 baseEnd_3937873 := by
    simpa [prefixWord, tailWord_3937873, baseEnd_3937873] using wordTrace_append hprefix tailTrace_3937873
  have hstable : (prefixWord ++ tailWord_3937873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937873).length < 2 ^ (prefixWord ++ tailWord_3937873).sum := by decide
  have hdescent : baseEnd_3937873 < baseStart_3937873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937885 : List Nat := [1, 4, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3937885 : Nat := 118140960795 + 3937885 * 2 ^ 59
def prefixEnd_3937885 : Nat := 4983230072969 + 3 ^ 40 * 3937885 * 2
def baseEnd_3937885 : Nat := 1348018511420287160351669

theorem tailTrace_3937885 : CollatzResearch.WordTrace tailWord_3937885 prefixEnd_3937885 1348018511420287160351669 := by
  unfold tailWord_3937885
  simp only [CollatzResearch.WordTrace]
  refine ⟨143626465338722657059687109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95750976892481771373124739 143626465338722657059687109)
  ·
    refine ⟨26929962251010498198691333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143626465338722657059687109 26929962251010498198691333)
    ·
      refine ⟨5049367922064468412254625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26929962251010498198691333 5049367922064468412254625)
      ·
        refine ⟨3787025941548351309190969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5049367922064468412254625 3787025941548351309190969)
        ·
          refine ⟨2840269456161263481893227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787025941548351309190969 2840269456161263481893227)
          ·
            refine ⟨4260404184241895222839841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840269456161263481893227 4260404184241895222839841)
            ·
              refine ⟨3195303138181421417129881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4260404184241895222839841 3195303138181421417129881)
              ·
                refine ⟨2396477353636066062847411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195303138181421417129881 2396477353636066062847411)
                ·
                  refine ⟨3594716030454099094271117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396477353636066062847411 3594716030454099094271117)
                  ·
                    refine ⟨1348018511420287160351669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3594716030454099094271117 1348018511420287160351669)
                    ·
                      rfl

theorem cell22_3937885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3937885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937885 prefixEnd_3937885 := by exact prefixLift 3937885
  have htrace : WordTrace (prefixWord ++ tailWord_3937885) baseStart_3937885 baseEnd_3937885 := by
    simpa [prefixWord, tailWord_3937885, baseEnd_3937885] using wordTrace_append hprefix tailTrace_3937885
  have hstable : (prefixWord ++ tailWord_3937885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937885).length < 2 ^ (prefixWord ++ tailWord_3937885).sum := by decide
  have hdescent : baseEnd_3937885 < baseStart_3937885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937892 : List Nat := [2, 3, 1, 1, 2, 3, 4, 2, 4]
def baseStart_3937892 : Nat := 118140960795 + 3937892 * 2 ^ 59
def prefixEnd_3937892 : Nat := 4983230072969 + 3 ^ 40 * 3937892 * 2
def baseEnd_3937892 : Nat := 449340302554447158475549

theorem tailTrace_3937892 : CollatzResearch.WordTrace tailWord_3937892 prefixEnd_3937892 449340302554447158475549 := by
  unfold tailWord_3937892
  simp only [CollatzResearch.WordTrace]
  refine ⟨71813360324848648627595965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95751147099798198170127953 71813360324848648627595965)
  ·
    refine ⟨26930010121818243235348487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71813360324848648627595965 26930010121818243235348487)
    ·
      refine ⟨40395015182727364853022731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26930010121818243235348487 40395015182727364853022731)
      ·
        refine ⟨60592522774091047279534097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40395015182727364853022731 60592522774091047279534097)
        ·
          refine ⟨45444392080568285459650573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60592522774091047279534097 45444392080568285459650573)
          ·
            refine ⟨17041647030213107047368965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45444392080568285459650573 17041647030213107047368965)
            ·
              refine ⟨3195308818164957571381681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17041647030213107047368965 3195308818164957571381681)
              ·
                refine ⟨2396481613623718178536261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195308818164957571381681 2396481613623718178536261)
                ·
                  refine ⟨449340302554447158475549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396481613623718178536261 449340302554447158475549)
                  ·
                    rfl

theorem cell22_3937892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_3937892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937892 prefixEnd_3937892 := by exact prefixLift 3937892
  have htrace : WordTrace (prefixWord ++ tailWord_3937892) baseStart_3937892 baseEnd_3937892 := by
    simpa [prefixWord, tailWord_3937892, baseEnd_3937892] using wordTrace_append hprefix tailTrace_3937892
  have hstable : (prefixWord ++ tailWord_3937892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937892).length < 2 ^ (prefixWord ++ tailWord_3937892).sum := by decide
  have hdescent : baseEnd_3937892 < baseStart_3937892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3937952 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 3, 3]
def baseStart_3937952 : Nat := 118140960795 + 3937952 * 2 ^ 59
def prefixEnd_3937952 : Nat := 4983230072969 + 3 ^ 40 * 3937952 * 2
def baseEnd_3937952 : Nat := 1348041446889521318926463

theorem tailTrace_3937952 : CollatzResearch.WordTrace tailWord_3937952 prefixEnd_3937952 1348041446889521318926463 := by
  unfold tailWord_3937952
  simp only [CollatzResearch.WordTrace]
  refine ⟨71814454514739963751188055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95752606019653285001584073 71814454514739963751188055)
  ·
    refine ⟨107721681772109945626782083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71814454514739963751188055 107721681772109945626782083)
    ·
      refine ⟨161582522658164918440173125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107721681772109945626782083 161582522658164918440173125)
      ·
        refine ⟨30296722998405922207532461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161582522658164918440173125 30296722998405922207532461)
        ·
          refine ⟨11361271124402220827824673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30296722998405922207532461 11361271124402220827824673)
          ·
            refine ⟨8520953343301665620868505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11361271124402220827824673 8520953343301665620868505)
            ·
              refine ⟨6390715007476249215651379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8520953343301665620868505 6390715007476249215651379)
              ·
                refine ⟨9586072511214373823477069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6390715007476249215651379 9586072511214373823477069)
                ·
                  refine ⟨3594777191705390183803901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9586072511214373823477069 3594777191705390183803901)
                  ·
                    refine ⟨1348041446889521318926463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3594777191705390183803901 1348041446889521318926463)
                    ·
                      rfl

theorem cell22_3937952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3, 3].length) (baseStart_3937952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3937952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3937952 prefixEnd_3937952 := by exact prefixLift 3937952
  have htrace : WordTrace (prefixWord ++ tailWord_3937952) baseStart_3937952 baseEnd_3937952 := by
    simpa [prefixWord, tailWord_3937952, baseEnd_3937952] using wordTrace_append hprefix tailTrace_3937952
  have hstable : (prefixWord ++ tailWord_3937952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3937952).length < 2 ^ (prefixWord ++ tailWord_3937952).sum := by decide
  have hdescent : baseEnd_3937952 < baseStart_3937952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3937952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938010 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_3938010 : Nat := 118140960795 + 3938010 * 2 ^ 59
def prefixEnd_3938010 : Nat := 4983230072969 + 3 ^ 40 * 3938010 * 2
def baseEnd_3938010 : Nat := 449353767158276166992095

theorem tailTrace_3938010 : CollatzResearch.WordTrace tailWord_3938010 prefixEnd_3938010 449353767158276166992095 := by
  unfold tailWord_3938010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35907756115817450851996871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95754016308846535605324989 35907756115817450851996871)
  ·
    refine ⟨53861634173726176277995307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35907756115817450851996871 53861634173726176277995307)
    ·
      refine ⟨80792451260589264416992961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53861634173726176277995307 80792451260589264416992961)
      ·
        refine ⟨60594338445441948312744721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80792451260589264416992961 60594338445441948312744721)
        ·
          refine ⟨45445753834081461234558541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60594338445441948312744721 45445753834081461234558541)
          ·
            refine ⟨17042157687780547962959453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45445753834081461234558541 17042157687780547962959453)
            ·
              refine ⟨6390809132917705486109795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17042157687780547962959453 6390809132917705486109795)
              ·
                refine ⟨9586213699376558229164693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6390809132917705486109795 9586213699376558229164693)
                ·
                  refine ⟨449353767158276166992095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9586213699376558229164693 449353767158276166992095)
                  ·
                    rfl

theorem cell22_3938010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_3938010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938010 prefixEnd_3938010 := by exact prefixLift 3938010
  have htrace : WordTrace (prefixWord ++ tailWord_3938010) baseStart_3938010 baseEnd_3938010 := by
    simpa [prefixWord, tailWord_3938010, baseEnd_3938010] using wordTrace_append hprefix tailTrace_3938010
  have hstable : (prefixWord ++ tailWord_3938010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938010).length < 2 ^ (prefixWord ++ tailWord_3938010).sum := by decide
  have hdescent : baseEnd_3938010 < baseStart_3938010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938029 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_3938029 : Nat := 118140960795 + 3938029 * 2 ^ 59
def prefixEnd_3938029 : Nat := 4983230072969 + 3 ^ 40 * 3938029 * 2
def baseEnd_3938029 : Nat := 1348067805563118784751227

theorem tailTrace_3938029 : CollatzResearch.WordTrace tailWord_3938029 prefixEnd_3938029 1348067805563118784751227 := by
  unfold tailWord_3938029
  simp only [CollatzResearch.WordTrace]
  refine ⟨143631717450200969652929141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95754478300133979768619427 143631717450200969652929141)
  ·
    refine ⟨13465473510956340904962107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143631717450200969652929141 13465473510956340904962107)
    ·
      refine ⟨20198210266434511357443161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13465473510956340904962107 20198210266434511357443161)
      ·
        refine ⟨15148657699825883518082371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20198210266434511357443161 15148657699825883518082371)
        ·
          refine ⟨22722986549738825277123557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15148657699825883518082371 22722986549738825277123557)
          ·
            refine ⟨4260559978076029739460667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22722986549738825277123557 4260559978076029739460667)
            ·
              refine ⟨6390839967114044609191001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4260559978076029739460667 6390839967114044609191001)
              ·
                refine ⟨4793129975335533456893251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6390839967114044609191001 4793129975335533456893251)
                ·
                  refine ⟨7189694963003300185339877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793129975335533456893251 7189694963003300185339877)
                  ·
                    refine ⟨1348067805563118784751227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7189694963003300185339877 1348067805563118784751227)
                    ·
                      rfl

theorem cell22_3938029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_3938029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938029 prefixEnd_3938029 := by exact prefixLift 3938029
  have htrace : WordTrace (prefixWord ++ tailWord_3938029) baseStart_3938029 baseEnd_3938029 := by
    simpa [prefixWord, tailWord_3938029, baseEnd_3938029] using wordTrace_append hprefix tailTrace_3938029
  have hstable : (prefixWord ++ tailWord_3938029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938029).length < 2 ^ (prefixWord ++ tailWord_3938029).sum := by decide
  have hdescent : baseEnd_3938029 < baseStart_3938029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938046 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_3938046 : Nat := 118140960795 + 3938046 * 2 ^ 59
def prefixEnd_3938046 : Nat := 4983230072969 + 3 ^ 40 * 3938046 * 2
def baseEnd_3938046 : Nat := 1348073625010536407076175

theorem tailTrace_3938046 : CollatzResearch.WordTrace tailWord_3938046 prefixEnd_3938046 1348073625010536407076175 := by
  unfold tailWord_3938046
  simp only [CollatzResearch.WordTrace]
  refine ⟨17954042186392422694537249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95754891660759587704198661 17954042186392422694537249)
  ·
    refine ⟨13465531639794317020902937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17954042186392422694537249 13465531639794317020902937)
    ·
      refine ⟨10099148729845737765677203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13465531639794317020902937 10099148729845737765677203)
      ·
        refine ⟨15148723094768606648515805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10099148729845737765677203 15148723094768606648515805)
        ·
          refine ⟨5680771160538227493193427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15148723094768606648515805 5680771160538227493193427)
          ·
            refine ⟨8521156740807341239790141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5680771160538227493193427 8521156740807341239790141)
            ·
              refine ⟨3195433777802752964921303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8521156740807341239790141 3195433777802752964921303)
              ·
                refine ⟨4793150666704129447381955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3195433777802752964921303 4793150666704129447381955)
                ·
                  refine ⟨7189726000056194171072933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793150666704129447381955 7189726000056194171072933)
                  ·
                    refine ⟨1348073625010536407076175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7189726000056194171072933 1348073625010536407076175)
                    ·
                      rfl

theorem cell22_3938046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_3938046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938046 prefixEnd_3938046 := by exact prefixLift 3938046
  have htrace : WordTrace (prefixWord ++ tailWord_3938046) baseStart_3938046 baseEnd_3938046 := by
    simpa [prefixWord, tailWord_3938046, baseEnd_3938046] using wordTrace_append hprefix tailTrace_3938046
  have hstable : (prefixWord ++ tailWord_3938046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938046).length < 2 ^ (prefixWord ++ tailWord_3938046).sum := by decide
  have hdescent : baseEnd_3938046 < baseStart_3938046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938055 : List Nat := [1, 1, 4, 4, 2, 10]
def baseStart_3938055 : Nat := 118140960795 + 3938055 * 2 ^ 59
def prefixEnd_3938055 : Nat := 4983230072969 + 3 ^ 40 * 3938055 * 2
def baseEnd_3938055 : Nat := 16642922294993375106187

theorem tailTrace_3938055 : CollatzResearch.WordTrace tailWord_3938055 prefixEnd_3938055 16642922294993375106187 := by
  unfold tailWord_3938055
  simp only [CollatzResearch.WordTrace]
  refine ⟨143632665748106776093375619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95755110498737850728917079 143632665748106776093375619)
  ·
    refine ⟨215448998622160164140063429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143632665748106776093375619 215448998622160164140063429)
    ·
      refine ⟨40396687241655030776261893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215448998622160164140063429 40396687241655030776261893)
      ·
        refine ⟨7574378857810318270549105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40396687241655030776261893 7574378857810318270549105)
        ·
          refine ⟨5680784143357738702911829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7574378857810318270549105 5680784143357738702911829)
          ·
            refine ⟨16642922294993375106187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5680784143357738702911829 16642922294993375106187)
            ·
              rfl

theorem cell22_3938055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 10].length) (baseStart_3938055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938055 prefixEnd_3938055 := by exact prefixLift 3938055
  have htrace : WordTrace (prefixWord ++ tailWord_3938055) baseStart_3938055 baseEnd_3938055 := by
    simpa [prefixWord, tailWord_3938055, baseEnd_3938055] using wordTrace_append hprefix tailTrace_3938055
  have hstable : (prefixWord ++ tailWord_3938055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938055).length < 2 ^ (prefixWord ++ tailWord_3938055).sum := by decide
  have hdescent : baseEnd_3938055 < baseStart_3938055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938104 : List Nat := [2, 1, 2, 1, 3, 3, 1, 5, 1, 3]
def baseStart_3938104 : Nat := 118140960795 + 3938104 * 2 ^ 59
def prefixEnd_3938104 : Nat := 4983230072969 + 3 ^ 40 * 3938104 * 2
def baseEnd_3938104 : Nat := 1348093479595843589125997

theorem tailTrace_3938104 : CollatzResearch.WordTrace tailWord_3938104 prefixEnd_3938104 1348093479595843589125997 := by
  unfold tailWord_3938104
  simp only [CollatzResearch.WordTrace]
  refine ⟨71817226462464628730954683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95756301949952838307939577 71817226462464628730954683)
  ·
    refine ⟨107725839693696943096432025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71817226462464628730954683 107725839693696943096432025)
    ·
      refine ⟨80794379770272707322324019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107725839693696943096432025 80794379770272707322324019)
      ·
        refine ⟨121191569655409060983486029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80794379770272707322324019 121191569655409060983486029)
        ·
          refine ⟨45446838620778397868807261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121191569655409060983486029 45446838620778397868807261)
          ·
            refine ⟨17042564482791899200802723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45446838620778397868807261 17042564482791899200802723)
            ·
              refine ⟨25563846724187848801204085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17042564482791899200802723 25563846724187848801204085)
              ·
                refine ⟨2396610630392610825112883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25563846724187848801204085 2396610630392610825112883)
                ·
                  refine ⟨3594915945588916237669325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396610630392610825112883 3594915945588916237669325)
                  ·
                    refine ⟨1348093479595843589125997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3594915945588916237669325 1348093479595843589125997)
                    ·
                      rfl

theorem cell22_3938104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_3938104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938104 prefixEnd_3938104 := by exact prefixLift 3938104
  have htrace : WordTrace (prefixWord ++ tailWord_3938104) baseStart_3938104 baseEnd_3938104 := by
    simpa [prefixWord, tailWord_3938104, baseEnd_3938104] using wordTrace_append hprefix tailTrace_3938104
  have hstable : (prefixWord ++ tailWord_3938104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938104).length < 2 ^ (prefixWord ++ tailWord_3938104).sum := by decide
  have hdescent : baseEnd_3938104 < baseStart_3938104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938115 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 2, 5]
def baseStart_3938115 : Nat := 118140960795 + 3938115 * 2 ^ 59
def prefixEnd_3938115 : Nat := 4983230072969 + 3 ^ 40 * 3938115 * 2
def baseEnd_3938115 : Nat := 1348097245120643227100963

theorem tailTrace_3938115 : CollatzResearch.WordTrace tailWord_3938115 prefixEnd_3938115 1348097245120643227100963 := by
  unfold tailWord_3938115
  simp only [CollatzResearch.WordTrace]
  refine ⟨143634854127889406340559799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95756569418592937560373199 143634854127889406340559799)
  ·
    refine ⟨215452281191834109510839699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143634854127889406340559799 215452281191834109510839699)
    ·
      refine ⟨323178421787751164266259549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215452281191834109510839699 323178421787751164266259549)
      ·
        refine ⟨121191908170406686599847331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323178421787751164266259549 121191908170406686599847331)
        ·
          refine ⟨181787862255610029899770997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121191908170406686599847331 181787862255610029899770997)
          ·
            refine ⟨17042612086463440303103531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181787862255610029899770997 17042612086463440303103531)
            ·
              refine ⟨25563918129695160454655297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17042612086463440303103531 25563918129695160454655297)
              ·
                refine ⟨19172938597271370340991473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25563918129695160454655297 19172938597271370340991473)
                ·
                  refine ⟨14379703947953527755743605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19172938597271370340991473 14379703947953527755743605)
                  ·
                    refine ⟨1348097245120643227100963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14379703947953527755743605 1348097245120643227100963)
                    ·
                      rfl

theorem cell22_3938115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_3938115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938115 prefixEnd_3938115 := by exact prefixLift 3938115
  have htrace : WordTrace (prefixWord ++ tailWord_3938115) baseStart_3938115 baseEnd_3938115 := by
    simpa [prefixWord, tailWord_3938115, baseEnd_3938115] using wordTrace_append hprefix tailTrace_3938115
  have hstable : (prefixWord ++ tailWord_3938115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938115).length < 2 ^ (prefixWord ++ tailWord_3938115).sum := by decide
  have hdescent : baseEnd_3938115 < baseStart_3938115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938132 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_3938132 : Nat := 118140960795 + 3938132 * 2 ^ 59
def prefixEnd_3938132 : Nat := 4983230072969 + 3 ^ 40 * 3938132 * 2
def baseEnd_3938132 : Nat := 1348103064568060849425911

theorem tailTrace_3938132 : CollatzResearch.WordTrace tailWord_3938132 prefixEnd_3938132 1348103064568060849425911 := by
  unfold tailWord_3938132
  simp only [CollatzResearch.WordTrace]
  refine ⟨71817737084413909121964325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95756982779218545495952433 71817737084413909121964325)
  ·
    refine ⟨13465825703327607960368311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71817737084413909121964325 13465825703327607960368311)
    ·
      refine ⟨20198738554991411940552467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13465825703327607960368311 20198738554991411940552467)
      ·
        refine ⟨30298107832487117910828701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20198738554991411940552467 30298107832487117910828701)
        ·
          refine ⟨11361790437182669216560763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30298107832487117910828701 11361790437182669216560763)
          ·
            refine ⟨17042685655774003824841145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11361790437182669216560763 17042685655774003824841145)
            ·
              refine ⟨12782014241830502868630859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17042685655774003824841145 12782014241830502868630859)
              ·
                refine ⟨19173021362745754302946289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12782014241830502868630859 19173021362745754302946289)
                ·
                  refine ⟨14379766022059315727209717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19173021362745754302946289 14379766022059315727209717)
                  ·
                    refine ⟨1348103064568060849425911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14379766022059315727209717 1348103064568060849425911)
                    ·
                      rfl

theorem cell22_3938132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_3938132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938132 prefixEnd_3938132 := by exact prefixLift 3938132
  have htrace : WordTrace (prefixWord ++ tailWord_3938132) baseStart_3938132 baseEnd_3938132 := by
    simpa [prefixWord, tailWord_3938132, baseEnd_3938132] using wordTrace_append hprefix tailTrace_3938132
  have hstable : (prefixWord ++ tailWord_3938132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938132).length < 2 ^ (prefixWord ++ tailWord_3938132).sum := by decide
  have hdescent : baseEnd_3938132 < baseStart_3938132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938145 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 6]
def baseStart_3938145 : Nat := 118140960795 + 3938145 * 2 ^ 59
def prefixEnd_3938145 : Nat := 4983230072969 + 3 ^ 40 * 3938145 * 2
def baseEnd_3938145 : Nat := 449369171577911049616957

theorem tailTrace_3938145 : CollatzResearch.WordTrace tailWord_3938145 prefixEnd_3938145 449369171577911049616957 := by
  unfold tailWord_3938145
  simp only [CollatzResearch.WordTrace]
  refine ⟨143635948317780721464151889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95757298878520480976101259 143635948317780721464151889)
  ·
    refine ⟨107726961238335541098113917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143635948317780721464151889 107726961238335541098113917)
    ·
      refine ⟨40397610464375827911792719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107726961238335541098113917 40397610464375827911792719)
      ·
        refine ⟨60596415696563741867689079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40397610464375827911792719 60596415696563741867689079)
        ·
          refine ⟨90894623544845612801533619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60596415696563741867689079 90894623544845612801533619)
          ·
            refine ⟨136341935317268419202300429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90894623544845612801533619 136341935317268419202300429)
            ·
              refine ⟨51128225743975657200862661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136341935317268419202300429 51128225743975657200862661)
              ·
                refine ⟨9586542326995435725161749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51128225743975657200862661 9586542326995435725161749)
                ·
                  refine ⟨449369171577911049616957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9586542326995435725161749 449369171577911049616957)
                  ·
                    rfl

theorem cell22_3938145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_3938145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938145 prefixEnd_3938145 := by exact prefixLift 3938145
  have htrace : WordTrace (prefixWord ++ tailWord_3938145) baseStart_3938145 baseEnd_3938145 := by
    simpa [prefixWord, tailWord_3938145, baseEnd_3938145] using wordTrace_append hprefix tailTrace_3938145
  have hstable : (prefixWord ++ tailWord_3938145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938145).length < 2 ^ (prefixWord ++ tailWord_3938145).sum := by decide
  have hdescent : baseEnd_3938145 < baseStart_3938145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938160 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_3938160 : Nat := 118140960795 + 3938160 * 2 ^ 59
def prefixEnd_3938160 : Nat := 4983230072969 + 3 ^ 40 * 3938160 * 2
def baseEnd_3938160 : Nat := 1348112649540278109725825

theorem tailTrace_3938160 : CollatzResearch.WordTrace tailWord_3938160 prefixEnd_3938160 1348112649540278109725825 := by
  unfold tailWord_3938160
  simp only [CollatzResearch.WordTrace]
  refine ⟨71818247706363189512973967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95757663608484252683965289 71818247706363189512973967)
  ·
    refine ⟨107727371559544784269460951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71818247706363189512973967 107727371559544784269460951)
    ·
      refine ⟨161591057339317176404191427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107727371559544784269460951 161591057339317176404191427)
      ·
        refine ⟨242386586008975764606287141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161591057339317176404191427 242386586008975764606287141)
        ·
          refine ⟨45447484876682955863678839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242386586008975764606287141 45447484876682955863678839)
          ·
            refine ⟨68171227315024433795518259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45447484876682955863678839 68171227315024433795518259)
            ·
              refine ⟨102256840972536650693277389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68171227315024433795518259 102256840972536650693277389)
              ·
                refine ⟨38346315364701244009979021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102256840972536650693277389 38346315364701244009979021)
                ·
                  refine ⟨14379868261762966503742133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38346315364701244009979021 14379868261762966503742133)
                  ·
                    refine ⟨1348112649540278109725825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14379868261762966503742133 1348112649540278109725825)
                    ·
                      rfl

theorem cell22_3938160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_3938160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938160 prefixEnd_3938160 := by exact prefixLift 3938160
  have htrace : WordTrace (prefixWord ++ tailWord_3938160) baseStart_3938160 baseEnd_3938160 := by
    simpa [prefixWord, tailWord_3938160, baseEnd_3938160] using wordTrace_append hprefix tailTrace_3938160
  have hstable : (prefixWord ++ tailWord_3938160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938160).length < 2 ^ (prefixWord ++ tailWord_3938160).sum := by decide
  have hdescent : baseEnd_3938160 < baseStart_3938160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938198 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3938198 : Nat := 118140960795 + 3938198 * 2 ^ 59
def prefixEnd_3938198 : Nat := 4983230072969 + 3 ^ 40 * 3938198 * 2
def baseEnd_3938198 : Nat := 1348125657716858677275709

theorem tailTrace_3938198 : CollatzResearch.WordTrace tailWord_3938198 prefixEnd_3938198 1348125657716858677275709 := by
  unfold tailWord_3938198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977367586661794469739453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95758587591059141010554165 8977367586661794469739453)
  ·
    refine ⟨3366512844998172926152295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8977367586661794469739453 3366512844998172926152295)
    ·
      refine ⟨5049769267497259389228443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3366512844998172926152295 5049769267497259389228443)
      ·
        refine ⟨7574653901245889083842665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5049769267497259389228443 7574653901245889083842665)
        ·
          refine ⟨5680990425934416812881999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7574653901245889083842665 5680990425934416812881999)
          ·
            refine ⟨8521485638901625219322999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5680990425934416812881999 8521485638901625219322999)
            ·
              refine ⟨12782228458352437828984499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8521485638901625219322999 12782228458352437828984499)
              ·
                refine ⟨19173342687528656743476749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12782228458352437828984499 19173342687528656743476749)
                ·
                  refine ⟨7190003507823246278803781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19173342687528656743476749 7190003507823246278803781)
                  ·
                    refine ⟨1348125657716858677275709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7190003507823246278803781 1348125657716858677275709)
                    ·
                      rfl

theorem cell22_3938198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3938198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938198 prefixEnd_3938198 := by exact prefixLift 3938198
  have htrace : WordTrace (prefixWord ++ tailWord_3938198) baseStart_3938198 baseEnd_3938198 := by
    simpa [prefixWord, tailWord_3938198, baseEnd_3938198] using wordTrace_append hprefix tailTrace_3938198
  have hstable : (prefixWord ++ tailWord_3938198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938198).length < 2 ^ (prefixWord ++ tailWord_3938198).sum := by decide
  have hdescent : baseEnd_3938198 < baseStart_3938198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938220 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_3938220 : Nat := 118140960795 + 3938220 * 2 ^ 59
def prefixEnd_3938220 : Nat := 4983230072969 + 3 ^ 40 * 3938220 * 2
def baseEnd_3938220 : Nat := 1348133188766457953225641

theorem tailTrace_3938220 : CollatzResearch.WordTrace tailWord_3938220 prefixEnd_3938220 1348133188766457953225641 := by
  unfold tailWord_3938220
  simp only [CollatzResearch.WordTrace]
  refine ⟨71819341896254504636566057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95759122528339339515421409 71819341896254504636566057)
  ·
    refine ⟨53864506422190878477424543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71819341896254504636566057 53864506422190878477424543)
    ·
      refine ⟨80796759633286317716136815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53864506422190878477424543 80796759633286317716136815)
      ·
        refine ⟨121195139449929476574205223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80796759633286317716136815 121195139449929476574205223)
        ·
          refine ⟨181792709174894214861307835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121195139449929476574205223 181792709174894214861307835)
          ·
            refine ⟨272689063762341322291961753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181792709174894214861307835 272689063762341322291961753)
            ·
              refine ⟨204516797821755991718971315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272689063762341322291961753 204516797821755991718971315)
              ·
                refine ⟨306775196732633987578456973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204516797821755991718971315 306775196732633987578456973)
                ·
                  refine ⟨115040698774737745341921365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306775196732633987578456973 115040698774737745341921365)
                  ·
                    refine ⟨1348133188766457953225641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115040698774737745341921365 1348133188766457953225641)
                    ·
                      rfl

theorem cell22_3938220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_3938220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938220 prefixEnd_3938220 := by exact prefixLift 3938220
  have htrace : WordTrace (prefixWord ++ tailWord_3938220) baseStart_3938220 baseEnd_3938220 := by
    simpa [prefixWord, tailWord_3938220, baseEnd_3938220] using wordTrace_append hprefix tailTrace_3938220
  have hstable : (prefixWord ++ tailWord_3938220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938220).length < 2 ^ (prefixWord ++ tailWord_3938220).sum := by decide
  have hdescent : baseEnd_3938220 < baseStart_3938220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938237 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_3938237 : Nat := 118140960795 + 3938237 * 2 ^ 59
def prefixEnd_3938237 : Nat := 4983230072969 + 3 ^ 40 * 3938237 * 2
def baseEnd_3938237 : Nat := 1348139008213875575550589

theorem tailTrace_3938237 : CollatzResearch.WordTrace tailWord_3938237 prefixEnd_3938237 1348139008213875575550589 := by
  unfold tailWord_3938237
  simp only [CollatzResearch.WordTrace]
  refine ⟨143639303833447421176500965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95759535888964947451000643 143639303833447421176500965)
  ·
    refine ⟨26932369468771391470593931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143639303833447421176500965 26932369468771391470593931)
    ·
      refine ⟨40398554203157087205890897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26932369468771391470593931 40398554203157087205890897)
      ·
        refine ⟨30298915652367815404418173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40398554203157087205890897 30298915652367815404418173)
        ·
          refine ⟨11362093369637930776656815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30298915652367815404418173 11362093369637930776656815)
          ·
            refine ⟨17043140054456896164985223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11362093369637930776656815 17043140054456896164985223)
            ·
              refine ⟨25564710081685344247477835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17043140054456896164985223 25564710081685344247477835)
              ·
                refine ⟨38347065122528016371216753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25564710081685344247477835 38347065122528016371216753)
                ·
                  refine ⟨28760298841896012278412565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38347065122528016371216753 28760298841896012278412565)
                  ·
                    refine ⟨1348139008213875575550589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28760298841896012278412565 1348139008213875575550589)
                    ·
                      rfl

theorem cell22_3938237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_3938237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938237 prefixEnd_3938237 := by exact prefixLift 3938237
  have htrace : WordTrace (prefixWord ++ tailWord_3938237) baseStart_3938237 baseEnd_3938237 := by
    simpa [prefixWord, tailWord_3938237, baseEnd_3938237] using wordTrace_append hprefix tailTrace_3938237
  have hstable : (prefixWord ++ tailWord_3938237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938237).length < 2 ^ (prefixWord ++ tailWord_3938237).sum := by decide
  have hdescent : baseEnd_3938237 < baseStart_3938237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938286 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_3938286 : Nat := 118140960795 + 3938286 * 2 ^ 59
def prefixEnd_3938286 : Nat := 4983230072969 + 3 ^ 40 * 3938286 * 2
def baseEnd_3938286 : Nat := 449385260638418593691813

theorem tailTrace_3938286 : CollatzResearch.WordTrace tailWord_3938286 prefixEnd_3938286 449385260638418593691813 := by
  unfold tailWord_3938286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17955136376283737818129339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95760727340179935030023141 17955136376283737818129339)
  ·
    refine ⟨26932704564425606727194009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17955136376283737818129339 26932704564425606727194009)
    ·
      refine ⟨20199528423319205045395507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26932704564425606727194009 20199528423319205045395507)
      ·
        refine ⟨30299292634978807568093261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20199528423319205045395507 30299292634978807568093261)
        ·
          refine ⟨11362234738117052838034973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30299292634978807568093261 11362234738117052838034973)
          ·
            refine ⟨4260838026793894814263115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11362234738117052838034973 4260838026793894814263115)
            ·
              refine ⟨6391257040190842221394673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4260838026793894814263115 6391257040190842221394673)
              ·
                refine ⟨4793442780143131666046005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391257040190842221394673 4793442780143131666046005)
                ·
                  refine ⟨449385260638418593691813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4793442780143131666046005 449385260638418593691813)
                  ·
                    rfl

theorem cell22_3938286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_3938286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938286 prefixEnd_3938286 := by exact prefixLift 3938286
  have htrace : WordTrace (prefixWord ++ tailWord_3938286) baseStart_3938286 baseEnd_3938286 := by
    simpa [prefixWord, tailWord_3938286, baseEnd_3938286] using wordTrace_append hprefix tailTrace_3938286
  have hstable : (prefixWord ++ tailWord_3938286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938286).length < 2 ^ (prefixWord ++ tailWord_3938286).sum := by decide
  have hdescent : baseEnd_3938286 < baseStart_3938286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938297 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 6]
def baseStart_3938297 : Nat := 118140960795 + 3938297 * 2 ^ 59
def prefixEnd_3938297 : Nat := 4983230072969 + 3 ^ 40 * 3938297 * 2
def baseEnd_3938297 : Nat := 449386515813351806350135

theorem tailTrace_3938297 : CollatzResearch.WordTrace tailWord_3938297 prefixEnd_3938297 449386515813351806350135 := by
  unfold tailWord_3938297
  simp only [CollatzResearch.WordTrace]
  refine ⟨143641492213230051423685145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95760994808820034282456763 143641492213230051423685145)
  ·
    refine ⟨107731119159922538567763859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143641492213230051423685145 107731119159922538567763859)
    ·
      refine ⟨161596678739883807851645789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107731119159922538567763859 161596678739883807851645789)
      ·
        refine ⟨60598754527456427944367171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161596678739883807851645789 60598754527456427944367171)
        ·
          refine ⟨90898131791184641916550757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60598754527456427944367171 90898131791184641916550757)
          ·
            refine ⟨17043399710847120359353267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90898131791184641916550757 17043399710847120359353267)
            ·
              refine ⟨25565099566270680539029901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17043399710847120359353267 25565099566270680539029901)
              ·
                refine ⟨9586912337351505202136213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25565099566270680539029901 9586912337351505202136213)
                ·
                  refine ⟨449386515813351806350135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9586912337351505202136213 449386515813351806350135)
                  ·
                    rfl

theorem cell22_3938297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_3938297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938297 prefixEnd_3938297 := by exact prefixLift 3938297
  have htrace : WordTrace (prefixWord ++ tailWord_3938297) baseStart_3938297 baseEnd_3938297 := by
    simpa [prefixWord, tailWord_3938297, baseEnd_3938297] using wordTrace_append hprefix tailTrace_3938297
  have hstable : (prefixWord ++ tailWord_3938297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938297).length < 2 ^ (prefixWord ++ tailWord_3938297).sum := by decide
  have hdescent : baseEnd_3938297 < baseStart_3938297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938324 : List Nat := [2, 4, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3938324 : Nat := 118140960795 + 3938324 * 2 ^ 59
def prefixEnd_3938324 : Nat := 4983230072969 + 3 ^ 40 * 3938324 * 2
def baseEnd_3938324 : Nat := 1348168790091836348625323

theorem tailTrace_3938324 : CollatzResearch.WordTrace tailWord_3938324 prefixEnd_3938324 1348168790091836348625323 := by
  unfold tailWord_3938324
  simp only [CollatzResearch.WordTrace]
  refine ⟨71821238492066117517459013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95761651322754823356612017 71821238492066117517459013)
  ·
    refine ⟨13466482217262397034523565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71821238492066117517459013 13466482217262397034523565)
    ·
      refine ⟨5049930831473398887946337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13466482217262397034523565 5049930831473398887946337)
      ·
        refine ⟨3787448123605049165959753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5049930831473398887946337 3787448123605049165959753)
        ·
          refine ⟨2840586092703786874469815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787448123605049165959753 2840586092703786874469815)
          ·
            refine ⟨4260879139055680311704723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840586092703786874469815 4260879139055680311704723)
            ·
              refine ⟨6391318708583520467557085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4260879139055680311704723 6391318708583520467557085)
              ·
                refine ⟨2396744515718820175333907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6391318708583520467557085 2396744515718820175333907)
                ·
                  refine ⟨3595116773578230263000861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396744515718820175333907 3595116773578230263000861)
                  ·
                    refine ⟨1348168790091836348625323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3595116773578230263000861 1348168790091836348625323)
                    ·
                      rfl

theorem cell22_3938324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3938324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938324 prefixEnd_3938324 := by exact prefixLift 3938324
  have htrace : WordTrace (prefixWord ++ tailWord_3938324) baseStart_3938324 baseEnd_3938324 := by
    simpa [prefixWord, tailWord_3938324, baseEnd_3938324] using wordTrace_append hprefix tailTrace_3938324
  have hstable : (prefixWord ++ tailWord_3938324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938324).length < 2 ^ (prefixWord ++ tailWord_3938324).sum := by decide
  have hdescent : baseEnd_3938324 < baseStart_3938324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938346 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3938346 : Nat := 118140960795 + 3938346 * 2 ^ 59
def prefixEnd_3938346 : Nat := 4983230072969 + 3 ^ 40 * 3938346 * 2
def baseEnd_3938346 : Nat := 1348176321141435624575255

theorem tailTrace_3938346 : CollatzResearch.WordTrace tailWord_3938346 prefixEnd_3938346 1348176321141435624575255 := by
  unfold tailWord_3938346
  simp only [CollatzResearch.WordTrace]
  refine ⟨35910819847513133198054723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95762186260035021861479261 35910819847513133198054723)
  ·
    refine ⟨53866229771269699797082085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35910819847513133198054723 53866229771269699797082085)
    ·
      refine ⟨10099918082113068711952891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53866229771269699797082085 10099918082113068711952891)
      ·
        refine ⟨15149877123169603067929337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10099918082113068711952891 15149877123169603067929337)
        ·
          refine ⟨11362407842377202300947003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15149877123169603067929337 11362407842377202300947003)
          ·
            refine ⟨17043611763565803451420505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11362407842377202300947003 17043611763565803451420505)
            ·
              refine ⟨12782708822674352588565379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17043611763565803451420505 12782708822674352588565379)
              ·
                refine ⟨19174063234011528882848069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12782708822674352588565379 19174063234011528882848069)
                ·
                  refine ⟨3595136856377161665534013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19174063234011528882848069 3595136856377161665534013)
                  ·
                    refine ⟨1348176321141435624575255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3595136856377161665534013 1348176321141435624575255)
                    ·
                      rfl

theorem cell22_3938346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3938346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938346 prefixEnd_3938346 := by exact prefixLift 3938346
  have htrace : WordTrace (prefixWord ++ tailWord_3938346) baseStart_3938346 baseEnd_3938346 := by
    simpa [prefixWord, tailWord_3938346, baseEnd_3938346] using wordTrace_append hprefix tailTrace_3938346
  have hstable : (prefixWord ++ tailWord_3938346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938346).length < 2 ^ (prefixWord ++ tailWord_3938346).sum := by decide
  have hdescent : baseEnd_3938346 < baseStart_3938346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938404 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 5]
def baseStart_3938404 : Nat := 118140960795 + 3938404 * 2 ^ 59
def prefixEnd_3938404 : Nat := 4983230072969 + 3 ^ 40 * 3938404 * 2
def baseEnd_3938404 : Nat := 449398725242247602208359

theorem tailTrace_3938404 : CollatzResearch.WordTrace tailWord_3938404 prefixEnd_3938404 449398725242247602208359 := by
  unfold tailWord_3938404
  simp only [CollatzResearch.WordTrace]
  refine ⟨71822697411921204348915133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95763596549228272465220177 71822697411921204348915133)
  ·
    refine ⟨26933511529470451630843175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71822697411921204348915133 26933511529470451630843175)
    ·
      refine ⟨40400267294205677446264763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26933511529470451630843175 40400267294205677446264763)
      ·
        refine ⟨60600400941308516169397145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40400267294205677446264763 60600400941308516169397145)
        ·
          refine ⟨45450300705981387127047859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60600400941308516169397145 45450300705981387127047859)
          ·
            refine ⟨68175451058972080690571789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45450300705981387127047859 68175451058972080690571789)
            ·
              refine ⟨25565794147114530258964421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68175451058972080690571789 25565794147114530258964421)
              ·
                refine ⟨4793586402583974423555829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25565794147114530258964421 4793586402583974423555829)
                ·
                  refine ⟨449398725242247602208359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4793586402583974423555829 449398725242247602208359)
                  ·
                    rfl

theorem cell22_3938404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_3938404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938404 prefixEnd_3938404 := by exact prefixLift 3938404
  have htrace : WordTrace (prefixWord ++ tailWord_3938404) baseStart_3938404 baseEnd_3938404 := by
    simpa [prefixWord, tailWord_3938404, baseEnd_3938404] using wordTrace_append hprefix tailTrace_3938404
  have hstable : (prefixWord ++ tailWord_3938404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938404).length < 2 ^ (prefixWord ++ tailWord_3938404).sum := by decide
  have hdescent : baseEnd_3938404 < baseStart_3938404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938466 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_3938466 : Nat := 118140960795 + 3938466 * 2 ^ 59
def prefixEnd_3938466 : Nat := 4983230072969 + 3 ^ 40 * 3938466 * 2
def baseEnd_3938466 : Nat := 449405799864598437191629

theorem tailTrace_3938466 : CollatzResearch.WordTrace tailWord_3938466 prefixEnd_3938466 449405799864598437191629 := by
  unfold tailWord_3938466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35911914037404448321646813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95765104099745195524391501 35911914037404448321646813)
  ·
    refine ⟨13466967764026668120617555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35911914037404448321646813 13466967764026668120617555)
    ·
      refine ⟨20200451646040002180926333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13466967764026668120617555 20200451646040002180926333)
      ·
        refine ⟨7575169367265000817847375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20200451646040002180926333 7575169367265000817847375)
        ·
          refine ⟨11362754050897501226771063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7575169367265000817847375 11362754050897501226771063)
          ·
            refine ⟨17044131076346251840156595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11362754050897501226771063 17044131076346251840156595)
            ·
              refine ⟨25566196614519377760234893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17044131076346251840156595 25566196614519377760234893)
              ·
                refine ⟨9587323730444766660088085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25566196614519377760234893 9587323730444766660088085)
                ·
                  refine ⟨449405799864598437191629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9587323730444766660088085 449405799864598437191629)
                  ·
                    rfl

theorem cell22_3938466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_3938466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938466 prefixEnd_3938466 := by exact prefixLift 3938466
  have htrace : WordTrace (prefixWord ++ tailWord_3938466) baseStart_3938466 baseEnd_3938466 := by
    simpa [prefixWord, tailWord_3938466, baseEnd_3938466] using wordTrace_append hprefix tailTrace_3938466
  have hstable : (prefixWord ++ tailWord_3938466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938466).length < 2 ^ (prefixWord ++ tailWord_3938466).sum := by decide
  have hdescent : baseEnd_3938466 < baseStart_3938466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938485 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3938485 : Nat := 118140960795 + 3938485 * 2 ^ 59
def prefixEnd_3938485 : Nat := 4983230072969 + 3 ^ 40 * 3938485 * 2
def baseEnd_3938485 : Nat := 1348223903682085595349829

theorem tailTrace_3938485 : CollatzResearch.WordTrace tailWord_3938485 prefixEnd_3938485 1348223903682085595349829 := by
  unfold tailWord_3938485
  simp only [CollatzResearch.WordTrace]
  refine ⟨143648349136548959531528909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95765566091032639687685939 143648349136548959531528909)
  ·
    refine ⟨53868130926205859824323341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143648349136548959531528909 53868130926205859824323341)
    ·
      refine ⟨20200549097327197434121253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53868130926205859824323341 20200549097327197434121253)
      ·
        refine ⟨3787602955748849518897735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20200549097327197434121253 3787602955748849518897735)
        ·
          refine ⟨5681404433623274278346603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787602955748849518897735 5681404433623274278346603)
          ·
            refine ⟨8522106650434911417519905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681404433623274278346603 8522106650434911417519905)
            ·
              refine ⟨6391579987826183563139929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8522106650434911417519905 6391579987826183563139929)
              ·
                refine ⟨4793684990869637672354947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6391579987826183563139929 4793684990869637672354947)
                ·
                  refine ⟨7190527486304456508532421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4793684990869637672354947 7190527486304456508532421)
                  ·
                    refine ⟨1348223903682085595349829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7190527486304456508532421 1348223903682085595349829)
                    ·
                      rfl

theorem cell22_3938485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3938485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938485 prefixEnd_3938485 := by exact prefixLift 3938485
  have htrace : WordTrace (prefixWord ++ tailWord_3938485) baseStart_3938485 baseEnd_3938485 := by
    simpa [prefixWord, tailWord_3938485, baseEnd_3938485] using wordTrace_append hprefix tailTrace_3938485
  have hstable : (prefixWord ++ tailWord_3938485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938485).length < 2 ^ (prefixWord ++ tailWord_3938485).sum := by decide
  have hdescent : baseEnd_3938485 < baseStart_3938485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938500 : List Nat := [2, 3, 3, 1, 2, 3, 1, 3, 4]
def baseStart_3938500 : Nat := 118140960795 + 3938500 * 2 ^ 59
def prefixEnd_3938500 : Nat := 4983230072969 + 3 ^ 40 * 3938500 * 2
def baseEnd_3938500 : Nat := 449409679496210185408261

theorem tailTrace_3938500 : CollatzResearch.WordTrace tailWord_3938500 prefixEnd_3938500 449409679496210185408261 := by
  unfold tailWord_3938500
  simp only [CollatzResearch.WordTrace]
  refine ⟨71824448115747308546662477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95765930820996411395549969 71824448115747308546662477)
  ·
    refine ⟨26934168043405240704998429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71824448115747308546662477 26934168043405240704998429)
    ·
      refine ⟨10100313016276965264374411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26934168043405240704998429 10100313016276965264374411)
      ·
        refine ⟨15150469524415447896561617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10100313016276965264374411 15150469524415447896561617)
        ·
          refine ⟨11362852143311585922421213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15150469524415447896561617 11362852143311585922421213)
          ·
            refine ⟨4261069553741844720907955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11362852143311585922421213 4261069553741844720907955)
            ·
              refine ⟨6391604330612767081361933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261069553741844720907955 6391604330612767081361933)
              ·
                refine ⟨2396851623979787655510725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6391604330612767081361933 2396851623979787655510725)
                ·
                  refine ⟨449409679496210185408261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396851623979787655510725 449409679496210185408261)
                  ·
                    rfl

theorem cell22_3938500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_3938500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938500 prefixEnd_3938500 := by exact prefixLift 3938500
  have htrace : WordTrace (prefixWord ++ tailWord_3938500) baseStart_3938500 baseEnd_3938500 := by
    simpa [prefixWord, tailWord_3938500, baseEnd_3938500] using wordTrace_append hprefix tailTrace_3938500
  have hstable : (prefixWord ++ tailWord_3938500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938500).length < 2 ^ (prefixWord ++ tailWord_3938500).sum := by decide
  have hdescent : baseEnd_3938500 < baseStart_3938500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938577 : List Nat := [1, 2, 2, 1, 1, 7, 2, 2, 1, 3]
def baseStart_3938577 : Nat := 118140960795 + 3938577 * 2 ^ 59
def prefixEnd_3938577 : Nat := 4983230072969 + 3 ^ 40 * 3938577 * 2
def baseEnd_3938577 : Nat := 1348255397162228022049547

theorem tailTrace_3938577 : CollatzResearch.WordTrace tailWord_3938577 prefixEnd_3938577 1348255397162228022049547 := by
  unfold tailWord_3938577
  simp only [CollatzResearch.WordTrace]
  refine ⟨143651704652215659243877985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95767803101477106162585323 143651704652215659243877985)
  ·
    refine ⟨107738778489161744432908489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143651704652215659243877985 107738778489161744432908489)
    ·
      refine ⟨80804083866871308324681367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107738778489161744432908489 80804083866871308324681367)
      ·
        refine ⟨121206125800306962487022051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80804083866871308324681367 121206125800306962487022051)
        ·
          refine ⟨181809188700460443730533077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121206125800306962487022051 181809188700460443730533077)
          ·
            refine ⟨4261152860167041649934369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 181809188700460443730533077 4261152860167041649934369)
            ·
              refine ⟨3195864645125281237450777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261152860167041649934369 3195864645125281237450777)
              ·
                refine ⟨2396898483843960928088083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195864645125281237450777 2396898483843960928088083)
                ·
                  refine ⟨3595347725765941392132125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396898483843960928088083 3595347725765941392132125)
                  ·
                    refine ⟨1348255397162228022049547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3595347725765941392132125 1348255397162228022049547)
                    ·
                      rfl

theorem cell22_3938577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_3938577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938577 prefixEnd_3938577 := by exact prefixLift 3938577
  have htrace : WordTrace (prefixWord ++ tailWord_3938577) baseStart_3938577 baseEnd_3938577 := by
    simpa [prefixWord, tailWord_3938577, baseEnd_3938577] using wordTrace_append hprefix tailTrace_3938577
  have hstable : (prefixWord ++ tailWord_3938577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938577).length < 2 ^ (prefixWord ++ tailWord_3938577).sum := by decide
  have hdescent : baseEnd_3938577 < baseStart_3938577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938590 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3938590 : Nat := 118140960795 + 3938590 * 2 ^ 59
def prefixEnd_3938590 : Nat := 4983230072969 + 3 ^ 40 * 3938590 * 2
def baseEnd_3938590 : Nat := 449419949109300107158169

theorem tailTrace_3938590 : CollatzResearch.WordTrace tailWord_3938590 prefixEnd_3938590 449419949109300107158169 := by
  unfold tailWord_3938590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17956522350146070308012653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95768119200779041642734149 17956522350146070308012653)
  ·
    refine ⟨6733695881304776365504745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17956522350146070308012653 6733695881304776365504745)
    ·
      refine ⟨5050271910978582274128559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6733695881304776365504745 5050271910978582274128559)
      ·
        refine ⟨7575407866467873411192839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5050271910978582274128559 7575407866467873411192839)
        ·
          refine ⟨11363111799701810116789259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7575407866467873411192839 11363111799701810116789259)
          ·
            refine ⟨17044667699552715175183889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11363111799701810116789259 17044667699552715175183889)
            ·
              refine ⟨12783500774664536381387917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17044667699552715175183889 12783500774664536381387917)
              ·
                refine ⟨4793812790499201143020469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12783500774664536381387917 4793812790499201143020469)
                ·
                  refine ⟨449419949109300107158169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4793812790499201143020469 449419949109300107158169)
                  ·
                    rfl

theorem cell22_3938590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3938590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938590 prefixEnd_3938590 := by exact prefixLift 3938590
  have htrace : WordTrace (prefixWord ++ tailWord_3938590) baseStart_3938590 baseEnd_3938590 := by
    simpa [prefixWord, tailWord_3938590, baseEnd_3938590] using wordTrace_append hprefix tailTrace_3938590
  have hstable : (prefixWord ++ tailWord_3938590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938590).length < 2 ^ (prefixWord ++ tailWord_3938590).sum := by decide
  have hdescent : baseEnd_3938590 < baseStart_3938590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938616 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_3938616 : Nat := 118140960795 + 3938616 * 2 ^ 59
def prefixEnd_3938616 : Nat := 4983230072969 + 3 ^ 40 * 3938616 * 2
def baseEnd_3938616 : Nat := 1348268747659244920324427

theorem tailTrace_3938616 : CollatzResearch.WordTrace tailWord_3938616 prefixEnd_3938616 1348268747659244920324427 := by
  unfold tailWord_3938616
  simp only [CollatzResearch.WordTrace]
  refine ⟨71826563549537184452273851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95768751399382912603031801 71826563549537184452273851)
  ·
    refine ⟨107739845324305776678410777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71826563549537184452273851 107739845324305776678410777)
    ·
      refine ⟨80804883993229332508808083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107739845324305776678410777 80804883993229332508808083)
      ·
        refine ⟨121207325989843998763212125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80804883993229332508808083 121207325989843998763212125)
        ·
          refine ⟨45452747246191499536204547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121207325989843998763212125 45452747246191499536204547)
          ·
            refine ⟨68179120869287249304306821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45452747246191499536204547 68179120869287249304306821)
            ·
              refine ⟨12783585162991359244557529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68179120869287249304306821 12783585162991359244557529)
              ·
                refine ⟨9587688872243519433418147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12783585162991359244557529 9587688872243519433418147)
                ·
                  refine ⟨14381533308365279150127221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9587688872243519433418147 14381533308365279150127221)
                  ·
                    refine ⟨1348268747659244920324427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14381533308365279150127221 1348268747659244920324427)
                    ·
                      rfl

theorem cell22_3938616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_3938616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938616 prefixEnd_3938616 := by exact prefixLift 3938616
  have htrace : WordTrace (prefixWord ++ tailWord_3938616) baseStart_3938616 baseEnd_3938616 := by
    simpa [prefixWord, tailWord_3938616, baseEnd_3938616] using wordTrace_append hprefix tailTrace_3938616
  have hstable : (prefixWord ++ tailWord_3938616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938616).length < 2 ^ (prefixWord ++ tailWord_3938616).sum := by decide
  have hdescent : baseEnd_3938616 < baseStart_3938616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938618 : List Nat := [3, 1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_3938618 : Nat := 118140960795 + 3938618 * 2 ^ 59
def prefixEnd_3938618 : Nat := 4983230072969 + 3 ^ 40 * 3938618 * 2
def baseEnd_3938618 : Nat := 449423144100039193924807

theorem tailTrace_3938618 : CollatzResearch.WordTrace tailWord_3938618 prefixEnd_3938618 449423144100039193924807 := by
  unfold tailWord_3938618
  simp only [CollatzResearch.WordTrace]
  refine ⟨35913300011266780811530127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95768800030044748830747005 35913300011266780811530127)
  ·
    refine ⟨53869950016900171217295191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35913300011266780811530127 53869950016900171217295191)
    ·
      refine ⟨80804925025350256825942787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53869950016900171217295191 80804925025350256825942787)
      ·
        refine ⟨121207387538025385238914181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80804925025350256825942787 121207387538025385238914181)
        ·
          refine ⟨22726385163379759732296409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121207387538025385238914181 22726385163379759732296409)
          ·
            refine ⟨17044788872534819799222307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22726385163379759732296409 17044788872534819799222307)
            ·
              refine ⟨25567183308802229698833461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17044788872534819799222307 25567183308802229698833461)
              ·
                refine ⟨2396923435200209034265637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25567183308802229698833461 2396923435200209034265637)
                ·
                  refine ⟨449423144100039193924807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396923435200209034265637 449423144100039193924807)
                  ·
                    rfl

theorem cell22_3938618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_3938618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938618 prefixEnd_3938618 := by exact prefixLift 3938618
  have htrace : WordTrace (prefixWord ++ tailWord_3938618) baseStart_3938618 baseEnd_3938618 := by
    simpa [prefixWord, tailWord_3938618, baseEnd_3938618] using wordTrace_append hprefix tailTrace_3938618
  have hstable : (prefixWord ++ tailWord_3938618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938618).length < 2 ^ (prefixWord ++ tailWord_3938618).sum := by decide
  have hdescent : baseEnd_3938618 < baseStart_3938618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938631 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 4, 4]
def baseStart_3938631 : Nat := 118140960795 + 3938631 * 2 ^ 59
def prefixEnd_3938631 : Nat := 4983230072969 + 3 ^ 40 * 3938631 * 2
def baseEnd_3938631 : Nat := 1348273882465789881199381

theorem tailTrace_3938631 : CollatzResearch.WordTrace tailWord_3938631 prefixEnd_3938631 1348273882465789881199381 := by
  unfold tailWord_3938631
  simp only [CollatzResearch.WordTrace]
  refine ⟨143653674194020026466343747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95769116129346684310895831 143653674194020026466343747)
  ·
    refine ⟨215480511291030039699515621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143653674194020026466343747 215480511291030039699515621)
    ·
      refine ⟨40402595867068132443659179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215480511291030039699515621 40402595867068132443659179)
      ·
        refine ⟨60603893800602198665488769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40402595867068132443659179 60603893800602198665488769)
        ·
          refine ⟨45452920350451648999116577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60603893800602198665488769 45452920350451648999116577)
          ·
            refine ⟨34089690262838736749337433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45452920350451648999116577 34089690262838736749337433)
            ·
              refine ⟨25567267697129052562003075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34089690262838736749337433 25567267697129052562003075)
              ·
                refine ⟨38350901545693578843004613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25567267697129052562003075 38350901545693578843004613)
                ·
                  refine ⟨7190794039817546033063365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38350901545693578843004613 7190794039817546033063365)
                  ·
                    refine ⟨1348273882465789881199381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7190794039817546033063365 1348273882465789881199381)
                    ·
                      rfl

theorem cell22_3938631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_3938631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938631 prefixEnd_3938631 := by exact prefixLift 3938631
  have htrace : WordTrace (prefixWord ++ tailWord_3938631) baseStart_3938631 baseEnd_3938631 := by
    simpa [prefixWord, tailWord_3938631, baseEnd_3938631] using wordTrace_append hprefix tailTrace_3938631
  have hstable : (prefixWord ++ tailWord_3938631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938631).length < 2 ^ (prefixWord ++ tailWord_3938631).sum := by decide
  have hdescent : baseEnd_3938631 < baseStart_3938631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938663 : List Nat := [1, 1, 5, 1, 3, 1, 4, 6]
def baseStart_3938663 : Nat := 118140960795 + 3938663 * 2 ^ 59
def prefixEnd_3938663 : Nat := 4983230072969 + 3 ^ 40 * 3938663 * 2
def baseEnd_3938663 : Nat := 149809426302194718266587

theorem tailTrace_3938663 : CollatzResearch.WordTrace tailWord_3938663 prefixEnd_3938663 149809426302194718266587 := by
  unfold tailWord_3938663
  simp only [CollatzResearch.WordTrace]
  refine ⟨143654841329904095931508643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95769894219936063954339095 143654841329904095931508643)
  ·
    refine ⟨215482261994856143897262965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143654841329904095931508643 215482261994856143897262965)
    ·
      refine ⟨20201462062017763490368403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215482261994856143897262965 20201462062017763490368403)
      ·
        refine ⟨30302193093026645235552605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20201462062017763490368403 30302193093026645235552605)
        ·
          refine ⟨11363322409884991963332227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30302193093026645235552605 11363322409884991963332227)
          ·
            refine ⟨17044983614827487944998341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11363322409884991963332227 17044983614827487944998341)
            ·
              refine ⟨3195934427780153989687189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17044983614827487944998341 3195934427780153989687189)
              ·
                refine ⟨149809426302194718266587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3195934427780153989687189 149809426302194718266587)
                ·
                  rfl

theorem cell22_3938663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 6].length) (baseStart_3938663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938663 prefixEnd_3938663 := by exact prefixLift 3938663
  have htrace : WordTrace (prefixWord ++ tailWord_3938663) baseStart_3938663 baseEnd_3938663 := by
    simpa [prefixWord, tailWord_3938663, baseEnd_3938663] using wordTrace_append hprefix tailTrace_3938663
  have hstable : (prefixWord ++ tailWord_3938663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938663).length < 2 ^ (prefixWord ++ tailWord_3938663).sum := by decide
  have hdescent : baseEnd_3938663 < baseStart_3938663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938783 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 1, 6]
def baseStart_3938783 : Nat := 118140960795 + 3938783 * 2 ^ 59
def prefixEnd_3938783 : Nat := 4983230072969 + 3 ^ 40 * 3938783 * 2
def baseEnd_3938783 : Nat := 1348325915172112151398915

theorem tailTrace_3938783 : CollatzResearch.WordTrace tailWord_3938783 prefixEnd_3938783 1348325915172112151398915 := by
  unfold tailWord_3938783
  simp only [CollatzResearch.WordTrace]
  refine ⟨143659218089469356425877003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95772812059646237617251335 143659218089469356425877003)
  ·
    refine ⟨215488827134204034638815505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143659218089469356425877003 215488827134204034638815505)
    ·
      refine ⟨161616620350653025979111629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215488827134204034638815505 161616620350653025979111629)
      ·
        refine ⟨60606232631494884742166861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161616620350653025979111629 60606232631494884742166861)
        ·
          refine ⟨22727337236810581778312573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60606232631494884742166861 22727337236810581778312573)
          ·
            refine ⟨8522751463803968166867215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22727337236810581778312573 8522751463803968166867215)
            ·
              refine ⟨12784127195705952250300823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522751463803968166867215 12784127195705952250300823)
              ·
                refine ⟨19176190793558928375451235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12784127195705952250300823 19176190793558928375451235)
                ·
                  refine ⟨28764286190338392563176853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19176190793558928375451235 28764286190338392563176853)
                  ·
                    refine ⟨1348325915172112151398915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28764286190338392563176853 1348325915172112151398915)
                    ·
                      rfl

theorem cell22_3938783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_3938783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938783 prefixEnd_3938783 := by exact prefixLift 3938783
  have htrace : WordTrace (prefixWord ++ tailWord_3938783) baseStart_3938783 baseEnd_3938783 := by
    simpa [prefixWord, tailWord_3938783, baseEnd_3938783] using wordTrace_append hprefix tailTrace_3938783
  have hstable : (prefixWord ++ tailWord_3938783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938783).length < 2 ^ (prefixWord ++ tailWord_3938783).sum := by decide
  have hdescent : baseEnd_3938783 < baseStart_3938783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938787 : List Nat := [1, 1, 1, 6, 3, 1, 2, 3, 4]
def baseStart_3938787 : Nat := 118140960795 + 3938787 * 2 ^ 59
def prefixEnd_3938787 : Nat := 4983230072969 + 3 ^ 40 * 3938787 * 2
def baseEnd_3938787 : Nat := 449442428151285824766301

theorem tailTrace_3938787 : CollatzResearch.WordTrace tailWord_3938787 prefixEnd_3938787 449442428151285824766301 := by
  unfold tailWord_3938787
  simp only [CollatzResearch.WordTrace]
  refine ⟨143659363981454865109022615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95772909320969910072681743 143659363981454865109022615)
  ·
    refine ⟨215489045972182297663533923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143659363981454865109022615 215489045972182297663533923)
    ·
      refine ⟨323233568958273446495300885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215489045972182297663533923 323233568958273446495300885)
      ·
        refine ⟨15151573544919067804467229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 323233568958273446495300885 15151573544919067804467229)
        ·
          refine ⟨5681840079344650426675211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15151573544919067804467229 5681840079344650426675211)
          ·
            refine ⟨8522760119016975640012817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681840079344650426675211 8522760119016975640012817)
            ·
              refine ⟨6392070089262731730009613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8522760119016975640012817 6392070089262731730009613)
              ·
                refine ⟨2397026283473524398753605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6392070089262731730009613 2397026283473524398753605)
                ·
                  refine ⟨449442428151285824766301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397026283473524398753605 449442428151285824766301)
                  ·
                    rfl

theorem cell22_3938787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 4].length) (baseStart_3938787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938787 prefixEnd_3938787 := by exact prefixLift 3938787
  have htrace : WordTrace (prefixWord ++ tailWord_3938787) baseStart_3938787 baseEnd_3938787 := by
    simpa [prefixWord, tailWord_3938787, baseEnd_3938787] using wordTrace_append hprefix tailTrace_3938787
  have hstable : (prefixWord ++ tailWord_3938787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938787).length < 2 ^ (prefixWord ++ tailWord_3938787).sum := by decide
  have hdescent : baseEnd_3938787 < baseStart_3938787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938789 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 1, 4]
def baseStart_3938789 : Nat := 118140960795 + 3938789 * 2 ^ 59
def prefixEnd_3938789 : Nat := 4983230072969 + 3 ^ 40 * 3938789 * 2
def baseEnd_3938789 : Nat := 1348327969094730135748897

theorem tailTrace_3938789 : CollatzResearch.WordTrace tailWord_3938789 prefixEnd_3938789 1348327969094730135748897 := by
  unfold tailWord_3938789
  simp only [CollatzResearch.WordTrace]
  refine ⟨143659436927447619450595421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95772957951631746300396947 143659436927447619450595421)
  ·
    refine ⟨53872288847792857293973283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143659436927447619450595421 53872288847792857293973283)
    ·
      refine ⟨80808433271689285940959925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53872288847792857293973283 80808433271689285940959925)
      ·
        refine ⟨7575790619220870556964993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80808433271689285940959925 7575790619220870556964993)
        ·
          refine ⟨5681842964415652917723745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7575790619220870556964993 5681842964415652917723745)
          ·
            refine ⟨4261382223311739688292809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5681842964415652917723745 4261382223311739688292809)
            ·
              refine ⟨3196036667483804766219607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261382223311739688292809 3196036667483804766219607)
              ·
                refine ⟨4794055001225707149329411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196036667483804766219607 4794055001225707149329411)
                ·
                  refine ⟨7191082501838560723994117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794055001225707149329411 7191082501838560723994117)
                  ·
                    refine ⟨1348327969094730135748897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191082501838560723994117 1348327969094730135748897)
                    ·
                      rfl

theorem cell22_3938789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_3938789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938789 prefixEnd_3938789 := by exact prefixLift 3938789
  have htrace : WordTrace (prefixWord ++ tailWord_3938789) baseStart_3938789 baseEnd_3938789 := by
    simpa [prefixWord, tailWord_3938789, baseEnd_3938789] using wordTrace_append hprefix tailTrace_3938789
  have hstable : (prefixWord ++ tailWord_3938789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938789).length < 2 ^ (prefixWord ++ tailWord_3938789).sum := by decide
  have hdescent : baseEnd_3938789 < baseStart_3938789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938798 : List Nat := [4, 1, 2, 1, 2, 3, 9]
def baseStart_3938798 : Nat := 118140960795 + 3938798 * 2 ^ 59
def prefixEnd_3938798 : Nat := 4983230072969 + 3 ^ 40 * 3938798 * 2
def baseEnd_3938798 : Nat := 49938187036246559713847

theorem tailTrace_3938798 : CollatzResearch.WordTrace tailWord_3938798 prefixEnd_3938798 49938187036246559713847 := by
  unfold tailWord_3938798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957470648051876748459131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95773176789610009325115365 17957470648051876748459131)
  ·
    refine ⟨26936205972077815122688697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17957470648051876748459131 26936205972077815122688697)
    ·
      refine ⟨20202154479058361342016523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26936205972077815122688697 20202154479058361342016523)
      ·
        refine ⟨30303231718587542013024785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20202154479058361342016523 30303231718587542013024785)
        ·
          refine ⟨22727423788940656509768589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30303231718587542013024785 22727423788940656509768589)
          ·
            refine ⟨8522783920852746191163221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22727423788940656509768589 8522783920852746191163221)
            ·
              refine ⟨49938187036246559713847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8522783920852746191163221 49938187036246559713847)
              ·
                rfl

theorem cell22_3938798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 9].length) (baseStart_3938798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938798 prefixEnd_3938798 := by exact prefixLift 3938798
  have htrace : WordTrace (prefixWord ++ tailWord_3938798) baseStart_3938798 baseEnd_3938798 := by
    simpa [prefixWord, tailWord_3938798, baseEnd_3938798] using wordTrace_append hprefix tailTrace_3938798
  have hstable : (prefixWord ++ tailWord_3938798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938798).length < 2 ^ (prefixWord ++ tailWord_3938798).sum := by decide
  have hdescent : baseEnd_3938798 < baseStart_3938798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938802 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_3938802 : Nat := 118140960795 + 3938802 * 2 ^ 59
def prefixEnd_3938802 : Nat := 4983230072969 + 3 ^ 40 * 3938802 * 2
def baseEnd_3938802 : Nat := 1348332419260402435173857

theorem tailTrace_3938802 : CollatzResearch.WordTrace tailWord_3938802 prefixEnd_3938802 1348332419260402435173857 := by
  unfold tailWord_3938802
  simp only [CollatzResearch.WordTrace]
  refine ⟨35914977769100130667704665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95773274050933681780545773 35914977769100130667704665)
  ·
    refine ⟨26936233326825098000778499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35914977769100130667704665 26936233326825098000778499)
    ·
      refine ⟨40404349990237647001167749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26936233326825098000778499 40404349990237647001167749)
      ·
        refine ⟨7575815623169558812718953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40404349990237647001167749 7575815623169558812718953)
        ·
          refine ⟨5681861717377169109539215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7575815623169558812718953 5681861717377169109539215)
          ·
            refine ⟨8522792576065753664308823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681861717377169109539215 8522792576065753664308823)
            ·
              refine ⟨12784188864098630496463235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522792576065753664308823 12784188864098630496463235)
              ·
                refine ⟨19176283296147945744694853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12784188864098630496463235 19176283296147945744694853)
                ·
                  refine ⟨3595553118027739827130285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19176283296147945744694853 3595553118027739827130285)
                  ·
                    refine ⟨1348332419260402435173857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3595553118027739827130285 1348332419260402435173857)
                    ·
                      rfl

theorem cell22_3938802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_3938802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938802 prefixEnd_3938802 := by exact prefixLift 3938802
  have htrace : WordTrace (prefixWord ++ tailWord_3938802) baseStart_3938802 baseEnd_3938802 := by
    simpa [prefixWord, tailWord_3938802, baseEnd_3938802] using wordTrace_append hprefix tailTrace_3938802
  have hstable : (prefixWord ++ tailWord_3938802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938802).length < 2 ^ (prefixWord ++ tailWord_3938802).sum := by decide
  have hdescent : baseEnd_3938802 < baseStart_3938802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938877 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 5]
def baseStart_3938877 : Nat := 118140960795 + 3938877 * 2 ^ 59
def prefixEnd_3938877 : Nat := 4983230072969 + 3 ^ 40 * 3938877 * 2
def baseEnd_3938877 : Nat := 449452697764375746516209

theorem tailTrace_3938877 : CollatzResearch.WordTrace tailWord_3938877 prefixEnd_3938877 449452697764375746516209 := by
  unfold tailWord_3938877
  simp only [CollatzResearch.WordTrace]
  refine ⟨143662646551128810479798885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95775097700752540319865923 143662646551128810479798885)
  ·
    refine ⟨26936746228336651964962291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143662646551128810479798885 26936746228336651964962291)
    ·
      refine ⟨40405119342504977947443437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26936746228336651964962291 40405119342504977947443437)
      ·
        refine ⟨15151919753439366730291289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40405119342504977947443437 15151919753439366730291289)
        ·
          refine ⟨11363939815079525047718467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15151919753439366730291289 11363939815079525047718467)
          ·
            refine ⟨17045909722619287571577701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11363939815079525047718467 17045909722619287571577701)
            ·
              refine ⟨3196108072991116419670819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17045909722619287571577701 3196108072991116419670819)
              ·
                refine ⟨4794162109486674629506229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196108072991116419670819 4794162109486674629506229)
                ·
                  refine ⟨449452697764375746516209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4794162109486674629506229 449452697764375746516209)
                  ·
                    rfl

theorem cell22_3938877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_3938877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938877 prefixEnd_3938877 := by exact prefixLift 3938877
  have htrace : WordTrace (prefixWord ++ tailWord_3938877) baseStart_3938877 baseEnd_3938877 := by
    simpa [prefixWord, tailWord_3938877, baseEnd_3938877] using wordTrace_append hprefix tailTrace_3938877
  have hstable : (prefixWord ++ tailWord_3938877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938877).length < 2 ^ (prefixWord ++ tailWord_3938877).sum := by decide
  have hdescent : baseEnd_3938877 < baseStart_3938877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938888 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 6]
def baseStart_3938888 : Nat := 118140960795 + 3938888 * 2 ^ 59
def prefixEnd_3938888 : Nat := 4983230072969 + 3 ^ 40 * 3938888 * 2
def baseEnd_3938888 : Nat := 449453952939308959174531

theorem tailTrace_3938888 : CollatzResearch.WordTrace tailWord_3938888 prefixEnd_3938888 449453952939308959174531 := by
  unfold tailWord_3938888
  simp only [CollatzResearch.WordTrace]
  refine ⟨71831523877044479679224659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95775365169392639572299545 71831523877044479679224659)
  ·
    refine ⟨107747285815566719518836989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71831523877044479679224659 107747285815566719518836989)
    ·
      refine ⟨40405232180837519819563871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107747285815566719518836989 40405232180837519819563871)
      ·
        refine ⟨60607848271256279729345807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40405232180837519819563871 60607848271256279729345807)
        ·
          refine ⟨90911772406884419594018711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60607848271256279729345807 90911772406884419594018711)
          ·
            refine ⟨136367658610326629391028067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90911772406884419594018711 136367658610326629391028067)
            ·
              refine ⟨204551487915489944086542101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136367658610326629391028067 204551487915489944086542101)
              ·
                refine ⟨9588350996038591129056661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204551487915489944086542101 9588350996038591129056661)
                ·
                  refine ⟨449453952939308959174531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9588350996038591129056661 449453952939308959174531)
                  ·
                    rfl

theorem cell22_3938888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_3938888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938888 prefixEnd_3938888 := by exact prefixLift 3938888
  have htrace : WordTrace (prefixWord ++ tailWord_3938888) baseStart_3938888 baseEnd_3938888 := by
    simpa [prefixWord, tailWord_3938888, baseEnd_3938888] using wordTrace_append hprefix tailTrace_3938888
  have hstable : (prefixWord ++ tailWord_3938888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938888).length < 2 ^ (prefixWord ++ tailWord_3938888).sum := by decide
  have hdescent : baseEnd_3938888 < baseStart_3938888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938890 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_3938890 : Nat := 118140960795 + 3938890 * 2 ^ 59
def prefixEnd_3938890 : Nat := 4983230072969 + 3 ^ 40 * 3938890 * 2
def baseEnd_3938890 : Nat := 1348362543458799538973587

theorem tailTrace_3938890 : CollatzResearch.WordTrace tailWord_3938890 prefixEnd_3938890 1348362543458799538973587 := by
  unfold tailWord_3938890
  simp only [CollatzResearch.WordTrace]
  refine ⟨35915780175020428425005531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95775413800054475800014749 35915780175020428425005531)
  ·
    refine ⟨53873670262530642637508297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35915780175020428425005531 53873670262530642637508297)
    ·
      refine ⟨40405252696897981978131223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53873670262530642637508297 40405252696897981978131223)
      ·
        refine ⟨60607879045346972967196835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40405252696897981978131223 60607879045346972967196835)
        ·
          refine ⟨90911818568020459450795253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60607879045346972967196835 90911818568020459450795253)
          ·
            refine ⟨8522982990751918073512055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90911818568020459450795253 8522982990751918073512055)
            ·
              refine ⟨12784474486127877110268083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522982990751918073512055 12784474486127877110268083)
              ·
                refine ⟨19176711729191815665402125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12784474486127877110268083 19176711729191815665402125)
                ·
                  refine ⟨7191266898446930874525797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19176711729191815665402125 7191266898446930874525797)
                  ·
                    refine ⟨1348362543458799538973587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191266898446930874525797 1348362543458799538973587)
                    ·
                      rfl

theorem cell22_3938890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_3938890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938890 prefixEnd_3938890 := by exact prefixLift 3938890
  have htrace : WordTrace (prefixWord ++ tailWord_3938890) baseStart_3938890 baseEnd_3938890 := by
    simpa [prefixWord, tailWord_3938890, baseEnd_3938890] using wordTrace_append hprefix tailTrace_3938890
  have hstable : (prefixWord ++ tailWord_3938890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938890).length < 2 ^ (prefixWord ++ tailWord_3938890).sum := by decide
  have hdescent : baseEnd_3938890 < baseStart_3938890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938922 : List Nat := [3, 1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_3938922 : Nat := 118140960795 + 3938922 * 2 ^ 59
def prefixEnd_3938922 : Nat := 4983230072969 + 3 ^ 40 * 3938922 * 2
def baseEnd_3938922 : Nat := 449457832570920707391163

theorem tailTrace_3938922 : CollatzResearch.WordTrace tailWord_3938922 prefixEnd_3938922 449457832570920707391163 := by
  unfold tailWord_3938922
  simp only [CollatzResearch.WordTrace]
  refine ⟨35916071958991445791296755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95776191890643855443458013 35916071958991445791296755)
  ·
    refine ⟨53874107938487168686945133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35916071958991445791296755 53874107938487168686945133)
    ·
      refine ⟨20202790476932688257604425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53874107938487168686945133 20202790476932688257604425)
      ·
        refine ⟨15152092857699516193203319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20202790476932688257604425 15152092857699516193203319)
        ·
          refine ⟨22728139286549274289804979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15152092857699516193203319 22728139286549274289804979)
          ·
            refine ⟨34092208929823911434707469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22728139286549274289804979 34092208929823911434707469)
            ·
              refine ⟨12784578348683966788015301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34092208929823911434707469 12784578348683966788015301)
              ·
                refine ⟨2397108440378243772752869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12784578348683966788015301 2397108440378243772752869)
                ·
                  refine ⟨449457832570920707391163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397108440378243772752869 449457832570920707391163)
                  ·
                    rfl

theorem cell22_3938922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_3938922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938922 prefixEnd_3938922 := by exact prefixLift 3938922
  have htrace : WordTrace (prefixWord ++ tailWord_3938922) baseStart_3938922 baseEnd_3938922 := by
    simpa [prefixWord, tailWord_3938922, baseEnd_3938922] using wordTrace_append hprefix tailTrace_3938922
  have hstable : (prefixWord ++ tailWord_3938922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938922).length < 2 ^ (prefixWord ++ tailWord_3938922).sum := by decide
  have hdescent : baseEnd_3938922 < baseStart_3938922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938937 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 2, 3]
def baseStart_3938937 : Nat := 118140960795 + 3938937 * 2 ^ 59
def prefixEnd_3938937 : Nat := 4983230072969 + 3 ^ 40 * 3938937 * 2
def baseEnd_3938937 : Nat := 1348378632519307083048443

theorem tailTrace_3938937 : CollatzResearch.WordTrace tailWord_3938937 prefixEnd_3938937 1348378632519307083048443 := by
  unfold tailWord_3938937
  simp only [CollatzResearch.WordTrace]
  refine ⟨143664834930911440726983065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95776556620607627151322043 143664834930911440726983065)
  ·
    refine ⟨107748626198183580545237299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143664834930911440726983065 107748626198183580545237299)
    ·
      refine ⟨161622939297275370817855949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107748626198183580545237299 161622939297275370817855949)
      ·
        refine ⟨60608602236478264056695981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161622939297275370817855949 60608602236478264056695981)
        ·
          refine ⟨22728225838679349021260993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60608602236478264056695981 22728225838679349021260993)
          ·
            refine ⟨17046169379009511765945745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22728225838679349021260993 17046169379009511765945745)
            ·
              refine ⟨12784627034257133824459309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17046169379009511765945745 12784627034257133824459309)
              ·
                refine ⟨4794235137846425184172241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12784627034257133824459309 4794235137846425184172241)
                ·
                  refine ⟨3595676353384818888129181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4794235137846425184172241 3595676353384818888129181)
                  ·
                    refine ⟨1348378632519307083048443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3595676353384818888129181 1348378632519307083048443)
                    ·
                      rfl

theorem cell22_3938937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 3].length) (baseStart_3938937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938937 prefixEnd_3938937 := by exact prefixLift 3938937
  have htrace : WordTrace (prefixWord ++ tailWord_3938937) baseStart_3938937 baseEnd_3938937 := by
    simpa [prefixWord, tailWord_3938937, baseEnd_3938937] using wordTrace_append hprefix tailTrace_3938937
  have hstable : (prefixWord ++ tailWord_3938937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938937).length < 2 ^ (prefixWord ++ tailWord_3938937).sum := by decide
  have hdescent : baseEnd_3938937 < baseStart_3938937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3938963 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 4, 6]
def baseStart_3938963 : Nat := 118140960795 + 3938963 * 2 ^ 59
def prefixEnd_3938963 : Nat := 4983230072969 + 3 ^ 40 * 3938963 * 2
def baseEnd_3938963 : Nat := 1348387532850651681898363

theorem tailTrace_3938963 : CollatzResearch.WordTrace tailWord_3938963 prefixEnd_3938963 1348387532850651681898363 := by
  unfold tailWord_3938963
  simp only [CollatzResearch.WordTrace]
  refine ⟨143665783228817247167429543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95777188819211498111619695 143665783228817247167429543)
  ·
    refine ⟨215498674843225870751144315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143665783228817247167429543 215498674843225870751144315)
    ·
      refine ⟨323248012264838806126716473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215498674843225870751144315 323248012264838806126716473)
      ·
        refine ⟨242436009198629104595037355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323248012264838806126716473 242436009198629104595037355)
        ·
          refine ⟨363654013797943656892556033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242436009198629104595037355 363654013797943656892556033)
          ·
            refine ⟨272740510348457742669417025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363654013797943656892556033 272740510348457742669417025)
            ·
              refine ⟨204555382761343307002062769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272740510348457742669417025 204555382761343307002062769)
              ·
                refine ⟨153416537071007480251547077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204555382761343307002062769 153416537071007480251547077)
                ·
                  refine ⟨28765600700813902547165077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153416537071007480251547077 28765600700813902547165077)
                  ·
                    refine ⟨1348387532850651681898363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28765600700813902547165077 1348387532850651681898363)
                    ·
                      rfl

theorem cell22_3938963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_3938963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3938963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3938963 prefixEnd_3938963 := by exact prefixLift 3938963
  have htrace : WordTrace (prefixWord ++ tailWord_3938963) baseStart_3938963 baseEnd_3938963 := by
    simpa [prefixWord, tailWord_3938963, baseEnd_3938963] using wordTrace_append hprefix tailTrace_3938963
  have hstable : (prefixWord ++ tailWord_3938963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3938963).length < 2 ^ (prefixWord ++ tailWord_3938963).sum := by decide
  have hdescent : baseEnd_3938963 < baseStart_3938963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3938963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939016 : List Nat := [2, 1, 3, 1, 2, 5, 1, 3, 1, 3]
def baseStart_3939016 : Nat := 118140960795 + 3939016 * 2 ^ 59
def prefixEnd_3939016 : Nat := 4983230072969 + 3 ^ 40 * 3939016 * 2
def baseEnd_3939016 : Nat := 1348405675833777210323201

theorem tailTrace_3939016 : CollatzResearch.WordTrace tailWord_3939016 prefixEnd_3939016 1348405675833777210323201 := by
  unfold tailWord_3939016
  simp only [CollatzResearch.WordTrace]
  refine ⟨71833858148812618609554451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95778477531750158146072601 71833858148812618609554451)
  ·
    refine ⟨107750787223218927914331677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71833858148812618609554451 107750787223218927914331677)
    ·
      refine ⟨40406545208707097967874379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107750787223218927914331677 40406545208707097967874379)
      ·
        refine ⟨60609817813060646951811569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40406545208707097967874379 60609817813060646951811569)
        ·
          refine ⟨45457363359795485213858677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60609817813060646951811569 45457363359795485213858677)
          ·
            refine ⟨4261627814980826738799251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45457363359795485213858677 4261627814980826738799251)
            ·
              refine ⟨6392441722471240108198877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261627814980826738799251 6392441722471240108198877)
              ·
                refine ⟨2397165645926715040574579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6392441722471240108198877 2397165645926715040574579)
                ·
                  refine ⟨3595748468890072560861869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397165645926715040574579 3595748468890072560861869)
                  ·
                    refine ⟨1348405675833777210323201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3595748468890072560861869 1348405675833777210323201)
                    ·
                      rfl

theorem cell22_3939016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_3939016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939016 prefixEnd_3939016 := by exact prefixLift 3939016
  have htrace : WordTrace (prefixWord ++ tailWord_3939016) baseStart_3939016 baseEnd_3939016 := by
    simpa [prefixWord, tailWord_3939016, baseEnd_3939016] using wordTrace_append hprefix tailTrace_3939016
  have hstable : (prefixWord ++ tailWord_3939016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939016).length < 2 ^ (prefixWord ++ tailWord_3939016).sum := by decide
  have hdescent : baseEnd_3939016 < baseStart_3939016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939140 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3939140 : Nat := 118140960795 + 3939140 * 2 ^ 59
def prefixEnd_3939140 : Nat := 4983230072969 + 3 ^ 40 * 3939140 * 2
def baseEnd_3939140 : Nat := 1348448123567882220222821

theorem tailTrace_3939140 : CollatzResearch.WordTrace tailWord_3939140 prefixEnd_3939140 1348448123567882220222821 := by
  unfold tailWord_3939140
  simp only [CollatzResearch.WordTrace]
  refine ⟨71836119474588003198311437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95781492632784004264415249 71836119474588003198311437)
  ·
    refine ⟨26938544802970501199366789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71836119474588003198311437 26938544802970501199366789)
    ·
      refine ⟨5050977150556968974881273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26938544802970501199366789 5050977150556968974881273)
      ·
        refine ⟨3788232862917726731160955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5050977150556968974881273 3788232862917726731160955)
        ·
          refine ⟨5682349294376590096741433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3788232862917726731160955 5682349294376590096741433)
          ·
            refine ⟨4261761970782442572556075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5682349294376590096741433 4261761970782442572556075)
            ·
              refine ⟨6392642956173663858834113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261761970782442572556075 6392642956173663858834113)
              ·
                refine ⟨4794482217130247894125585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6392642956173663858834113 4794482217130247894125585)
                ·
                  refine ⟨3595861662847685920594189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4794482217130247894125585 3595861662847685920594189)
                  ·
                    refine ⟨1348448123567882220222821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3595861662847685920594189 1348448123567882220222821)
                    ·
                      rfl

theorem cell22_3939140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3939140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939140 prefixEnd_3939140 := by exact prefixLift 3939140
  have htrace : WordTrace (prefixWord ++ tailWord_3939140) baseStart_3939140 baseEnd_3939140 := by
    simpa [prefixWord, tailWord_3939140, baseEnd_3939140] using wordTrace_append hprefix tailTrace_3939140
  have hstable : (prefixWord ++ tailWord_3939140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939140).length < 2 ^ (prefixWord ++ tailWord_3939140).sum := by decide
  have hdescent : baseEnd_3939140 < baseStart_3939140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939162 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_3939162 : Nat := 118140960795 + 3939162 * 2 ^ 59
def prefixEnd_3939162 : Nat := 4983230072969 + 3 ^ 40 * 3939162 * 2
def baseEnd_3939162 : Nat := 1348455654617481496172753

theorem tailTrace_3939162 : CollatzResearch.WordTrace tailWord_3939162 prefixEnd_3939162 1348455654617481496172753 := by
  unfold tailWord_3939162
  simp only [CollatzResearch.WordTrace]
  refine ⟨35918260338774076038480935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95782027570064202769282493 35918260338774076038480935)
  ·
    refine ⟨53877390508161114057721403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35918260338774076038480935 53877390508161114057721403)
    ·
      refine ⟨80816085762241671086582105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53877390508161114057721403 80816085762241671086582105)
      ·
        refine ⟨60612064321681253314936579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80816085762241671086582105 60612064321681253314936579)
        ·
          refine ⟨90918096482521879972404869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60612064321681253314936579 90918096482521879972404869)
          ·
            refine ⟨17047143090472852494825913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90918096482521879972404869 17047143090472852494825913)
            ·
              refine ⟨12785357317854639371119435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17047143090472852494825913 12785357317854639371119435)
              ·
                refine ⟨19178035976781959056679153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12785357317854639371119435 19178035976781959056679153)
                ·
                  refine ⟨14383526982586469292509365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19178035976781959056679153 14383526982586469292509365)
                  ·
                    refine ⟨1348455654617481496172753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14383526982586469292509365 1348455654617481496172753)
                    ·
                      rfl

theorem cell22_3939162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_3939162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939162 prefixEnd_3939162 := by exact prefixLift 3939162
  have htrace : WordTrace (prefixWord ++ tailWord_3939162) baseStart_3939162 baseEnd_3939162 := by
    simpa [prefixWord, tailWord_3939162, baseEnd_3939162] using wordTrace_append hprefix tailTrace_3939162
  have hstable : (prefixWord ++ tailWord_3939162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939162).length < 2 ^ (prefixWord ++ tailWord_3939162).sum := by decide
  have hdescent : baseEnd_3939162 < baseStart_3939162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939202 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3939202 : Nat := 118140960795 + 3939202 * 2 ^ 59
def prefixEnd_3939202 : Nat := 4983230072969 + 3 ^ 40 * 3939202 * 2
def baseEnd_3939202 : Nat := 1348469347434934725172631

theorem tailTrace_3939202 : CollatzResearch.WordTrace tailWord_3939202 prefixEnd_3939202 1348469347434934725172631 := by
  unfold tailWord_3939202
  simp only [CollatzResearch.WordTrace]
  refine ⟨35918625068737847746344965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95783000183300927323586573 35918625068737847746344965)
  ·
    refine ⟨6734742200388346452439681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35918625068737847746344965 6734742200388346452439681)
    ·
      refine ⟨5051056650291259839329761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6734742200388346452439681 5051056650291259839329761)
      ·
        refine ⟨3788292487718444879497321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5051056650291259839329761 3788292487718444879497321)
        ·
          refine ⟨2841219365788833659622991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3788292487718444879497321 2841219365788833659622991)
          ·
            refine ⟨4261829048683250489434487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841219365788833659622991 4261829048683250489434487)
            ·
              refine ⟨6392743573024875734151731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261829048683250489434487 6392743573024875734151731)
              ·
                refine ⟨9589115359537313601227597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6392743573024875734151731 9589115359537313601227597)
                ·
                  refine ⟨3595918259826492600460349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9589115359537313601227597 3595918259826492600460349)
                  ·
                    refine ⟨1348469347434934725172631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3595918259826492600460349 1348469347434934725172631)
                    ·
                      rfl

theorem cell22_3939202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3939202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939202 prefixEnd_3939202 := by exact prefixLift 3939202
  have htrace : WordTrace (prefixWord ++ tailWord_3939202) baseStart_3939202 baseEnd_3939202 := by
    simpa [prefixWord, tailWord_3939202, baseEnd_3939202] using wordTrace_append hprefix tailTrace_3939202
  have hstable : (prefixWord ++ tailWord_3939202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939202).length < 2 ^ (prefixWord ++ tailWord_3939202).sum := by decide
  have hdescent : baseEnd_3939202 < baseStart_3939202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939209 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 6]
def baseStart_3939209 : Nat := 118140960795 + 3939209 * 2 ^ 59
def prefixEnd_3939209 : Nat := 4983230072969 + 3 ^ 40 * 3939209 * 2
def baseEnd_3939209 : Nat := 449490581225996346749203

theorem tailTrace_3939209 : CollatzResearch.WordTrace tailWord_3939209 prefixEnd_3939209 449490581225996346749203 := by
  unfold tailWord_3939209
  simp only [CollatzResearch.WordTrace]
  refine ⟨143674755585926031180884681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95783170390617354120589787 143674755585926031180884681)
  ·
    refine ⟨107756066689444523385663511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143674755585926031180884681 107756066689444523385663511)
    ·
      refine ⟨161634100034166785078495267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107756066689444523385663511 161634100034166785078495267)
      ·
        refine ⟨242451150051250177617742901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161634100034166785078495267 242451150051250177617742901)
        ·
          refine ⟨22729795317304704151663397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242451150051250177617742901 22729795317304704151663397)
          ·
            refine ⟨4261836621994632028436887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22729795317304704151663397 4261836621994632028436887)
            ·
              refine ⟨6392754932991948042655331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261836621994632028436887 6392754932991948042655331)
              ·
                refine ⟨9589132399487922063982997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6392754932991948042655331 9589132399487922063982997)
                ·
                  refine ⟨449490581225996346749203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9589132399487922063982997 449490581225996346749203)
                  ·
                    rfl

theorem cell22_3939209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 6].length) (baseStart_3939209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939209 prefixEnd_3939209 := by exact prefixLift 3939209
  have htrace : WordTrace (prefixWord ++ tailWord_3939209) baseStart_3939209 baseEnd_3939209 := by
    simpa [prefixWord, tailWord_3939209, baseEnd_3939209] using wordTrace_append hprefix tailTrace_3939209
  have hstable : (prefixWord ++ tailWord_3939209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939209).length < 2 ^ (prefixWord ++ tailWord_3939209).sum := by decide
  have hdescent : baseEnd_3939209 < baseStart_3939209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939228 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 1, 4]
def baseStart_3939228 : Nat := 118140960795 + 3939228 * 2 ^ 59
def prefixEnd_3939228 : Nat := 4983230072969 + 3 ^ 40 * 3939228 * 2
def baseEnd_3939228 : Nat := 1348478247766279324022551

theorem tailTrace_3939228 : CollatzResearch.WordTrace tailWord_3939228 prefixEnd_3939228 1348478247766279324022551 := by
  unfold tailWord_3939228
  simp only [CollatzResearch.WordTrace]
  refine ⟨71837724286428598712913169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95783632381904798283884225 71837724286428598712913169)
  ·
    refine ⟨53878293214821449034684877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71837724286428598712913169 53878293214821449034684877)
    ·
      refine ⟨20204359955558043388006829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53878293214821449034684877 20204359955558043388006829)
      ·
        refine ⟨7576634983334266270502561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20204359955558043388006829 7576634983334266270502561)
        ·
          refine ⟨5682476237500699702876921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7576634983334266270502561 5682476237500699702876921)
          ·
            refine ⟨4261857178125524777157691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5682476237500699702876921 4261857178125524777157691)
            ·
              refine ⟨6392785767188287165736537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261857178125524777157691 6392785767188287165736537)
              ·
                refine ⟨4794589325391215374302403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6392785767188287165736537 4794589325391215374302403)
                ·
                  refine ⟨7191883988086823061453605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794589325391215374302403 7191883988086823061453605)
                  ·
                    refine ⟨1348478247766279324022551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191883988086823061453605 1348478247766279324022551)
                    ·
                      rfl

theorem cell22_3939228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_3939228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939228 prefixEnd_3939228 := by exact prefixLift 3939228
  have htrace : WordTrace (prefixWord ++ tailWord_3939228) baseStart_3939228 baseEnd_3939228 := by
    simpa [prefixWord, tailWord_3939228, baseEnd_3939228] using wordTrace_append hprefix tailTrace_3939228
  have hstable : (prefixWord ++ tailWord_3939228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939228).length < 2 ^ (prefixWord ++ tailWord_3939228).sum := by decide
  have hdescent : baseEnd_3939228 < baseStart_3939228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939245 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_3939245 : Nat := 118140960795 + 3939245 * 2 ^ 59
def prefixEnd_3939245 : Nat := 4983230072969 + 3 ^ 40 * 3939245 * 2
def baseEnd_3939245 : Nat := 1348484067213696946347499

theorem tailTrace_3939245 : CollatzResearch.WordTrace tailWord_3939245 prefixEnd_3939245 1348484067213696946347499 := by
  unfold tailWord_3939245
  simp only [CollatzResearch.WordTrace]
  refine ⟨143676068613795609329195189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95784045742530406219463459 143676068613795609329195189)
  ·
    refine ⟨13469631432543338374612049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143676068613795609329195189 13469631432543338374612049)
    ·
      refine ⟨10102223574407503780959037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13469631432543338374612049 10102223574407503780959037)
      ·
        refine ⟨3788333840402813917859639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10102223574407503780959037 3788333840402813917859639)
        ·
          refine ⟨5682500760604220876789459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3788333840402813917859639 5682500760604220876789459)
          ·
            refine ⟨8523751140906331315184189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5682500760604220876789459 8523751140906331315184189)
            ·
              refine ⟨3196406677839874243194071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8523751140906331315184189 3196406677839874243194071)
              ·
                refine ⟨4794610016759811364791107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196406677839874243194071 4794610016759811364791107)
                ·
                  refine ⟨7191915025139717047186661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4794610016759811364791107 7191915025139717047186661)
                  ·
                    refine ⟨1348484067213696946347499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7191915025139717047186661 1348484067213696946347499)
                    ·
                      rfl

theorem cell22_3939245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_3939245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939245 prefixEnd_3939245 := by exact prefixLift 3939245
  have htrace : WordTrace (prefixWord ++ tailWord_3939245) baseStart_3939245 baseEnd_3939245 := by
    simpa [prefixWord, tailWord_3939245, baseEnd_3939245] using wordTrace_append hprefix tailTrace_3939245
  have hstable : (prefixWord ++ tailWord_3939245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939245).length < 2 ^ (prefixWord ++ tailWord_3939245).sum := by decide
  have hdescent : baseEnd_3939245 < baseStart_3939245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939297 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3939297 : Nat := 118140960795 + 3939297 * 2 ^ 59
def prefixEnd_3939297 : Nat := 4983230072969 + 3 ^ 40 * 3939297 * 2
def baseEnd_3939297 : Nat := 1348501867876386144047339

theorem tailTrace_3939297 : CollatzResearch.WordTrace tailWord_3939297 prefixEnd_3939297 1348501867876386144047339 := by
  unfold tailWord_3939297
  simp only [CollatzResearch.WordTrace]
  refine ⟨143677965209607222210088145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95785310139738148140058763 143677965209607222210088145)
  ·
    refine ⟨107758473907205416657566109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143677965209607222210088145 107758473907205416657566109)
    ·
      refine ⟨40409427715202031246587291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107758473907205416657566109 40409427715202031246587291)
      ·
        refine ⟨60614141572803046869880937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40409427715202031246587291 60614141572803046869880937)
        ·
          refine ⟨45460606179602285152410703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60614141572803046869880937 45460606179602285152410703)
          ·
            refine ⟨68190909269403427728616055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45460606179602285152410703 68190909269403427728616055)
            ·
              refine ⟨102286363904105141592924083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68190909269403427728616055 102286363904105141592924083)
              ·
                refine ⟨153429545856157712389386125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102286363904105141592924083 153429545856157712389386125)
                ·
                  refine ⟨57536079696059142146019797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153429545856157712389386125 57536079696059142146019797)
                  ·
                    refine ⟨1348501867876386144047339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57536079696059142146019797 1348501867876386144047339)
                    ·
                      rfl

theorem cell22_3939297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3939297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939297 prefixEnd_3939297 := by exact prefixLift 3939297
  have htrace : WordTrace (prefixWord ++ tailWord_3939297) baseStart_3939297 baseEnd_3939297 := by
    simpa [prefixWord, tailWord_3939297, baseEnd_3939297] using wordTrace_append hprefix tailTrace_3939297
  have hstable : (prefixWord ++ tailWord_3939297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939297).length < 2 ^ (prefixWord ++ tailWord_3939297).sum := by decide
  have hdescent : baseEnd_3939297 < baseStart_3939297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939303 : List Nat := [1, 1, 5, 2, 2, 1, 1, 5, 1, 3]
def baseStart_3939303 : Nat := 118140960795 + 3939303 * 2 ^ 59
def prefixEnd_3939303 : Nat := 4983230072969 + 3 ^ 40 * 3939303 * 2
def baseEnd_3939303 : Nat := 1348503921799004128397321

theorem tailTrace_3939303 : CollatzResearch.WordTrace tailWord_3939303 prefixEnd_3939303 1348503921799004128397321 := by
  unfold tailWord_3939303
  simp only [CollatzResearch.WordTrace]
  refine ⟨143678184047585485234806563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95785456031723656823204375 143678184047585485234806563)
  ·
    refine ⟨215517276071378227852209845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143678184047585485234806563 215517276071378227852209845)
    ·
      refine ⟨20204744631691708861144673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215517276071378227852209845 20204744631691708861144673)
      ·
        refine ⟨15153558473768781645858505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20204744631691708861144673 15153558473768781645858505)
        ·
          refine ⟨11365168855326586234393879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15153558473768781645858505 11365168855326586234393879)
          ·
            refine ⟨17047753282989879351590819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11365168855326586234393879 17047753282989879351590819)
            ·
              refine ⟨25571629924484819027386229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17047753282989879351590819 25571629924484819027386229)
              ·
                refine ⟨2397340305420451783817459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25571629924484819027386229 2397340305420451783817459)
                ·
                  refine ⟨3596010458130677675726189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397340305420451783817459 3596010458130677675726189)
                  ·
                    refine ⟨1348503921799004128397321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3596010458130677675726189 1348503921799004128397321)
                    ·
                      rfl

theorem cell22_3939303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_3939303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939303 prefixEnd_3939303 := by exact prefixLift 3939303
  have htrace : WordTrace (prefixWord ++ tailWord_3939303) baseStart_3939303 baseEnd_3939303 := by
    simpa [prefixWord, tailWord_3939303, baseEnd_3939303] using wordTrace_append hprefix tailTrace_3939303
  have hstable : (prefixWord ++ tailWord_3939303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939303).length < 2 ^ (prefixWord ++ tailWord_3939303).sum := by decide
  have hdescent : baseEnd_3939303 < baseStart_3939303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939376 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 2, 3]
def baseStart_3939376 : Nat := 118140960795 + 3939376 * 2 ^ 59
def prefixEnd_3939376 : Nat := 4983230072969 + 3 ^ 40 * 3939376 * 2
def baseEnd_3939376 : Nat := 1348528911190856271322097

theorem tailTrace_3939376 : CollatzResearch.WordTrace tailWord_3939376 prefixEnd_3939376 1348528911190856271322097 := by
  unfold tailWord_3939376
  simp only [CollatzResearch.WordTrace]
  refine ⟨71840423288160509351106991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95787231050880679134809321 71840423288160509351106991)
  ·
    refine ⟨107760634932240764026660487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71840423288160509351106991 107760634932240764026660487)
    ·
      refine ⟨161640952398361146039990731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107760634932240764026660487 161640952398361146039990731)
      ·
        refine ⟨242461428597541719059986097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161640952398361146039990731 242461428597541719059986097)
        ·
          refine ⟨181846071448156289294989573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242461428597541719059986097 181846071448156289294989573)
          ·
            refine ⟨34096138396529304242810545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181846071448156289294989573 34096138396529304242810545)
            ·
              refine ⟨25572103797396978182107909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34096138396529304242810545 25572103797396978182107909)
              ·
                refine ⟨4794769462011933409145233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25572103797396978182107909 4794769462011933409145233)
                ·
                  refine ⟨3596077096508950056858925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4794769462011933409145233 3596077096508950056858925)
                  ·
                    refine ⟨1348528911190856271322097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3596077096508950056858925 1348528911190856271322097)
                    ·
                      rfl

theorem cell22_3939376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2, 3].length) (baseStart_3939376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939376 prefixEnd_3939376 := by exact prefixLift 3939376
  have htrace : WordTrace (prefixWord ++ tailWord_3939376) baseStart_3939376 baseEnd_3939376 := by
    simpa [prefixWord, tailWord_3939376, baseEnd_3939376] using wordTrace_append hprefix tailTrace_3939376
  have hstable : (prefixWord ++ tailWord_3939376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939376).length < 2 ^ (prefixWord ++ tailWord_3939376).sum := by decide
  have hdescent : baseEnd_3939376 < baseStart_3939376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939378 : List Nat := [3, 2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_3939378 : Nat := 118140960795 + 3939378 * 2 ^ 59
def prefixEnd_3939378 : Nat := 4983230072969 + 3 ^ 40 * 3939378 * 2
def baseEnd_3939378 : Nat := 449509865277242977590697

theorem tailTrace_3939378 : CollatzResearch.WordTrace tailWord_3939378 prefixEnd_3939378 449509865277242977590697 := by
  unfold tailWord_3939378
  simp only [CollatzResearch.WordTrace]
  refine ⟨35920229880578443260946697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95787279681542515362524525 35920229880578443260946697)
  ·
    refine ⟨26940172410433832445710023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35920229880578443260946697 26940172410433832445710023)
    ·
      refine ⟨40410258615650748668565035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26940172410433832445710023 40410258615650748668565035)
      ·
        refine ⟨60615387923476123002847553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40410258615650748668565035 60615387923476123002847553)
        ·
          refine ⟨45461540942607092252135665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60615387923476123002847553 45461540942607092252135665)
          ·
            refine ⟨34096155706955319189101749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45461540942607092252135665 34096155706955319189101749)
            ·
              refine ⟨3196514597527061173978289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34096155706955319189101749 3196514597527061173978289)
              ·
                refine ⟨2397385948145295880483717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3196514597527061173978289 2397385948145295880483717)
                ·
                  refine ⟨449509865277242977590697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397385948145295880483717 449509865277242977590697)
                  ·
                    rfl

theorem cell22_3939378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_3939378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939378 prefixEnd_3939378 := by exact prefixLift 3939378
  have htrace : WordTrace (prefixWord ++ tailWord_3939378) baseStart_3939378 baseEnd_3939378 := by
    simpa [prefixWord, tailWord_3939378, baseEnd_3939378] using wordTrace_append hprefix tailTrace_3939378
  have hstable : (prefixWord ++ tailWord_3939378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939378).length < 2 ^ (prefixWord ++ tailWord_3939378).sum := by decide
  have hdescent : baseEnd_3939378 < baseStart_3939378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939389 : List Nat := [1, 4, 1, 3, 1, 2, 1, 9]
def baseStart_3939389 : Nat := 118140960795 + 3939389 * 2 ^ 59
def prefixEnd_3939389 : Nat := 4983230072969 + 3 ^ 40 * 3939389 * 2
def baseEnd_3939389 : Nat := 149837040150725396749673

theorem tailTrace_3939389 : CollatzResearch.WordTrace tailWord_3939389 prefixEnd_3939389 149837040150725396749673 := by
  unfold tailWord_3939389
  simp only [CollatzResearch.WordTrace]
  refine ⟨143681320725273921922437221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95787547150182614614958147 143681320725273921922437221)
  ·
    refine ⟨26940247635988860360456979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143681320725273921922437221 26940247635988860360456979)
    ·
      refine ⟨40410371453983290540685469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26940247635988860360456979 40410371453983290540685469)
      ·
        refine ⟨15153889295243733952757051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40410371453983290540685469 15153889295243733952757051)
        ·
          refine ⟨22730833942865600929135577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15153889295243733952757051 22730833942865600929135577)
          ·
            refine ⟨17048125457149200696851683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22730833942865600929135577 17048125457149200696851683)
            ·
              refine ⟨25572188185723801045277525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17048125457149200696851683 25572188185723801045277525)
              ·
                refine ⟨149837040150725396749673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25572188185723801045277525 149837040150725396749673)
                ·
                  rfl

theorem cell22_3939389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 9].length) (baseStart_3939389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939389 prefixEnd_3939389 := by exact prefixLift 3939389
  have htrace : WordTrace (prefixWord ++ tailWord_3939389) baseStart_3939389 baseEnd_3939389 := by
    simpa [prefixWord, tailWord_3939389, baseEnd_3939389] using wordTrace_append hprefix tailTrace_3939389
  have hstable : (prefixWord ++ tailWord_3939389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939389).length < 2 ^ (prefixWord ++ tailWord_3939389).sum := by decide
  have hdescent : baseEnd_3939389 < baseStart_3939389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939530 : List Nat := [3, 1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_3939530 : Nat := 118140960795 + 3939530 * 2 ^ 59
def prefixEnd_3939530 : Nat := 4983230072969 + 3 ^ 40 * 3939530 * 2
def baseEnd_3939530 : Nat := 449527209512683734323875

theorem tailTrace_3939530 : CollatzResearch.WordTrace tailWord_3939530 prefixEnd_3939530 449527209512683734323875 := by
  unfold tailWord_3939530
  simp only [CollatzResearch.WordTrace]
  refine ⟨35921615854440775750830011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95790975611842068668880029 35921615854440775750830011)
  ·
    refine ⟨53882423781661163626245017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35921615854440775750830011 53882423781661163626245017)
    ·
      refine ⟨40411817836245872719683763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53882423781661163626245017 40411817836245872719683763)
      ·
        refine ⟨60617726754368809079525645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40411817836245872719683763 60617726754368809079525645)
        ·
          refine ⟨22731647532888303404822117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60617726754368809079525645 22731647532888303404822117)
          ·
            refine ⟨4262183912416556888404147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22731647532888303404822117 4262183912416556888404147)
            ·
              refine ⟨6393275868624835332606221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262183912416556888404147 6393275868624835332606221)
              ·
                refine ⟨2397478450734313249727333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6393275868624835332606221 2397478450734313249727333)
                ·
                  refine ⟨449527209512683734323875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397478450734313249727333 449527209512683734323875)
                  ·
                    rfl

theorem cell22_3939530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_3939530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939530 prefixEnd_3939530 := by exact prefixLift 3939530
  have htrace : WordTrace (prefixWord ++ tailWord_3939530) baseStart_3939530 baseEnd_3939530 := by
    simpa [prefixWord, tailWord_3939530, baseEnd_3939530] using wordTrace_append hprefix tailTrace_3939530
  have hstable : (prefixWord ++ tailWord_3939530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939530).length < 2 ^ (prefixWord ++ tailWord_3939530).sum := by decide
  have hdescent : baseEnd_3939530 < baseStart_3939530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939539 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 1, 9]
def baseStart_3939539 : Nat := 118140960795 + 3939539 * 2 ^ 59
def prefixEnd_3939539 : Nat := 4983230072969 + 3 ^ 40 * 3939539 * 2
def baseEnd_3939539 : Nat := 1348584709421978179496597

theorem tailTrace_3939539 : CollatzResearch.WordTrace tailWord_3939539 prefixEnd_3939539 1348584709421978179496597 := by
  unfold tailWord_3939539
  simp only [CollatzResearch.WordTrace]
  refine ⟨143686791674730497540397671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95791194449820331693598447 143686791674730497540397671)
  ·
    refine ⟨215530187512095746310596507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143686791674730497540397671 215530187512095746310596507)
    ·
      refine ⟨323295281268143619465894761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215530187512095746310596507 323295281268143619465894761)
      ·
        refine ⟨242471460951107714599421071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323295281268143619465894761 242471460951107714599421071)
        ·
          refine ⟨363707191426661571899131607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242471460951107714599421071 363707191426661571899131607)
          ·
            refine ⟨545560787139992357848697411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363707191426661571899131607 545560787139992357848697411)
            ·
              refine ⟨818341180709988536773046117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545560787139992357848697411 818341180709988536773046117)
              ·
                refine ⟨153438971383122850644946147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 818341180709988536773046117 153438971383122850644946147)
                ·
                  refine ⟨230158457074684275967419221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153438971383122850644946147 230158457074684275967419221)
                  ·
                    refine ⟨1348584709421978179496597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 230158457074684275967419221 1348584709421978179496597)
                    ·
                      rfl

theorem cell22_3939539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_3939539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939539 prefixEnd_3939539 := by exact prefixLift 3939539
  have htrace : WordTrace (prefixWord ++ tailWord_3939539) baseStart_3939539 baseEnd_3939539 := by
    simpa [prefixWord, tailWord_3939539, baseEnd_3939539] using wordTrace_append hprefix tailTrace_3939539
  have hstable : (prefixWord ++ tailWord_3939539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939539).length < 2 ^ (prefixWord ++ tailWord_3939539).sum := by decide
  have hdescent : baseEnd_3939539 < baseStart_3939539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939541 : List Nat := [1, 3, 2, 4, 1, 1, 10]
def baseStart_3939541 : Nat := 118140960795 + 3939541 * 2 ^ 59
def prefixEnd_3939541 : Nat := 4983230072969 + 3 ^ 40 * 3939541 * 2
def baseEnd_3939541 : Nat := 49947607187512994109133

theorem tailTrace_3939541 : CollatzResearch.WordTrace tailWord_3939541 prefixEnd_3939541 49947607187512994109133 := by
  unfold tailWord_3939541
  simp only [CollatzResearch.WordTrace]
  refine ⟨143686864620723251881970477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95791243080482167921313651 143686864620723251881970477)
  ·
    refine ⟨53882574232771219455738929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143686864620723251881970477 53882574232771219455738929)
    ·
      refine ⟨40411930674578414591804197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53882574232771219455738929 40411930674578414591804197)
      ·
        refine ⟨7577237001483452735963287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40411930674578414591804197 7577237001483452735963287)
        ·
          refine ⟨11365855502225179103944931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7577237001483452735963287 11365855502225179103944931)
          ·
            refine ⟨17048783253337768655917397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11365855502225179103944931 17048783253337768655917397)
            ·
              refine ⟨49947607187512994109133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17048783253337768655917397 49947607187512994109133)
              ·
                rfl

theorem cell22_3939541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 10].length) (baseStart_3939541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939541 prefixEnd_3939541 := by exact prefixLift 3939541
  have htrace : WordTrace (prefixWord ++ tailWord_3939541) baseStart_3939541 baseEnd_3939541 := by
    simpa [prefixWord, tailWord_3939541, baseEnd_3939541] using wordTrace_append hprefix tailTrace_3939541
  have hstable : (prefixWord ++ tailWord_3939541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939541).length < 2 ^ (prefixWord ++ tailWord_3939541).sum := by decide
  have hdescent : baseEnd_3939541 < baseStart_3939541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939562 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 2, 3]
def baseStart_3939562 : Nat := 118140960795 + 3939562 * 2 ^ 59
def prefixEnd_3939562 : Nat := 4983230072969 + 3 ^ 40 * 3939562 * 2
def baseEnd_3939562 : Nat := 1348592582792013786171527

theorem tailTrace_3939562 : CollatzResearch.WordTrace tailWord_3939562 prefixEnd_3939562 1348592582792013786171527 := by
  unfold tailWord_3939562
  simp only [CollatzResearch.WordTrace]
  refine ⟨35921907638411793117121235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95791753702431448312323293 35921907638411793117121235)
  ·
    refine ⟨53882861457617689675681853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35921907638411793117121235 53882861457617689675681853)
    ·
      refine ⟨20206073046606633628380695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53882861457617689675681853 20206073046606633628380695)
      ·
        refine ⟨30309109569909950442571043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20206073046606633628380695 30309109569909950442571043)
        ·
          refine ⟨45463664354864925663856565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30309109569909950442571043 45463664354864925663856565)
          ·
            refine ⟨4262218533268586780986553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45463664354864925663856565 4262218533268586780986553)
            ·
              refine ⟨3196663899951440085739915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4262218533268586780986553 3196663899951440085739915)
              ·
                refine ⟨4794995849927160128609873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196663899951440085739915 4794995849927160128609873)
                ·
                  refine ⟨3596246887445370096457405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4794995849927160128609873 3596246887445370096457405)
                  ·
                    refine ⟨1348592582792013786171527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3596246887445370096457405 1348592582792013786171527)
                    ·
                      rfl

theorem cell22_3939562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_3939562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939562 prefixEnd_3939562 := by exact prefixLift 3939562
  have htrace : WordTrace (prefixWord ++ tailWord_3939562) baseStart_3939562 baseEnd_3939562 := by
    simpa [prefixWord, tailWord_3939562, baseEnd_3939562] using wordTrace_append hprefix tailTrace_3939562
  have hstable : (prefixWord ++ tailWord_3939562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939562).length < 2 ^ (prefixWord ++ tailWord_3939562).sum := by decide
  have hdescent : baseEnd_3939562 < baseStart_3939562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939601 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_3939601 : Nat := 118140960795 + 3939601 * 2 ^ 59
def prefixEnd_3939601 : Nat := 4983230072969 + 3 ^ 40 * 3939601 * 2
def baseEnd_3939601 : Nat := 1348605933289030684446407

theorem tailTrace_3939601 : CollatzResearch.WordTrace tailWord_3939601 prefixEnd_3939601 1348605933289030684446407 := by
  unfold tailWord_3939601
  simp only [CollatzResearch.WordTrace]
  refine ⟨143689053000505882129154657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95792702000337254752769771 143689053000505882129154657)
  ·
    refine ⟨107766789750379411596865993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143689053000505882129154657 107766789750379411596865993)
    ·
      refine ⟨80825092312784558697649495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107766789750379411596865993 80825092312784558697649495)
      ·
        refine ⟨121237638469176838046474243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80825092312784558697649495 121237638469176838046474243)
        ·
          refine ⟨181856457703765257069711365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121237638469176838046474243 181856457703765257069711365)
          ·
            refine ⟨34098085819455985700570881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181856457703765257069711365 34098085819455985700570881)
            ·
              refine ⟨25573564364591989275428161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34098085819455985700570881 25573564364591989275428161)
              ·
                refine ⟨19180173273443991956571121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25573564364591989275428161 19180173273443991956571121)
                ·
                  refine ⟨14385129955082993967428341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19180173273443991956571121 14385129955082993967428341)
                  ·
                    refine ⟨1348605933289030684446407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14385129955082993967428341 1348605933289030684446407)
                    ·
                      rfl

theorem cell22_3939601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_3939601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939601 prefixEnd_3939601 := by exact prefixLift 3939601
  have htrace : WordTrace (prefixWord ++ tailWord_3939601) baseStart_3939601 baseEnd_3939601 := by
    simpa [prefixWord, tailWord_3939601, baseEnd_3939601] using wordTrace_append hprefix tailTrace_3939601
  have hstable : (prefixWord ++ tailWord_3939601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939601).length < 2 ^ (prefixWord ++ tailWord_3939601).sum := by decide
  have hdescent : baseEnd_3939601 < baseStart_3939601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939633 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_3939633 : Nat := 118140960795 + 3939633 * 2 ^ 59
def prefixEnd_3939633 : Nat := 4983230072969 + 3 ^ 40 * 3939633 * 2
def baseEnd_3939633 : Nat := 1348616887542993267646309

theorem tailTrace_3939633 : CollatzResearch.WordTrace tailWord_3939633 prefixEnd_3939633 1348616887542993267646309 := by
  unfold tailWord_3939633
  simp only [CollatzResearch.WordTrace]
  refine ⟨143690220136389951594319553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95793480090926634396213035 143690220136389951594319553)
  ·
    refine ⟨107767665102292463695739665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143690220136389951594319553 107767665102292463695739665)
    ·
      refine ⟨80825748826719347771804749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107767665102292463695739665 80825748826719347771804749)
      ·
        refine ⟨30309655810019755414426781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80825748826719347771804749 30309655810019755414426781)
        ·
          refine ⟨11366120928757408280410043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30309655810019755414426781 11366120928757408280410043)
          ·
            refine ⟨17049181393136112420615065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11366120928757408280410043 17049181393136112420615065)
            ·
              refine ⟨12786886044852084315461299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17049181393136112420615065 12786886044852084315461299)
              ·
                refine ⟨19180329067278126473191949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12786886044852084315461299 19180329067278126473191949)
                ·
                  refine ⟨7192623400229297427446981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19180329067278126473191949 7192623400229297427446981)
                  ·
                    refine ⟨1348616887542993267646309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7192623400229297427446981 1348616887542993267646309)
                    ·
                      rfl

theorem cell22_3939633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_3939633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939633 prefixEnd_3939633 := by exact prefixLift 3939633
  have htrace : WordTrace (prefixWord ++ tailWord_3939633) baseStart_3939633 baseEnd_3939633 := by
    simpa [prefixWord, tailWord_3939633, baseEnd_3939633] using wordTrace_append hprefix tailTrace_3939633
  have hstable : (prefixWord ++ tailWord_3939633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939633).length < 2 ^ (prefixWord ++ tailWord_3939633).sum := by decide
  have hdescent : baseEnd_3939633 < baseStart_3939633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939680 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 1, 5]
def baseStart_3939680 : Nat := 118140960795 + 3939680 * 2 ^ 59
def prefixEnd_3939680 : Nat := 4983230072969 + 3 ^ 40 * 3939680 * 2
def baseEnd_3939680 : Nat := 1348632976603500811721165

theorem tailTrace_3939680 : CollatzResearch.WordTrace tailWord_3939680 prefixEnd_3939680 1348632976603500811721165 := by
  unfold tailWord_3939680
  simp only [CollatzResearch.WordTrace]
  refine ⟨71845967183609839310640247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95794622911479785747520329 71845967183609839310640247)
  ·
    refine ⟨107768950775414758965960371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71845967183609839310640247 107768950775414758965960371)
    ·
      refine ⟨161653426163122138448940557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107768950775414758965960371 161653426163122138448940557)
      ·
        refine ⟨60620034811170801918352709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161653426163122138448940557 60620034811170801918352709)
        ·
          refine ⟨11366256527094525359691133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60620034811170801918352709 11366256527094525359691133)
          ·
            refine ⟨4262346197660447009884175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11366256527094525359691133 4262346197660447009884175)
            ·
              refine ⟨6393519296490670514826263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262346197660447009884175 6393519296490670514826263)
              ·
                refine ⟨9590278944736005772239395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6393519296490670514826263 9590278944736005772239395)
                ·
                  refine ⟨14385418417104008658359093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9590278944736005772239395 14385418417104008658359093)
                  ·
                    refine ⟨1348632976603500811721165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14385418417104008658359093 1348632976603500811721165)
                    ·
                      rfl

theorem cell22_3939680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 5].length) (baseStart_3939680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939680 prefixEnd_3939680 := by exact prefixLift 3939680
  have htrace : WordTrace (prefixWord ++ tailWord_3939680) baseStart_3939680 baseEnd_3939680 := by
    simpa [prefixWord, tailWord_3939680, baseEnd_3939680] using wordTrace_append hprefix tailTrace_3939680
  have hstable : (prefixWord ++ tailWord_3939680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939680).length < 2 ^ (prefixWord ++ tailWord_3939680).sum := by decide
  have hdescent : baseEnd_3939680 < baseStart_3939680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939693 : List Nat := [1, 5, 1, 1, 1, 4, 1, 8]
def baseStart_3939693 : Nat := 118140960795 + 3939693 * 2 ^ 59
def prefixEnd_3939693 : Nat := 4983230072969 + 3 ^ 40 * 3939693 * 2
def baseEnd_3939693 : Nat := 149848602974352567905125

theorem tailTrace_3939693 : CollatzResearch.WordTrace tailWord_3939693 prefixEnd_3939693 149848602974352567905125 := by
  unfold tailWord_3939693
  simp only [CollatzResearch.WordTrace]
  refine ⟨143692408516172581841503733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95794939010781721227669155 143692408516172581841503733)
  ·
    refine ⟨13471163298391179547640975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143692408516172581841503733 13471163298391179547640975)
    ·
      refine ⟨20206744947586769321461463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13471163298391179547640975 20206744947586769321461463)
      ·
        refine ⟨30310117421380153982192195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20206744947586769321461463 30310117421380153982192195)
        ·
          refine ⟨45465176132070230973288293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30310117421380153982192195 45465176132070230973288293)
          ·
            refine ⟨8524720524763168307491555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45465176132070230973288293 8524720524763168307491555)
            ·
              refine ⟨12787080787144752461237333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524720524763168307491555 12787080787144752461237333)
              ·
                refine ⟨149848602974352567905125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12787080787144752461237333 149848602974352567905125)
                ·
                  rfl

theorem cell22_3939693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 8].length) (baseStart_3939693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939693 prefixEnd_3939693 := by exact prefixLift 3939693
  have htrace : WordTrace (prefixWord ++ tailWord_3939693) baseStart_3939693 baseEnd_3939693 := by
    simpa [prefixWord, tailWord_3939693, baseEnd_3939693] using wordTrace_append hprefix tailTrace_3939693
  have hstable : (prefixWord ++ tailWord_3939693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939693).length < 2 ^ (prefixWord ++ tailWord_3939693).sum := by decide
  have hdescent : baseEnd_3939693 < baseStart_3939693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939772 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 5]
def baseStart_3939772 : Nat := 118140960795 + 3939772 * 2 ^ 59
def prefixEnd_3939772 : Nat := 4983230072969 + 3 ^ 40 * 3939772 * 2
def baseEnd_3939772 : Nat := 449554823361214412806961

theorem tailTrace_3939772 : CollatzResearch.WordTrace tailWord_3939772 prefixEnd_3939772 449554823361214412806961 := by
  unfold tailWord_3939772
  simp only [CollatzResearch.WordTrace]
  refine ⟨71847644941443189166814785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95796859921924252222419713 71847644941443189166814785)
  ·
    refine ⟨53885733706082391875111089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71847644941443189166814785 53885733706082391875111089)
    ·
      refine ⟨40414300279561793906333317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53885733706082391875111089 40414300279561793906333317)
      ·
        refine ⟨7577681302417836357437497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40414300279561793906333317 7577681302417836357437497)
        ·
          refine ⟨5683260976813377268078123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7577681302417836357437497 5683260976813377268078123)
          ·
            refine ⟨8524891465220065902117185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5683260976813377268078123 8524891465220065902117185)
            ·
              refine ⟨6393668598915049426587889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8524891465220065902117185 6393668598915049426587889)
              ·
                refine ⟨4795251449186287069940917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6393668598915049426587889 4795251449186287069940917)
                ·
                  refine ⟨449554823361214412806961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4795251449186287069940917 449554823361214412806961)
                  ·
                    rfl

theorem cell22_3939772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_3939772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939772 prefixEnd_3939772 := by exact prefixLift 3939772
  have htrace : WordTrace (prefixWord ++ tailWord_3939772) baseStart_3939772 baseEnd_3939772 := by
    simpa [prefixWord, tailWord_3939772, baseEnd_3939772] using wordTrace_append hprefix tailTrace_3939772
  have hstable : (prefixWord ++ tailWord_3939772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939772).length < 2 ^ (prefixWord ++ tailWord_3939772).sum := by decide
  have hdescent : baseEnd_3939772 < baseStart_3939772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939778 : List Nat := [3, 5, 2, 1, 2, 1, 1, 7]
def baseStart_3939778 : Nat := 118140960795 + 3939778 * 2 ^ 59
def prefixEnd_3939778 : Nat := 4983230072969 + 3 ^ 40 * 3939778 * 2
def baseEnd_3939778 : Nat := 149851836000695691418985

theorem tailTrace_3939778 : CollatzResearch.WordTrace tailWord_3939778 prefixEnd_3939778 149851836000695691418985 := by
  unfold tailWord_3939778
  simp only [CollatzResearch.WordTrace]
  refine ⟨35923877180216160339586997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95797005813909760905565325 35923877180216160339586997)
  ·
    refine ⟨3367863485645265031836281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35923877180216160339586997 3367863485645265031836281)
    ·
      refine ⟨2525897614233948773877211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3367863485645265031836281 2525897614233948773877211)
      ·
        refine ⟨3788846421350923160815817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525897614233948773877211 3788846421350923160815817)
        ·
          refine ⟨2841634816013192370611863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3788846421350923160815817 2841634816013192370611863)
          ·
            refine ⟨4262452224019788555917795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841634816013192370611863 4262452224019788555917795)
            ·
              refine ⟨6393678336029682833876693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262452224019788555917795 6393678336029682833876693)
              ·
                refine ⟨149851836000695691418985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6393678336029682833876693 149851836000695691418985)
                ·
                  rfl

theorem cell22_3939778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_3939778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939778 prefixEnd_3939778 := by exact prefixLift 3939778
  have htrace : WordTrace (prefixWord ++ tailWord_3939778) baseStart_3939778 baseEnd_3939778 := by
    simpa [prefixWord, tailWord_3939778, baseEnd_3939778] using wordTrace_append hprefix tailTrace_3939778
  have hstable : (prefixWord ++ tailWord_3939778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939778).length < 2 ^ (prefixWord ++ tailWord_3939778).sum := by decide
  have hdescent : baseEnd_3939778 < baseStart_3939778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939783 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 6]
def baseStart_3939783 : Nat := 118140960795 + 3939783 * 2 ^ 59
def prefixEnd_3939783 : Nat := 4983230072969 + 3 ^ 40 * 3939783 * 2
def baseEnd_3939783 : Nat := 449556078536147625465283

theorem tailTrace_3939783 : CollatzResearch.WordTrace tailWord_3939783 prefixEnd_3939783 449556078536147625465283 := by
  unfold tailWord_3939783
  simp only [CollatzResearch.WordTrace]
  refine ⟨143695691085846527212280003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95797127390564351474853335 143695691085846527212280003)
  ·
    refine ⟨215543536628769790818420005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143695691085846527212280003 215543536628769790818420005)
    ·
      refine ⟨40414413117894335778453751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215543536628769790818420005 40414413117894335778453751)
      ·
        refine ⟨60621619676841503667680627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40414413117894335778453751 60621619676841503667680627)
        ·
          refine ⟨90932429515262255501520941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60621619676841503667680627 90932429515262255501520941)
          ·
            refine ⟨34099661068223345813070353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90932429515262255501520941 34099661068223345813070353)
            ·
              refine ⟨25574745801167509359802765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34099661068223345813070353 25574745801167509359802765)
              ·
                refine ⟨9590529675437816009926037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25574745801167509359802765 9590529675437816009926037)
                ·
                  refine ⟨449556078536147625465283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9590529675437816009926037 449556078536147625465283)
                  ·
                    rfl

theorem cell22_3939783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 6].length) (baseStart_3939783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939783 prefixEnd_3939783 := by exact prefixLift 3939783
  have htrace : WordTrace (prefixWord ++ tailWord_3939783) baseStart_3939783 baseEnd_3939783 := by
    simpa [prefixWord, tailWord_3939783, baseEnd_3939783] using wordTrace_append hprefix tailTrace_3939783
  have hstable : (prefixWord ++ tailWord_3939783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939783).length < 2 ^ (prefixWord ++ tailWord_3939783).sum := by decide
  have hdescent : baseEnd_3939783 < baseStart_3939783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939815 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 1, 5]
def baseStart_3939815 : Nat := 118140960795 + 3939815 * 2 ^ 59
def prefixEnd_3939815 : Nat := 4983230072969 + 3 ^ 40 * 3939815 * 2
def baseEnd_3939815 : Nat := 1348679189862405459595751

theorem tailTrace_3939815 : CollatzResearch.WordTrace tailWord_3939815 prefixEnd_3939815 1348679189862405459595751 := by
  unfold tailWord_3939815
  simp only [CollatzResearch.WordTrace]
  refine ⟨143696858221730596677444899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95797905481153731118296599 143696858221730596677444899)
  ·
    refine ⟨215545287332595895016167349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143696858221730596677444899 215545287332595895016167349)
    ·
      refine ⟨20207370687430865157765689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215545287332595895016167349 20207370687430865157765689)
      ·
        refine ⟨15155528015573148868324267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20207370687430865157765689 15155528015573148868324267)
        ·
          refine ⟨22733292023359723302486401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15155528015573148868324267 22733292023359723302486401)
          ·
            refine ⟨17049969017519792476864801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22733292023359723302486401 17049969017519792476864801)
            ·
              refine ⟨12787476763139844357648601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17049969017519792476864801 12787476763139844357648601)
              ·
                refine ⟨9590607572354883268236451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12787476763139844357648601 9590607572354883268236451)
                ·
                  refine ⟨14385911358532324902354677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9590607572354883268236451 14385911358532324902354677)
                  ·
                    refine ⟨1348679189862405459595751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14385911358532324902354677 1348679189862405459595751)
                    ·
                      rfl

theorem cell22_3939815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_3939815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939815 prefixEnd_3939815 := by exact prefixLift 3939815
  have htrace : WordTrace (prefixWord ++ tailWord_3939815) baseStart_3939815 baseEnd_3939815 := by
    simpa [prefixWord, tailWord_3939815, baseEnd_3939815] using wordTrace_append hprefix tailTrace_3939815
  have hstable : (prefixWord ++ tailWord_3939815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939815).length < 2 ^ (prefixWord ++ tailWord_3939815).sum := by decide
  have hdescent : baseEnd_3939815 < baseStart_3939815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939832 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 2, 3]
def baseStart_3939832 : Nat := 118140960795 + 3939832 * 2 ^ 59
def prefixEnd_3939832 : Nat := 4983230072969 + 3 ^ 40 * 3939832 * 2
def baseEnd_3939832 : Nat := 1348685009309823081920699

theorem tailTrace_3939832 : CollatzResearch.WordTrace tailWord_3939832 prefixEnd_3939832 1348685009309823081920699 := by
  unfold tailWord_3939832
  simp only [CollatzResearch.WordTrace]
  refine ⟨71848739131334504290406875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95798318841779339053875833 71848739131334504290406875)
  ·
    refine ⟨107773108697001756435610313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71848739131334504290406875 107773108697001756435610313)
    ·
      refine ⟨80829831522751317326707735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107773108697001756435610313 80829831522751317326707735)
      ·
        refine ⟨121244747284126975990061603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80829831522751317326707735 121244747284126975990061603)
        ·
          refine ⟨181867120926190463985092405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121244747284126975990061603 181867120926190463985092405)
          ·
            refine ⟨17050042586830355998602413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181867120926190463985092405 17050042586830355998602413)
            ·
              refine ⟨6393765970061383499475905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17050042586830355998602413 6393765970061383499475905)
              ·
                refine ⟨4795324477546037624606929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6393765970061383499475905 4795324477546037624606929)
                ·
                  refine ⟨3596493358159528218455197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4795324477546037624606929 3596493358159528218455197)
                  ·
                    refine ⟨1348685009309823081920699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3596493358159528218455197 1348685009309823081920699)
                    ·
                      rfl

theorem cell22_3939832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_3939832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939832 prefixEnd_3939832 := by exact prefixLift 3939832
  have htrace : WordTrace (prefixWord ++ tailWord_3939832) baseStart_3939832 baseEnd_3939832 := by
    simpa [prefixWord, tailWord_3939832, baseEnd_3939832] using wordTrace_append hprefix tailTrace_3939832
  have hstable : (prefixWord ++ tailWord_3939832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939832).length < 2 ^ (prefixWord ++ tailWord_3939832).sum := by decide
  have hdescent : baseEnd_3939832 < baseStart_3939832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939890 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_3939890 : Nat := 118140960795 + 3939890 * 2 ^ 59
def prefixEnd_3939890 : Nat := 4983230072969 + 3 ^ 40 * 3939890 * 2
def baseEnd_3939890 : Nat := 449568287965043421323507

theorem tailTrace_3939890 : CollatzResearch.WordTrace tailWord_3939890 prefixEnd_3939890 449568287965043421323507 := by
  unfold tailWord_3939890
  simp only [CollatzResearch.WordTrace]
  refine ⟨35924898424114721121606281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95799729130972589657616749 35924898424114721121606281)
  ·
    refine ⟨26943673818086040841204711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35924898424114721121606281 26943673818086040841204711)
    ·
      refine ⟨40415510727129061261807067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26943673818086040841204711 40415510727129061261807067)
      ·
        refine ⟨60623266090693591892710601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40415510727129061261807067 60623266090693591892710601)
        ·
          refine ⟨45467449568020193919532951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60623266090693591892710601 45467449568020193919532951)
          ·
            refine ⟨68201174352030290879299427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45467449568020193919532951 68201174352030290879299427)
            ·
              refine ⟨102301761528045436318949141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68201174352030290879299427 102301761528045436318949141)
              ·
                refine ⟨4795395071627129827450741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102301761528045436318949141 4795395071627129827450741)
                ·
                  refine ⟨449568287965043421323507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4795395071627129827450741 449568287965043421323507)
                  ·
                    rfl

theorem cell22_3939890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_3939890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939890 prefixEnd_3939890 := by exact prefixLift 3939890
  have htrace : WordTrace (prefixWord ++ tailWord_3939890) baseStart_3939890 baseEnd_3939890 := by
    simpa [prefixWord, tailWord_3939890, baseEnd_3939890] using wordTrace_append hprefix tailTrace_3939890
  have hstable : (prefixWord ++ tailWord_3939890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939890).length < 2 ^ (prefixWord ++ tailWord_3939890).sum := by decide
  have hdescent : baseEnd_3939890 < baseStart_3939890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939905 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3939905 : Nat := 118140960795 + 3939905 * 2 ^ 59
def prefixEnd_3939905 : Nat := 4983230072969 + 3 ^ 40 * 3939905 * 2
def baseEnd_3939905 : Nat := 1348709998701675224845475

theorem tailTrace_3939905 : CollatzResearch.WordTrace tailWord_3939905 prefixEnd_3939905 1348709998701675224845475 := by
  unfold tailWord_3939905
  simp only [CollatzResearch.WordTrace]
  refine ⟨143700140791404542048221169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95800093860936361365480779 143700140791404542048221169)
  ·
    refine ⟨107775105593553406536165877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143700140791404542048221169 107775105593553406536165877)
    ·
      refine ⟨10103916149395631862765551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107775105593553406536165877 10103916149395631862765551)
      ·
        refine ⟨15155874224093447794148327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10103916149395631862765551 15155874224093447794148327)
        ·
          refine ⟨22733811336140171691222491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15155874224093447794148327 22733811336140171691222491)
          ·
            refine ⟨34100717004210257536833737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22733811336140171691222491 34100717004210257536833737)
            ·
              refine ⟨25575537753157693152625303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34100717004210257536833737 25575537753157693152625303)
              ·
                refine ⟨38363306629736539728937955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25575537753157693152625303 38363306629736539728937955)
                ·
                  refine ⟨57544959944604809593406933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38363306629736539728937955 57544959944604809593406933)
                  ·
                    refine ⟨1348709998701675224845475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57544959944604809593406933 1348709998701675224845475)
                    ·
                      rfl

theorem cell22_3939905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3939905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939905 prefixEnd_3939905 := by exact prefixLift 3939905
  have htrace : WordTrace (prefixWord ++ tailWord_3939905) baseStart_3939905 baseEnd_3939905 := by
    simpa [prefixWord, tailWord_3939905, baseEnd_3939905] using wordTrace_append hprefix tailTrace_3939905
  have hstable : (prefixWord ++ tailWord_3939905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939905).length < 2 ^ (prefixWord ++ tailWord_3939905).sum := by decide
  have hdescent : baseEnd_3939905 < baseStart_3939905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939920 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_3939920 : Nat := 118140960795 + 3939920 * 2 ^ 59
def prefixEnd_3939920 : Nat := 4983230072969 + 3 ^ 40 * 3939920 * 2
def baseEnd_3939920 : Nat := 1348715133508220185720429

theorem tailTrace_3939920 : CollatzResearch.WordTrace tailWord_3939920 prefixEnd_3939920 1348715133508220185720429 := by
  unfold tailWord_3939920
  simp only [CollatzResearch.WordTrace]
  refine ⟨71850343943175099805008607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95800458590900133073344809 71850343943175099805008607)
  ·
    refine ⟨107775515914762649707512911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71850343943175099805008607 107775515914762649707512911)
    ·
      refine ⟨161663273872143974561269367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107775515914762649707512911 161663273872143974561269367)
      ·
        refine ⟨242494910808215961841904051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161663273872143974561269367 242494910808215961841904051)
        ·
          refine ⟨363742366212323942762856077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242494910808215961841904051 363742366212323942762856077)
          ·
            refine ⟨136403387329621478536071029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363742366212323942762856077 136403387329621478536071029)
            ·
              refine ⟨12787817562152013612756659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136403387329621478536071029 12787817562152013612756659)
              ·
                refine ⟨19181726343228020419134989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12787817562152013612756659 19181726343228020419134989)
                ·
                  refine ⟨7193147378710507657175621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19181726343228020419134989 7193147378710507657175621)
                  ·
                    refine ⟨1348715133508220185720429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7193147378710507657175621 1348715133508220185720429)
                    ·
                      rfl

theorem cell22_3939920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_3939920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939920 prefixEnd_3939920 := by exact prefixLift 3939920
  have htrace : WordTrace (prefixWord ++ tailWord_3939920) baseStart_3939920 baseEnd_3939920 := by
    simpa [prefixWord, tailWord_3939920, baseEnd_3939920] using wordTrace_append hprefix tailTrace_3939920
  have hstable : (prefixWord ++ tailWord_3939920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939920).length < 2 ^ (prefixWord ++ tailWord_3939920).sum := by decide
  have hdescent : baseEnd_3939920 < baseStart_3939920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939982 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_3939982 : Nat := 118140960795 + 3939982 * 2 ^ 59
def prefixEnd_3939982 : Nat := 4983230072969 + 3 ^ 40 * 3939982 * 2
def baseEnd_3939982 : Nat := 1348736357375272690670239

theorem tailTrace_3939982 : CollatzResearch.WordTrace tailWord_3939982 prefixEnd_3939982 1348736357375272690670239 := by
  unfold tailWord_3939982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17962868651515698024846775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95801966141417056132516133 17962868651515698024846775)
  ·
    refine ⟨26944302977273547037270163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17962868651515698024846775 26944302977273547037270163)
    ·
      refine ⟨40416454465910320555905245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26944302977273547037270163 40416454465910320555905245)
      ·
        refine ⟨15156170424716370208464467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40416454465910320555905245 15156170424716370208464467)
        ·
          refine ⟨22734255637074555312696701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15156170424716370208464467 22734255637074555312696701)
          ·
            refine ⟨8525345863902958242261263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22734255637074555312696701 8525345863902958242261263)
            ·
              refine ⟨12788018795854437363391895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8525345863902958242261263 12788018795854437363391895)
              ·
                refine ⟨19182028193781656045087843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12788018795854437363391895 19182028193781656045087843)
                ·
                  refine ⟨28773042290672484067631765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19182028193781656045087843 28773042290672484067631765)
                  ·
                    refine ⟨1348736357375272690670239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28773042290672484067631765 1348736357375272690670239)
                    ·
                      rfl

theorem cell22_3939982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_3939982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939982 prefixEnd_3939982 := by exact prefixLift 3939982
  have htrace : WordTrace (prefixWord ++ tailWord_3939982) baseStart_3939982 baseEnd_3939982 := by
    simpa [prefixWord, tailWord_3939982, baseEnd_3939982] using wordTrace_append hprefix tailTrace_3939982
  have hstable : (prefixWord ++ tailWord_3939982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939982).length < 2 ^ (prefixWord ++ tailWord_3939982).sum := by decide
  have hdescent : baseEnd_3939982 < baseStart_3939982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939986 : List Nat := [3, 2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_3939986 : Nat := 118140960795 + 3939986 * 2 ^ 59
def prefixEnd_3939986 : Nat := 4983230072969 + 3 ^ 40 * 3939986 * 2
def baseEnd_3939986 : Nat := 449579242219006004523409

theorem tailTrace_3939986 : CollatzResearch.WordTrace tailWord_3939986 prefixEnd_3939986 449579242219006004523409 := by
  unfold tailWord_3939986
  simp only [CollatzResearch.WordTrace]
  refine ⟨35925773776027773220479953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95802063402740728587946541 35925773776027773220479953)
  ·
    refine ⟨26944330332020829915359965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35925773776027773220479953 26944330332020829915359965)
    ·
      refine ⟨10104123874507811218259987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26944330332020829915359965 10104123874507811218259987)
      ·
        refine ⟨15156185811761716827389981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104123874507811218259987 15156185811761716827389981)
        ·
          refine ⟨5683569679410643810271243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15156185811761716827389981 5683569679410643810271243)
          ·
            refine ⟨8525354519115965715406865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5683569679410643810271243 8525354519115965715406865)
            ·
              refine ⟨6394015889336974286555149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8525354519115965715406865 6394015889336974286555149)
              ·
                refine ⟨2397755958501365357458181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6394015889336974286555149 2397755958501365357458181)
                ·
                  refine ⟨449579242219006004523409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397755958501365357458181 449579242219006004523409)
                  ·
                    rfl

theorem cell22_3939986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_3939986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939986 prefixEnd_3939986 := by exact prefixLift 3939986
  have htrace : WordTrace (prefixWord ++ tailWord_3939986) baseStart_3939986 baseEnd_3939986 := by
    simpa [prefixWord, tailWord_3939986, baseEnd_3939986] using wordTrace_append hprefix tailTrace_3939986
  have hstable : (prefixWord ++ tailWord_3939986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939986).length < 2 ^ (prefixWord ++ tailWord_3939986).sum := by decide
  have hdescent : baseEnd_3939986 < baseStart_3939986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939988 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_3939988 : Nat := 118140960795 + 3939988 * 2 ^ 59
def prefixEnd_3939988 : Nat := 4983230072969 + 3 ^ 40 * 3939988 * 2
def baseEnd_3939988 : Nat := 1348738411297890675020221

theorem tailTrace_3939988 : CollatzResearch.WordTrace tailWord_3939988 prefixEnd_3939988 1348738411297890675020221 := by
  unfold tailWord_3939988
  simp only [CollatzResearch.WordTrace]
  refine ⟨71851584025051923611746309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95802112033402564815661745 71851584025051923611746309)
  ·
    refine ⟨13472172004697235677202433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71851584025051923611746309 13472172004697235677202433)
    ·
      refine ⟨10104129003522926757901825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13472172004697235677202433 10104129003522926757901825)
      ·
        refine ⟨7578096752642195068426369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10104129003522926757901825 7578096752642195068426369)
        ·
          refine ⟨5683572564481646301319777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7578096752642195068426369 5683572564481646301319777)
          ·
            refine ⟨4262679423361234725989833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5683572564481646301319777 4262679423361234725989833)
            ·
              refine ⟨3197009567520926044492375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4262679423361234725989833 3197009567520926044492375)
              ·
                refine ⟨4795514351281389066738563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197009567520926044492375 4795514351281389066738563)
                ·
                  refine ⟨7193271526922083600107845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795514351281389066738563 7193271526922083600107845)
                  ·
                    refine ⟨1348738411297890675020221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7193271526922083600107845 1348738411297890675020221)
                    ·
                      rfl

theorem cell22_3939988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_3939988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3939988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3939988 prefixEnd_3939988 := by exact prefixLift 3939988
  have htrace : WordTrace (prefixWord ++ tailWord_3939988) baseStart_3939988 baseEnd_3939988 := by
    simpa [prefixWord, tailWord_3939988, baseEnd_3939988] using wordTrace_append hprefix tailTrace_3939988
  have hstable : (prefixWord ++ tailWord_3939988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939988).length < 2 ^ (prefixWord ++ tailWord_3939988).sum := by decide
  have hdescent : baseEnd_3939988 < baseStart_3939988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940001 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 2, 3]
def baseStart_3940001 : Nat := 118140960795 + 3940001 * 2 ^ 59
def prefixEnd_3940001 : Nat := 4983230072969 + 3 ^ 40 * 3940001 * 2
def baseEnd_3940001 : Nat := 1348742861463562974445181

theorem tailTrace_3940001 : CollatzResearch.WordTrace tailWord_3940001 prefixEnd_3940001 1348742861463562974445181 := by
  unfold tailWord_3940001
  simp only [CollatzResearch.WordTrace]
  refine ⟨143703642199056750443715857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95802428132704500295810571 143703642199056750443715857)
  ·
    refine ⟨107777731649292562832786893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143703642199056750443715857 107777731649292562832786893)
    ·
      refine ⟨40416649368484711062295085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107777731649292562832786893 40416649368484711062295085)
      ·
        refine ⟨15156243513181766648360657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40416649368484711062295085 15156243513181766648360657)
        ·
          refine ⟨11367182634886324986270493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15156243513181766648360657 11367182634886324986270493)
          ·
            refine ⟨4262693488082371869851435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11367182634886324986270493 4262693488082371869851435)
            ·
              refine ⟨6394040232123557804777153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262693488082371869851435 6394040232123557804777153)
              ·
                refine ⟨4795530174092668353582865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6394040232123557804777153 4795530174092668353582865)
                ·
                  refine ⟨3596647630569501265187149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4795530174092668353582865 3596647630569501265187149)
                  ·
                    refine ⟨1348742861463562974445181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3596647630569501265187149 1348742861463562974445181)
                    ·
                      rfl

theorem cell22_3940001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_3940001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940001 prefixEnd_3940001 := by exact prefixLift 3940001
  have htrace : WordTrace (prefixWord ++ tailWord_3940001) baseStart_3940001 baseEnd_3940001 := by
    simpa [prefixWord, tailWord_3940001, baseEnd_3940001] using wordTrace_append hprefix tailTrace_3940001
  have hstable : (prefixWord ++ tailWord_3940001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940001).length < 2 ^ (prefixWord ++ tailWord_3940001).sum := by decide
  have hdescent : baseEnd_3940001 < baseStart_3940001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940104 : List Nat := [2, 1, 3, 2, 2, 1, 2, 5, 4]
def baseStart_3940104 : Nat := 118140960795 + 3940104 * 2 ^ 59
def prefixEnd_3940104 : Nat := 4983230072969 + 3 ^ 40 * 3940104 * 2
def baseEnd_3940104 : Nat := 449592706822835013039955

theorem tailTrace_3940104 : CollatzResearch.WordTrace tailWord_3940104 prefixEnd_3940104 449592706822835013039955 := by
  unfold tailWord_3940104
  simp only [CollatzResearch.WordTrace]
  refine ⟨71853699458841799517357683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95804932611789066023143577 71853699458841799517357683)
  ·
    refine ⟨107780549188262699276036525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71853699458841799517357683 107780549188262699276036525)
    ·
      refine ⟨40417705945598512228513697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107780549188262699276036525 40417705945598512228513697)
      ·
        refine ⟨30313279459198884171385273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40417705945598512228513697 30313279459198884171385273)
        ·
          refine ⟨22734959594399163128538955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30313279459198884171385273 22734959594399163128538955)
          ·
            refine ⟨34102439391598744692808433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22734959594399163128538955 34102439391598744692808433)
            ·
              refine ⟨25576829543699058519606325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34102439391598744692808433 25576829543699058519606325)
              ·
                refine ⟨2397827769721786736213093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25576829543699058519606325 2397827769721786736213093)
                ·
                  refine ⟨449592706822835013039955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397827769721786736213093 449592706822835013039955)
                  ·
                    rfl

theorem cell22_3940104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 4].length) (baseStart_3940104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940104 prefixEnd_3940104 := by exact prefixLift 3940104
  have htrace : WordTrace (prefixWord ++ tailWord_3940104) baseStart_3940104 baseEnd_3940104 := by
    simpa [prefixWord, tailWord_3940104, baseEnd_3940104] using wordTrace_append hprefix tailTrace_3940104
  have hstable : (prefixWord ++ tailWord_3940104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940104).length < 2 ^ (prefixWord ++ tailWord_3940104).sum := by decide
  have hdescent : baseEnd_3940104 < baseStart_3940104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940106 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 1, 4]
def baseStart_3940106 : Nat := 118140960795 + 3940106 * 2 ^ 59
def prefixEnd_3940106 : Nat := 4983230072969 + 3 ^ 40 * 3940106 * 2
def baseEnd_3940106 : Nat := 1348778805109377700569859

theorem tailTrace_3940106 : CollatzResearch.WordTrace tailWord_3940106 prefixEnd_3940106 1348778805109377700569859 := by
  unfold tailWord_3940106
  simp only [CollatzResearch.WordTrace]
  refine ⟨35926867965919088344072043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95804981242450902250858781 35926867965919088344072043)
  ·
    refine ⟨53890301948878632516108065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35926867965919088344072043 53890301948878632516108065)
    ·
      refine ⟨40417726461658974387081049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53890301948878632516108065 40417726461658974387081049)
      ·
        refine ⟨30313294846244230790310787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40417726461658974387081049 30313294846244230790310787)
        ·
          refine ⟨45469942269366346185466181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30313294846244230790310787 45469942269366346185466181)
          ·
            refine ⟨8525614175506189909774909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45469942269366346185466181 8525614175506189909774909)
            ·
              refine ⟨3197105315814821216165591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8525614175506189909774909 3197105315814821216165591)
              ·
                refine ⟨4795657973722231824248387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197105315814821216165591 4795657973722231824248387)
                ·
                  refine ⟨7193486960583347736372581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795657973722231824248387 7193486960583347736372581)
                  ·
                    refine ⟨1348778805109377700569859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7193486960583347736372581 1348778805109377700569859)
                    ·
                      rfl

theorem cell22_3940106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_3940106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940106 prefixEnd_3940106 := by exact prefixLift 3940106
  have htrace : WordTrace (prefixWord ++ tailWord_3940106) baseStart_3940106 baseEnd_3940106 := by
    simpa [prefixWord, tailWord_3940106, baseEnd_3940106] using wordTrace_append hprefix tailTrace_3940106
  have hstable : (prefixWord ++ tailWord_3940106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940106).length < 2 ^ (prefixWord ++ tailWord_3940106).sum := by decide
  have hdescent : baseEnd_3940106 < baseStart_3940106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940136 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3940136 : Nat := 118140960795 + 3940136 * 2 ^ 59
def prefixEnd_3940136 : Nat := 4983230072969 + 3 ^ 40 * 3940136 * 2
def baseEnd_3940136 : Nat := 1348789074722467622319767

theorem tailTrace_3940136 : CollatzResearch.WordTrace tailWord_3940136 prefixEnd_3940136 1348789074722467622319767 := by
  unfold tailWord_3940136
  simp only [CollatzResearch.WordTrace]
  refine ⟨71854283026783834249940131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95805710702378445666586841 71854283026783834249940131)
  ·
    refine ⟨107781424540175751374910197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71854283026783834249940131 107781424540175751374910197)
    ·
      refine ⟨10104508550641476691397831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107781424540175751374910197 10104508550641476691397831)
      ·
        refine ⟨15156762825962215037096747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104508550641476691397831 15156762825962215037096747)
        ·
          refine ⟨22735144238943322555645121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15156762825962215037096747 22735144238943322555645121)
          ·
            refine ⟨17051358179207491916733841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22735144238943322555645121 17051358179207491916733841)
            ·
              refine ⟨12788518634405618937550381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17051358179207491916733841 12788518634405618937550381)
              ·
                refine ⟨4795694487902107101581393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12788518634405618937550381 4795694487902107101581393)
                ·
                  refine ⟨3596770865926580326186045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4795694487902107101581393 3596770865926580326186045)
                  ·
                    refine ⟨1348789074722467622319767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3596770865926580326186045 1348789074722467622319767)
                    ·
                      rfl

theorem cell22_3940136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3940136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940136 prefixEnd_3940136 := by exact prefixLift 3940136
  have htrace : WordTrace (prefixWord ++ tailWord_3940136) baseStart_3940136 baseEnd_3940136 := by
    simpa [prefixWord, tailWord_3940136, baseEnd_3940136] using wordTrace_append hprefix tailTrace_3940136
  have hstable : (prefixWord ++ tailWord_3940136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940136).length < 2 ^ (prefixWord ++ tailWord_3940136).sum := by decide
  have hdescent : baseEnd_3940136 < baseStart_3940136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940166 : List Nat := [6, 1, 1, 2, 1, 2, 9]
def baseStart_3940166 : Nat := 118140960795 + 3940166 * 2 ^ 59
def prefixEnd_3940166 : Nat := 4983230072969 + 3 ^ 40 * 3940166 * 2
def baseEnd_3940166 : Nat := 49955531271687316447025

theorem tailTrace_3940166 : CollatzResearch.WordTrace tailWord_3940166 prefixEnd_3940166 49955531271687316447025 := by
  unfold tailWord_3940166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490926882608093238233511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95806440162305989082314901 4490926882608093238233511)
  ·
    refine ⟨6736390323912139857350267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4490926882608093238233511 6736390323912139857350267)
    ·
      refine ⟨10104585485868209786025401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6736390323912139857350267 10104585485868209786025401)
      ·
        refine ⟨7578439114401157339519051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10104585485868209786025401 7578439114401157339519051)
        ·
          refine ⟨11367658671601736009278577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7578439114401157339519051 11367658671601736009278577)
          ·
            refine ⟨8525744003701302006958933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11367658671601736009278577 8525744003701302006958933)
            ·
              refine ⟨49955531271687316447025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8525744003701302006958933 49955531271687316447025)
              ·
                rfl

theorem cell22_3940166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 9].length) (baseStart_3940166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940166 prefixEnd_3940166 := by exact prefixLift 3940166
  have htrace : WordTrace (prefixWord ++ tailWord_3940166) baseStart_3940166 baseEnd_3940166 := by
    simpa [prefixWord, tailWord_3940166, baseEnd_3940166] using wordTrace_append hprefix tailTrace_3940166
  have hstable : (prefixWord ++ tailWord_3940166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940166).length < 2 ^ (prefixWord ++ tailWord_3940166).sum := by decide
  have hdescent : baseEnd_3940166 < baseStart_3940166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940181 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 3, 3]
def baseStart_3940181 : Nat := 118140960795 + 3940181 * 2 ^ 59
def prefixEnd_3940181 : Nat := 4983230072969 + 3 ^ 40 * 3940181 * 2
def baseEnd_3940181 : Nat := 1348804479142102504944629

theorem tailTrace_3940181 : CollatzResearch.WordTrace tailWord_3940181 prefixEnd_3940181 1348804479142102504944629 := by
  unfold tailWord_3940181
  simp only [CollatzResearch.WordTrace]
  refine ⟨143710207338404641185268397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95806804892269760790178931 143710207338404641185268397)
  ·
    refine ⟨53891327751901740444475649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143710207338404641185268397 53891327751901740444475649)
    ·
      refine ⟨40418495813926305333356737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53891327751901740444475649 40418495813926305333356737)
      ·
        refine ⟨30313871860444729000017553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40418495813926305333356737 30313871860444729000017553)
        ·
          refine ⟨22735403895333546750013165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30313871860444729000017553 22735403895333546750013165)
          ·
            refine ⟨8525776460750080031254937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22735403895333546750013165 8525776460750080031254937)
            ·
              refine ⟨6394332345562560023441203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8525776460750080031254937 6394332345562560023441203)
              ·
                refine ⟨9591498518343840035161805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394332345562560023441203 9591498518343840035161805)
                ·
                  refine ⟨3596811944378940013185677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9591498518343840035161805 3596811944378940013185677)
                  ·
                    refine ⟨1348804479142102504944629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3596811944378940013185677 1348804479142102504944629)
                    ·
                      rfl

theorem cell22_3940181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_3940181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940181 prefixEnd_3940181 := by exact prefixLift 3940181
  have htrace : WordTrace (prefixWord ++ tailWord_3940181) baseStart_3940181 baseEnd_3940181 := by
    simpa [prefixWord, tailWord_3940181, baseEnd_3940181] using wordTrace_append hprefix tailTrace_3940181
  have hstable : (prefixWord ++ tailWord_3940181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940181).length < 2 ^ (prefixWord ++ tailWord_3940181).sum := by decide
  have hdescent : baseEnd_3940181 < baseStart_3940181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940224 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 1, 4]
def baseStart_3940224 : Nat := 118140960795 + 3940224 * 2 ^ 59
def prefixEnd_3940224 : Nat := 4983230072969 + 3 ^ 40 * 3940224 * 2
def baseEnd_3940224 : Nat := 1348819198920864726119497

theorem tailTrace_3940224 : CollatzResearch.WordTrace tailWord_3940224 prefixEnd_3940224 1348819198920864726119497 := by
  unfold tailWord_3940224
  simp only [CollatzResearch.WordTrace]
  refine ⟨71855887838624429764541863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95807850451499239686055817 71855887838624429764541863)
  ·
    refine ⟨107783831757936644646812795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71855887838624429764541863 107783831757936644646812795)
    ·
      refine ⟨161675747636904966970219193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107783831757936644646812795 161675747636904966970219193)
      ·
        refine ⟨121256810727678725227664395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161675747636904966970219193 121256810727678725227664395)
        ·
          refine ⟨181885216091518087841496593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121256810727678725227664395 181885216091518087841496593)
          ·
            refine ⟨136413912068638565881122445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181885216091518087841496593 136413912068638565881122445)
            ·
              refine ⟨51155217025739462205420917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136413912068638565881122445 51155217025739462205420917)
              ·
                refine ⟨4795801596163074581758211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51155217025739462205420917 4795801596163074581758211)
                ·
                  refine ⟨7193702394244611872637317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795801596163074581758211 7193702394244611872637317)
                  ·
                    refine ⟨1348819198920864726119497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7193702394244611872637317 1348819198920864726119497)
                    ·
                      rfl

theorem cell22_3940224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_3940224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940224 prefixEnd_3940224 := by exact prefixLift 3940224
  have htrace : WordTrace (prefixWord ++ tailWord_3940224) baseStart_3940224 baseEnd_3940224 := by
    simpa [prefixWord, tailWord_3940224, baseEnd_3940224] using wordTrace_append hprefix tailTrace_3940224
  have hstable : (prefixWord ++ tailWord_3940224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940224).length < 2 ^ (prefixWord ++ tailWord_3940224).sum := by decide
  have hdescent : baseEnd_3940224 < baseStart_3940224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940284 : List Nat := [2, 2, 2, 5, 11]
def baseStart_3940284 : Nat := 118140960795 + 3940284 * 2 ^ 59
def prefixEnd_3940284 : Nat := 4983230072969 + 3 ^ 40 * 3940284 * 2
def baseEnd_3940284 : Nat := 5550780815419936500491

theorem tailTrace_3940284 : CollatzResearch.WordTrace tailWord_3940284 prefixEnd_3940284 5550780815419936500491 := by
  unfold tailWord_3940284
  simp only [CollatzResearch.WordTrace]
  refine ⟨71856982028515744888133953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95809309371354326517511937 71856982028515744888133953)
  ·
    refine ⟨53892736521386808666100465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71856982028515744888133953 53892736521386808666100465)
    ·
      refine ⟨40419552391040106499575349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53892736521386808666100465 40419552391040106499575349)
      ·
        refine ⟨3789333036660009984335189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40419552391040106499575349 3789333036660009984335189)
        ·
          refine ⟨5550780815419936500491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3789333036660009984335189 5550780815419936500491)
          ·
            rfl

theorem cell22_3940284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 11].length) (baseStart_3940284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940284 prefixEnd_3940284 := by exact prefixLift 3940284
  have htrace : WordTrace (prefixWord ++ tailWord_3940284) baseStart_3940284 baseEnd_3940284 := by
    simpa [prefixWord, tailWord_3940284, baseEnd_3940284] using wordTrace_append hprefix tailTrace_3940284
  have hstable : (prefixWord ++ tailWord_3940284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940284).length < 2 ^ (prefixWord ++ tailWord_3940284).sum := by decide
  have hdescent : baseEnd_3940284 < baseStart_3940284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940286 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3940286 : Nat := 118140960795 + 3940286 * 2 ^ 59
def prefixEnd_3940286 : Nat := 4983230072969 + 3 ^ 40 * 3940286 * 2
def baseEnd_3940286 : Nat := 1348840422787917231069307

theorem tailTrace_3940286 : CollatzResearch.WordTrace tailWord_3940286 prefixEnd_3940286 1348840422787917231069307 := by
  unfold tailWord_3940286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17964254625378030514730089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95809358002016162745227141 17964254625378030514730089)
  ·
    refine ⟨13473190969033522886047567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17964254625378030514730089 13473190969033522886047567)
    ·
      refine ⟨20209786453550284329071351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13473190969033522886047567 20209786453550284329071351)
      ·
        refine ⟨30314679680325426493607027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20209786453550284329071351 30314679680325426493607027)
        ·
          refine ⟨45472019520488139740410541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30314679680325426493607027 45472019520488139740410541)
          ·
            refine ⟨17052007320183052402653953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45472019520488139740410541 17052007320183052402653953)
            ·
              refine ⟨12789005490137289301990465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17052007320183052402653953 12789005490137289301990465)
              ·
                refine ⟨9591754117602966976492849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12789005490137289301990465 9591754117602966976492849)
                ·
                  refine ⟨7193815588202225232369637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9591754117602966976492849 7193815588202225232369637)
                  ·
                    refine ⟨1348840422787917231069307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7193815588202225232369637 1348840422787917231069307)
                    ·
                      rfl

theorem cell22_3940286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3940286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940286 prefixEnd_3940286 := by exact prefixLift 3940286
  have htrace : WordTrace (prefixWord ++ tailWord_3940286) baseStart_3940286 baseEnd_3940286 := by
    simpa [prefixWord, tailWord_3940286, baseEnd_3940286] using wordTrace_append hprefix tailTrace_3940286
  have hstable : (prefixWord ++ tailWord_3940286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940286).length < 2 ^ (prefixWord ++ tailWord_3940286).sum := by decide
  have hdescent : baseEnd_3940286 < baseStart_3940286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940344 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_3940344 : Nat := 118140960795 + 3940344 * 2 ^ 59
def prefixEnd_3940344 : Nat := 4983230072969 + 3 ^ 40 * 3940344 * 2
def baseEnd_3940344 : Nat := 1348860277373224413119129

theorem tailTrace_3940344 : CollatzResearch.WordTrace tailWord_3940344 prefixEnd_3940344 1348860277373224413119129 := by
  unfold tailWord_3940344
  simp only [CollatzResearch.WordTrace]
  refine ⟨71858076218407060011726043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95810768291209413348968057 71858076218407060011726043)
  ·
    refine ⟨107787114327610590017589065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71858076218407060011726043 107787114327610590017589065)
    ·
      refine ⟨80840335745707942513191799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107787114327610590017589065 80840335745707942513191799)
      ·
        refine ⟨121260503618561913769787699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80840335745707942513191799 121260503618561913769787699)
        ·
          refine ⟨181890755427842870654681549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121260503618561913769787699 181890755427842870654681549)
          ·
            refine ⟨68209033285441076495505581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181890755427842870654681549 68209033285441076495505581)
            ·
              refine ⟨25578387482040403685814593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68209033285441076495505581 25578387482040403685814593)
              ·
                refine ⟨19183790611530302764360945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25578387482040403685814593 19183790611530302764360945)
                ·
                  refine ⟨14387842958647727073270709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19183790611530302764360945 14387842958647727073270709)
                  ·
                    refine ⟨1348860277373224413119129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14387842958647727073270709 1348860277373224413119129)
                    ·
                      rfl

theorem cell22_3940344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_3940344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940344 prefixEnd_3940344 := by exact prefixLift 3940344
  have htrace : WordTrace (prefixWord ++ tailWord_3940344) baseStart_3940344 baseEnd_3940344 := by
    simpa [prefixWord, tailWord_3940344, baseEnd_3940344] using wordTrace_append hprefix tailTrace_3940344
  have hstable : (prefixWord ++ tailWord_3940344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940344).length < 2 ^ (prefixWord ++ tailWord_3940344).sum := by decide
  have hdescent : baseEnd_3940344 < baseStart_3940344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940350 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_3940350 : Nat := 118140960795 + 3940350 * 2 ^ 59
def prefixEnd_3940350 : Nat := 4983230072969 + 3 ^ 40 * 3940350 * 2
def baseEnd_3940350 : Nat := 1348862331295842397469111

theorem tailTrace_3940350 : CollatzResearch.WordTrace tailWord_3940350 prefixEnd_3940350 1348862331295842397469111 := by
  unfold tailWord_3940350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17964546409349047881021313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95810914183194922032113669 17964546409349047881021313)
  ·
    refine ⟨13473409807011785910765985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17964546409349047881021313 13473409807011785910765985)
    ·
      refine ⟨10105057355258839433074489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13473409807011785910765985 10105057355258839433074489)
      ·
        refine ⟨7578793016444129574805867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10105057355258839433074489 7578793016444129574805867)
        ·
          refine ⟨11368189524666194362208801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7578793016444129574805867 11368189524666194362208801)
          ·
            refine ⟨8526142143499645771656601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11368189524666194362208801 8526142143499645771656601)
            ·
              refine ⟨6394606607624734328742451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8526142143499645771656601 6394606607624734328742451)
              ·
                refine ⟨9591909911437101493113677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394606607624734328742451 9591909911437101493113677)
                ·
                  refine ⟨3596966216788913059917629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9591909911437101493113677 3596966216788913059917629)
                  ·
                    refine ⟨1348862331295842397469111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3596966216788913059917629 1348862331295842397469111)
                    ·
                      rfl

theorem cell22_3940350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_3940350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940350 prefixEnd_3940350 := by exact prefixLift 3940350
  have htrace : WordTrace (prefixWord ++ tailWord_3940350) baseStart_3940350 baseEnd_3940350 := by
    simpa [prefixWord, tailWord_3940350, baseEnd_3940350] using wordTrace_append hprefix tailTrace_3940350
  have hstable : (prefixWord ++ tailWord_3940350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940350).length < 2 ^ (prefixWord ++ tailWord_3940350).sum := by decide
  have hdescent : baseEnd_3940350 < baseStart_3940350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3940408 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 6]
def baseStart_3940408 : Nat := 118140960795 + 3940408 * 2 ^ 59
def prefixEnd_3940408 : Nat := 4983230072969 + 3 ^ 40 * 3940408 * 2
def baseEnd_3940408 : Nat := 449627395293716526506311

theorem tailTrace_3940408 : CollatzResearch.WordTrace tailWord_3940408 prefixEnd_3940408 449627395293716526506311 := by
  unfold tailWord_3940408
  simp only [CollatzResearch.WordTrace]
  refine ⟨71859243354291129476890939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95812324472388172635854585 71859243354291129476890939)
  ·
    refine ⟨107788865031436694215336409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71859243354291129476890939 107788865031436694215336409)
    ·
      refine ⟨80841648773577520661502307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107788865031436694215336409 80841648773577520661502307)
      ·
        refine ⟨121262473160366280992253461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80841648773577520661502307 121262473160366280992253461)
        ·
          refine ⟨5684178429392169421511881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121262473160366280992253461 5684178429392169421511881)
          ·
            refine ⟨4263133822044127066133911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5684178429392169421511881 4263133822044127066133911)
            ·
              refine ⟨6394700733066190599200867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4263133822044127066133911 6394700733066190599200867)
              ·
                refine ⟨9592051099599285898801301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394700733066190599200867 9592051099599285898801301)
                ·
                  refine ⟨449627395293716526506311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9592051099599285898801301 449627395293716526506311)
                  ·
                    rfl

theorem cell22_3940408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 6].length) (baseStart_3940408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3940408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3940408 prefixEnd_3940408 := by exact prefixLift 3940408
  have htrace : WordTrace (prefixWord ++ tailWord_3940408) baseStart_3940408 baseEnd_3940408 := by
    simpa [prefixWord, tailWord_3940408, baseEnd_3940408] using wordTrace_append hprefix tailTrace_3940408
  have hstable : (prefixWord ++ tailWord_3940408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3940408).length < 2 ^ (prefixWord ++ tailWord_3940408).sum := by decide
  have hdescent : baseEnd_3940408 < baseStart_3940408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3940408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
