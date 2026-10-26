import V185TrunkScan23Chunk1317

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7806248 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_7806248 : Nat := 118140960795 + 7806248 * 2 ^ 59
def prefixEnd_7806248 : Nat := 4983230072969 + 3 ^ 40 * 7806248 * 2
def baseEnd_7806248 : Nat := 4008357332198879252499725

theorem tailTrace_7806248 : CollatzResearch.WordTrace tailWord_7806248 prefixEnd_7806248 4008357332198879252499725 := by
  unfold tailWord_7806248
  simp only [CollatzResearch.WordTrace]
  refine ⟨142358627511652085930977699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189811503348869447907970265 142358627511652085930977699)
  ·
    refine ⟨213537941267478128896466549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142358627511652085930977699 213537941267478128896466549)
    ·
      refine ⟨20019181993826074584043739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213537941267478128896466549 20019181993826074584043739)
      ·
        refine ⟨30028772990739111876065609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20019181993826074584043739 30028772990739111876065609)
        ·
          refine ⟨22521579743054333907049207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30028772990739111876065609 22521579743054333907049207)
          ·
            refine ⟨33782369614581500860573811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22521579743054333907049207 33782369614581500860573811)
            ·
              refine ⟨50673554421872251290860717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33782369614581500860573811 50673554421872251290860717)
              ·
                refine ⟨19002582908202094234072769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50673554421872251290860717 19002582908202094234072769)
                ·
                  refine ⟨14251937181151570675554577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19002582908202094234072769 14251937181151570675554577)
                  ·
                    refine ⟨10688952885863678006665933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14251937181151570675554577 10688952885863678006665933)
                    ·
                      refine ⟨4008357332198879252499725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10688952885863678006665933 4008357332198879252499725)
                      ·
                        rfl

theorem cell23_7806248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_7806248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806248 prefixEnd_7806248 := by exact prefixLift 7806248
  have htrace : WordTrace (prefixWord ++ tailWord_7806248) baseStart_7806248 baseEnd_7806248 := by
    simpa [prefixWord, tailWord_7806248, baseEnd_7806248] using wordTrace_append hprefix tailTrace_7806248
  have hstable : (prefixWord ++ tailWord_7806248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806248).length < 2 ^ (prefixWord ++ tailWord_7806248).sum := by decide
  have hdescent : baseEnd_7806248 < baseStart_7806248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806345 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 1, 6]
def baseStart_7806345 : Nat := 118140960795 + 7806345 * 2 ^ 59
def prefixEnd_7806345 : Nat := 4983230072969 + 3 ^ 40 * 7806345 * 2
def baseEnd_7806345 : Nat := 1336135713274121790995593

theorem tailTrace_7806345 : CollatzResearch.WordTrace tailWord_7806345 prefixEnd_7806345 1336135713274121790995593 := by
  unfold tailWord_7806345
  simp only [CollatzResearch.WordTrace]
  refine ⟨284720792903952757428236489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189813861935968504952157659 284720792903952757428236489)
  ·
    refine ⟨213540594677964568071177367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284720792903952757428236489 213540594677964568071177367)
    ·
      refine ⟨320310892016946852106766051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213540594677964568071177367 320310892016946852106766051)
      ·
        refine ⟨480466338025420278160149077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320310892016946852106766051 480466338025420278160149077)
        ·
          refine ⟨5630464898735393884689247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 480466338025420278160149077 5630464898735393884689247)
          ·
            refine ⟨8445697348103090827033871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5630464898735393884689247 8445697348103090827033871)
            ·
              refine ⟨12668546022154636240550807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8445697348103090827033871 12668546022154636240550807)
              ·
                refine ⟨19002819033231954360826211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12668546022154636240550807 19002819033231954360826211)
                ·
                  refine ⟨28504228549847931541239317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19002819033231954360826211 28504228549847931541239317)
                  ·
                    refine ⟨1336135713274121790995593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28504228549847931541239317 1336135713274121790995593)
                    ·
                      rfl

theorem cell23_7806345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 6].length) (baseStart_7806345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806345 prefixEnd_7806345 := by exact prefixLift 7806345
  have htrace : WordTrace (prefixWord ++ tailWord_7806345) baseStart_7806345 baseEnd_7806345 := by
    simpa [prefixWord, tailWord_7806345, baseEnd_7806345] using wordTrace_append hprefix tailTrace_7806345
  have hstable : (prefixWord ++ tailWord_7806345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806345).length < 2 ^ (prefixWord ++ tailWord_7806345).sum := by decide
  have hdescent : baseEnd_7806345 < baseStart_7806345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806368 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 6, 1, 3]
def baseStart_7806368 : Nat := 118140960795 + 7806368 * 2 ^ 59
def prefixEnd_7806368 : Nat := 4983230072969 + 3 ^ 40 * 7806368 * 2
def baseEnd_7806368 : Nat := 4008418949877418782999173

theorem tailTrace_7806368 : CollatzResearch.WordTrace tailWord_7806368 prefixEnd_7806368 4008418949877418782999173 := by
  unfold tailWord_7806368
  simp only [CollatzResearch.WordTrace]
  refine ⟨142360815891434716178161879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189814421188579621570882505 142360815891434716178161879)
  ·
    refine ⟨213541223837152074267242819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142360815891434716178161879 213541223837152074267242819)
    ·
      refine ⟨320311835755728111400864229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213541223837152074267242819 320311835755728111400864229)
      ·
        refine ⟨60058469204199020887662043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320311835755728111400864229 60058469204199020887662043)
        ·
          refine ⟨90087703806298531331493065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60058469204199020887662043 90087703806298531331493065)
          ·
            refine ⟨67565777854723898498619799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90087703806298531331493065 67565777854723898498619799)
            ·
              refine ⟨101348666782085847747929699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67565777854723898498619799 101348666782085847747929699)
              ·
                refine ⟨152023000173128771621894549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101348666782085847747929699 152023000173128771621894549)
                ·
                  refine ⟨7126078133115411169776307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152023000173128771621894549 7126078133115411169776307)
                  ·
                    refine ⟨10689117199673116754664461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7126078133115411169776307 10689117199673116754664461)
                    ·
                      refine ⟨4008418949877418782999173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10689117199673116754664461 4008418949877418782999173)
                      ·
                        rfl

theorem cell23_7806368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_7806368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806368 prefixEnd_7806368 := by exact prefixLift 7806368
  have htrace : WordTrace (prefixWord ++ tailWord_7806368) baseStart_7806368 baseEnd_7806368 := by
    simpa [prefixWord, tailWord_7806368, baseEnd_7806368] using wordTrace_append hprefix tailTrace_7806368
  have hstable : (prefixWord ++ tailWord_7806368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806368).length < 2 ^ (prefixWord ++ tailWord_7806368).sum := by decide
  have hdescent : baseEnd_7806368 < baseStart_7806368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806385 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 2, 1, 3]
def baseStart_7806385 : Nat := 118140960795 + 7806385 * 2 ^ 59
def prefixEnd_7806385 : Nat := 4983230072969 + 3 ^ 40 * 7806385 * 2
def baseEnd_7806385 : Nat := 4008427679048545216486595

theorem tailTrace_7806385 : CollatzResearch.WordTrace tailWord_7806385 prefixEnd_7806385 4008427679048545216486595 := by
  unfold tailWord_7806385
  simp only [CollatzResearch.WordTrace]
  refine ⟨284722251823807844259692609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189814834549205229506461739 284722251823807844259692609)
  ·
    refine ⟨213541688867855883194769457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284722251823807844259692609 213541688867855883194769457)
    ·
      refine ⟨160156266650891912396077093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213541688867855883194769457 160156266650891912396077093)
      ·
        refine ⟨30029299997042233574264455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160156266650891912396077093 30029299997042233574264455)
        ·
          refine ⟨45043949995563350361396683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30029299997042233574264455 45043949995563350361396683)
          ·
            refine ⟨67565924993345025542095025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45043949995563350361396683 67565924993345025542095025)
            ·
              refine ⟨50674443745008769156571269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67565924993345025542095025 50674443745008769156571269)
              ·
                refine ⟨9501458202189144216857113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50674443745008769156571269 9501458202189144216857113)
                ·
                  refine ⟨7126093651641858162642835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9501458202189144216857113 7126093651641858162642835)
                  ·
                    refine ⟨10689140477462787243964253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7126093651641858162642835 10689140477462787243964253)
                    ·
                      refine ⟨4008427679048545216486595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10689140477462787243964253 4008427679048545216486595)
                      ·
                        rfl

theorem cell23_7806385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_7806385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806385 prefixEnd_7806385 := by exact prefixLift 7806385
  have htrace : WordTrace (prefixWord ++ tailWord_7806385) baseStart_7806385 baseEnd_7806385 := by
    simpa [prefixWord, tailWord_7806385, baseEnd_7806385] using wordTrace_append hprefix tailTrace_7806385
  have hstable : (prefixWord ++ tailWord_7806385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806385).length < 2 ^ (prefixWord ++ tailWord_7806385).sum := by decide
  have hdescent : baseEnd_7806385 < baseStart_7806385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806391 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_7806391 : Nat := 118140960795 + 7806391 * 2 ^ 59
def prefixEnd_7806391 : Nat := 4983230072969 + 3 ^ 40 * 7806391 * 2
def baseEnd_7806391 : Nat := 4008430759932472193011567

theorem tailTrace_7806391 : CollatzResearch.WordTrace tailWord_7806391 prefixEnd_7806391 4008430759932472193011567 := by
  unfold tailWord_7806391
  simp only [CollatzResearch.WordTrace]
  refine ⟨284722470661786107284411027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189814980441190738189607351 284722470661786107284411027)
  ·
    refine ⟨427083705992679160926616541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284722470661786107284411027 427083705992679160926616541)
    ·
      refine ⟨160156389747254685347481203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427083705992679160926616541 160156389747254685347481203)
      ·
        refine ⟨240234584620882028021221805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160156389747254685347481203 240234584620882028021221805)
        ·
          refine ⟨90087969232830760507958177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240234584620882028021221805 90087969232830760507958177)
          ·
            refine ⟨67565976924623070380968633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90087969232830760507958177 67565976924623070380968633)
            ·
              refine ⟨50674482693467302785726475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67565976924623070380968633 50674482693467302785726475)
              ·
                refine ⟨76011724040200954178589713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50674482693467302785726475 76011724040200954178589713)
                ·
                  refine ⟨57008793030150715633942285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76011724040200954178589713 57008793030150715633942285)
                  ·
                    refine ⟨21378297386306518362728357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57008793030150715633942285 21378297386306518362728357)
                    ·
                      refine ⟨4008430759932472193011567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21378297386306518362728357 4008430759932472193011567)
                      ·
                        rfl

theorem cell23_7806391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_7806391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806391 prefixEnd_7806391 := by exact prefixLift 7806391
  have htrace : WordTrace (prefixWord ++ tailWord_7806391) baseStart_7806391 baseEnd_7806391 := by
    simpa [prefixWord, tailWord_7806391, baseEnd_7806391] using wordTrace_append hprefix tailTrace_7806391
  have hstable : (prefixWord ++ tailWord_7806391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806391).length < 2 ^ (prefixWord ++ tailWord_7806391).sum := by decide
  have hdescent : baseEnd_7806391 < baseStart_7806391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806411 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 5]
def baseStart_7806411 : Nat := 118140960795 + 7806411 * 2 ^ 59
def prefixEnd_7806411 : Nat := 4983230072969 + 3 ^ 40 * 7806411 * 2
def baseEnd_7806411 : Nat := 4008441029545562114761475

theorem tailTrace_7806411 : CollatzResearch.WordTrace tailWord_7806411 prefixEnd_7806411 4008441029545562114761475 := by
  unfold tailWord_7806411
  simp only [CollatzResearch.WordTrace]
  refine ⟨284723200121713650700139087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189815466747809100466759391 284723200121713650700139087)
  ·
    refine ⟨427084800182570476050208631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284723200121713650700139087 427084800182570476050208631)
    ·
      refine ⟨640627200273855714075312947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427084800182570476050208631 640627200273855714075312947)
      ·
        refine ⟨960940800410783571112969421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640627200273855714075312947 960940800410783571112969421)
        ·
          refine ⟨360352800154043839167363533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 960940800410783571112969421 360352800154043839167363533)
          ·
            refine ⟨135132300057766439687761325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360352800154043839167363533 135132300057766439687761325)
            ·
              refine ⟨50674612521662414882910497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135132300057766439687761325 50674612521662414882910497)
              ·
                refine ⟨38005959391246811162182873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50674612521662414882910497 38005959391246811162182873)
                ·
                  refine ⟨28504469543435108371637155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38005959391246811162182873 28504469543435108371637155)
                  ·
                    refine ⟨42756704315152662557455733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28504469543435108371637155 42756704315152662557455733)
                    ·
                      refine ⟨4008441029545562114761475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42756704315152662557455733 4008441029545562114761475)
                      ·
                        rfl

theorem cell23_7806411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 5].length) (baseStart_7806411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806411 prefixEnd_7806411 := by exact prefixLift 7806411
  have htrace : WordTrace (prefixWord ++ tailWord_7806411) baseStart_7806411 baseEnd_7806411 := by
    simpa [prefixWord, tailWord_7806411, baseEnd_7806411] using wordTrace_append hprefix tailTrace_7806411
  have hstable : (prefixWord ++ tailWord_7806411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806411).length < 2 ^ (prefixWord ++ tailWord_7806411).sum := by decide
  have hdescent : baseEnd_7806411 < baseStart_7806411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806412 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 1, 3, 2]
def baseStart_7806412 : Nat := 118140960795 + 7806412 * 2 ^ 59
def prefixEnd_7806412 : Nat := 4983230072969 + 3 ^ 40 * 7806412 * 2
def baseEnd_7806412 : Nat := 4008441543026216610848971

theorem tailTrace_7806412 : CollatzResearch.WordTrace tailWord_7806412 prefixEnd_7806412 4008441543026216610848971 := by
  unfold tailWord_7806412
  simp only [CollatzResearch.WordTrace]
  refine ⟨142361618297355013935462745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189815491063140018580616993 142361618297355013935462745)
  ·
    refine ⟨106771213723016260451597059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142361618297355013935462745 106771213723016260451597059)
    ·
      refine ⟨160156820584524390677395589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106771213723016260451597059 160156820584524390677395589)
      ·
        refine ⟨30029403859598323252011673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160156820584524390677395589 30029403859598323252011673)
        ·
          refine ⟨22522052894698742439008755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30029403859598323252011673 22522052894698742439008755)
          ·
            refine ⟨33783079342048113658513133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22522052894698742439008755 33783079342048113658513133)
            ·
              refine ⟨12668654753268042621942425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33783079342048113658513133 12668654753268042621942425)
              ·
                refine ⟨9501491064951031966456819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12668654753268042621942425 9501491064951031966456819)
                ·
                  refine ⟨14252236597426547949685229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9501491064951031966456819 14252236597426547949685229)
                  ·
                    refine ⟨5344588724034955481131961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14252236597426547949685229 5344588724034955481131961)
                    ·
                      refine ⟨4008441543026216610848971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344588724034955481131961 4008441543026216610848971)
                      ·
                        rfl

theorem cell23_7806412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_7806412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806412 prefixEnd_7806412 := by exact prefixLift 7806412
  have htrace : WordTrace (prefixWord ++ tailWord_7806412) baseStart_7806412 baseEnd_7806412 := by
    simpa [prefixWord, tailWord_7806412, baseEnd_7806412] using wordTrace_append hprefix tailTrace_7806412
  have hstable : (prefixWord ++ tailWord_7806412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806412).length < 2 ^ (prefixWord ++ tailWord_7806412).sum := by decide
  have hdescent : baseEnd_7806412 < baseStart_7806412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806425 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 1, 4, 2]
def baseStart_7806425 : Nat := 118140960795 + 7806425 * 2 ^ 59
def prefixEnd_7806425 : Nat := 4983230072969 + 3 ^ 40 * 7806425 * 2
def baseEnd_7806425 : Nat := 4008448218274725059986411

theorem tailTrace_7806425 : CollatzResearch.WordTrace tailWord_7806425 prefixEnd_7806425 4008448218274725059986411 := by
  unfold tailWord_7806425
  simp only [CollatzResearch.WordTrace]
  refine ⟨284723710743662931091148729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189815807162441954060765819 284723710743662931091148729)
  ·
    refine ⟨213542783057747198318361547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284723710743662931091148729 213542783057747198318361547)
    ·
      refine ⟨320314174586620797477542321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213542783057747198318361547 320314174586620797477542321)
      ·
        refine ⟨240235630939965598108156741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320314174586620797477542321 240235630939965598108156741)
        ·
          refine ⟨45044180801243549645279389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240235630939965598108156741 45044180801243549645279389)
          ·
            refine ⟨16891567800466331116979771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45044180801243549645279389 16891567800466331116979771)
            ·
              refine ⟨25337351700699496675469657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16891567800466331116979771 25337351700699496675469657)
              ·
                refine ⟨19003013775524622506602243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25337351700699496675469657 19003013775524622506602243)
                ·
                  refine ⟨28504520663286933759903365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19003013775524622506602243 28504520663286933759903365)
                  ·
                    refine ⟨5344597624366300079981881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28504520663286933759903365 5344597624366300079981881)
                    ·
                      refine ⟨4008448218274725059986411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344597624366300079981881 4008448218274725059986411)
                      ·
                        rfl

theorem cell23_7806425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_7806425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806425 prefixEnd_7806425 := by exact prefixLift 7806425
  have htrace : WordTrace (prefixWord ++ tailWord_7806425) baseStart_7806425 baseEnd_7806425 := by
    simpa [prefixWord, tailWord_7806425, baseEnd_7806425] using wordTrace_append hprefix tailTrace_7806425
  have hstable : (prefixWord ++ tailWord_7806425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806425).length < 2 ^ (prefixWord ++ tailWord_7806425).sum := by decide
  have hdescent : baseEnd_7806425 < baseStart_7806425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806429 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_7806429 : Nat := 118140960795 + 7806429 * 2 ^ 59
def prefixEnd_7806429 : Nat := 4983230072969 + 3 ^ 40 * 7806429 * 2
def baseEnd_7806429 : Nat := 4008450272197343044336393

theorem tailTrace_7806429 : CollatzResearch.WordTrace tailWord_7806429 prefixEnd_7806429 4008450272197343044336393 := by
  unfold tailWord_7806429
  simp only [CollatzResearch.WordTrace]
  refine ⟨284723856635648439774294341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189815904423765626516196227 284723856635648439774294341)
  ·
    refine ⟨53385723119184082457680189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284723856635648439774294341 53385723119184082457680189)
    ·
      refine ⟨20019646169694030921630071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53385723119184082457680189 20019646169694030921630071)
      ·
        refine ⟨30029469254541046382445107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20019646169694030921630071 30029469254541046382445107)
        ·
          refine ⟨45044203881811569573667661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30029469254541046382445107 45044203881811569573667661)
          ·
            refine ⟨16891576455679338590125373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45044203881811569573667661 16891576455679338590125373)
            ·
              refine ⟨6334341170879751971297015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16891576455679338590125373 6334341170879751971297015)
              ·
                refine ⟨9501511756319627956945523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6334341170879751971297015 9501511756319627956945523)
                ·
                  refine ⟨14252267634479441935418285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9501511756319627956945523 14252267634479441935418285)
                  ·
                    refine ⟨5344600362929790725781857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14252267634479441935418285 5344600362929790725781857)
                    ·
                      refine ⟨4008450272197343044336393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344600362929790725781857 4008450272197343044336393)
                      ·
                        rfl

theorem cell23_7806429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_7806429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806429 prefixEnd_7806429 := by exact prefixLift 7806429
  have htrace : WordTrace (prefixWord ++ tailWord_7806429) baseStart_7806429 baseEnd_7806429 := by
    simpa [prefixWord, tailWord_7806429, baseEnd_7806429] using wordTrace_append hprefix tailTrace_7806429
  have hstable : (prefixWord ++ tailWord_7806429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806429).length < 2 ^ (prefixWord ++ tailWord_7806429).sum := by decide
  have hdescent : baseEnd_7806429 < baseStart_7806429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806458 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3]
def baseStart_7806458 : Nat := 118140960795 + 7806458 * 2 ^ 59
def prefixEnd_7806458 : Nat := 4983230072969 + 3 ^ 40 * 7806458 * 2
def baseEnd_7806458 : Nat := 4008465163136323430873759

theorem tailTrace_7806458 : CollatzResearch.WordTrace tailWord_7806458 prefixEnd_7806458 4008465163136323430873759 := by
  unfold tailWord_7806458
  simp only [CollatzResearch.WordTrace]
  refine ⟨71181228588135844431775007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189816609568362251818066685 71181228588135844431775007)
  ·
    refine ⟨106771842882203766647662511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71181228588135844431775007 106771842882203766647662511)
    ·
      refine ⟨160157764323305649971493767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106771842882203766647662511 160157764323305649971493767)
      ·
        refine ⟨240236646484958474957240651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160157764323305649971493767 240236646484958474957240651)
        ·
          refine ⟨360354969727437712435860977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240236646484958474957240651 360354969727437712435860977)
          ·
            refine ⟨270266227295578284326895733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360354969727437712435860977 270266227295578284326895733)
            ·
              refine ⟨25337458808960464155646475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270266227295578284326895733 25337458808960464155646475)
              ·
                refine ⟨38006188213440696233469713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25337458808960464155646475 38006188213440696233469713)
                ·
                  refine ⟨28504641160080522175102285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38006188213440696233469713 28504641160080522175102285)
                  ·
                    refine ⟨10689240435030195815663357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28504641160080522175102285 10689240435030195815663357)
                    ·
                      refine ⟨4008465163136323430873759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10689240435030195815663357 4008465163136323430873759)
                      ·
                        rfl

theorem cell23_7806458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_7806458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806458 prefixEnd_7806458 := by exact prefixLift 7806458
  have htrace : WordTrace (prefixWord ++ tailWord_7806458) baseStart_7806458 baseEnd_7806458 := by
    simpa [prefixWord, tailWord_7806458, baseEnd_7806458] using wordTrace_append hprefix tailTrace_7806458
  have hstable : (prefixWord ++ tailWord_7806458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806458).length < 2 ^ (prefixWord ++ tailWord_7806458).sum := by decide
  have hdescent : baseEnd_7806458 < baseStart_7806458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806515 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 2, 4, 2]
def baseStart_7806515 : Nat := 118140960795 + 7806515 * 2 ^ 59
def prefixEnd_7806515 : Nat := 4983230072969 + 3 ^ 40 * 7806515 * 2
def baseEnd_7806515 : Nat := 4008494431533629707860997

theorem tailTrace_7806515 : CollatzResearch.WordTrace tailWord_7806515 prefixEnd_7806515 4008494431533629707860997 := by
  unfold tailWord_7806515
  simp only [CollatzResearch.WordTrace]
  refine ⟨284726993313336876461924999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189817995542224584307949999 284726993313336876461924999)
  ·
    refine ⟨427090489970005314692887499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284726993313336876461924999 427090489970005314692887499)
    ·
      refine ⟨640635734955007972039331249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427090489970005314692887499 640635734955007972039331249)
      ·
        refine ⟨480476801216255979029498437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640635734955007972039331249 480476801216255979029498437)
        ·
          refine ⟨90089400228047996068030957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 480476801216255979029498437 90089400228047996068030957)
          ·
            refine ⟨33783525085517998525511609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90089400228047996068030957 33783525085517998525511609)
            ·
              refine ⟨25337643814138498894133707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33783525085517998525511609 25337643814138498894133707)
              ·
                refine ⟨38006465721207748341200561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25337643814138498894133707 38006465721207748341200561)
                ·
                  refine ⟨28504849290905811255900421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38006465721207748341200561 28504849290905811255900421)
                  ·
                    refine ⟨5344659242044839610481329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28504849290905811255900421 5344659242044839610481329)
                    ·
                      refine ⟨4008494431533629707860997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344659242044839610481329 4008494431533629707860997)
                      ·
                        rfl

theorem cell23_7806515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 4, 2].length) (baseStart_7806515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806515 prefixEnd_7806515 := by exact prefixLift 7806515
  have htrace : WordTrace (prefixWord ++ tailWord_7806515) baseStart_7806515 baseEnd_7806515 := by
    simpa [prefixWord, tailWord_7806515, baseEnd_7806515] using wordTrace_append hprefix tailTrace_7806515
  have hstable : (prefixWord ++ tailWord_7806515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806515).length < 2 ^ (prefixWord ++ tailWord_7806515).sum := by decide
  have hdescent : baseEnd_7806515 < baseStart_7806515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806531 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 9]
def baseStart_7806531 : Nat := 118140960795 + 7806531 * 2 ^ 59
def prefixEnd_7806531 : Nat := 4983230072969 + 3 ^ 40 * 7806531 * 2
def baseEnd_7806531 : Nat := 4008502647224101645260923

theorem tailTrace_7806531 : CollatzResearch.WordTrace tailWord_7806531 prefixEnd_7806531 4008502647224101645260923 := by
  unfold tailWord_7806531
  simp only [CollatzResearch.WordTrace]
  refine ⟨284727576881278911194507447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189818384587519274129671631 284727576881278911194507447)
  ·
    refine ⟨427091365321918366791761171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284727576881278911194507447 427091365321918366791761171)
    ·
      refine ⟨640637047982877550187641757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427091365321918366791761171 640637047982877550187641757)
      ·
        refine ⟨240238892993579081320365659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640637047982877550187641757 240238892993579081320365659)
        ·
          refine ⟨360358339490368621980548489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240238892993579081320365659 360358339490368621980548489)
          ·
            refine ⟨270268754617776466485411367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360358339490368621980548489 270268754617776466485411367)
            ·
              refine ⟨405403131926664699728117051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270268754617776466485411367 405403131926664699728117051)
              ·
                refine ⟨608104697889997049592175577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405403131926664699728117051 608104697889997049592175577)
                ·
                  refine ⟨456078523417497787194131683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608104697889997049592175577 456078523417497787194131683)
                  ·
                    refine ⟨684117785126246680791197525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 456078523417497787194131683 684117785126246680791197525)
                    ·
                      refine ⟨4008502647224101645260923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 684117785126246680791197525 4008502647224101645260923)
                      ·
                        rfl

theorem cell23_7806531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_7806531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806531 prefixEnd_7806531 := by exact prefixLift 7806531
  have htrace : WordTrace (prefixWord ++ tailWord_7806531) baseStart_7806531 baseEnd_7806531 := by
    simpa [prefixWord, tailWord_7806531, baseEnd_7806531] using wordTrace_append hprefix tailTrace_7806531
  have hstable : (prefixWord ++ tailWord_7806531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806531).length < 2 ^ (prefixWord ++ tailWord_7806531).sum := by decide
  have hdescent : baseEnd_7806531 < baseStart_7806531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806575 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 6, 3, 2]
def baseStart_7806575 : Nat := 118140960795 + 7806575 * 2 ^ 59
def prefixEnd_7806575 : Nat := 4983230072969 + 3 ^ 40 * 7806575 * 2
def baseEnd_7806575 : Nat := 4008525240372899473110721

theorem tailTrace_7806575 : CollatzResearch.WordTrace tailWord_7806575 prefixEnd_7806575 4008525240372899473110721 := by
  unfold tailWord_7806575
  simp only [CollatzResearch.WordTrace]
  refine ⟨284729181693119506709109179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189819454462079671139406119 284729181693119506709109179)
  ·
    refine ⟨427093772539679260063663769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284729181693119506709109179 427093772539679260063663769)
    ·
      refine ⟨320320329404759445047747827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427093772539679260063663769 320320329404759445047747827)
      ·
        refine ⟨480480494107139167571621741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320320329404759445047747827 480480494107139167571621741)
        ·
          refine ⟨180180185290177187839358153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480480494107139167571621741 180180185290177187839358153)
          ·
            refine ⟨135135138967632890879518615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180180185290177187839358153 135135138967632890879518615)
            ·
              refine ⟨202702708451449336319277923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135135138967632890879518615 202702708451449336319277923)
              ·
                refine ⟨304054062677174004478916885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202702708451449336319277923 304054062677174004478916885)
                ·
                  refine ⟨14252534187992531459949229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 304054062677174004478916885 14252534187992531459949229)
                  ·
                    refine ⟨5344700320497199297480961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14252534187992531459949229 5344700320497199297480961)
                    ·
                      refine ⟨4008525240372899473110721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344700320497199297480961 4008525240372899473110721)
                      ·
                        rfl

theorem cell23_7806575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 3, 2].length) (baseStart_7806575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806575 prefixEnd_7806575 := by exact prefixLift 7806575
  have htrace : WordTrace (prefixWord ++ tailWord_7806575) baseStart_7806575 baseEnd_7806575 := by
    simpa [prefixWord, tailWord_7806575, baseEnd_7806575] using wordTrace_append hprefix tailTrace_7806575
  have hstable : (prefixWord ++ tailWord_7806575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806575).length < 2 ^ (prefixWord ++ tailWord_7806575).sum := by decide
  have hdescent : baseEnd_7806575 < baseStart_7806575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806592 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 2, 3, 2]
def baseStart_7806592 : Nat := 118140960795 + 7806592 * 2 ^ 59
def prefixEnd_7806592 : Nat := 4983230072969 + 3 ^ 40 * 7806592 * 2
def baseEnd_7806592 : Nat := 4008533969544025906598143

theorem tailTrace_7806592 : CollatzResearch.WordTrace tailWord_7806592 prefixEnd_7806592 4008533969544025906598143 := by
  unfold tailWord_7806592
  simp only [CollatzResearch.WordTrace]
  refine ⟨142364900867028959306239015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189819867822705279074985353 142364900867028959306239015)
  ·
    refine ⟨213547351300543438959358523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142364900867028959306239015 213547351300543438959358523)
    ·
      refine ⟨320321026950815158439037785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213547351300543438959358523 320321026950815158439037785)
      ·
        refine ⟨240240770213111368829278339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320321026950815158439037785 240240770213111368829278339)
        ·
          refine ⟨360361155319667053243917509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240240770213111368829278339 360361155319667053243917509)
          ·
            refine ⟨67567716622437572483234533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360361155319667053243917509 67567716622437572483234533)
            ·
              refine ⟨12668946866707044840606475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67567716622437572483234533 12668946866707044840606475)
              ·
                refine ⟨19003420300060567260909713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12668946866707044840606475 19003420300060567260909713)
                ·
                  refine ⟨14252565225045425445682285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19003420300060567260909713 14252565225045425445682285)
                  ·
                    refine ⟨5344711959392034542130857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14252565225045425445682285 5344711959392034542130857)
                    ·
                      refine ⟨4008533969544025906598143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344711959392034542130857 4008533969544025906598143)
                      ·
                        rfl

theorem cell23_7806592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_7806592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806592 prefixEnd_7806592 := by exact prefixLift 7806592
  have htrace : WordTrace (prefixWord ++ tailWord_7806592) baseStart_7806592 baseEnd_7806592 := by
    simpa [prefixWord, tailWord_7806592, baseEnd_7806592] using wordTrace_append hprefix tailTrace_7806592
  have hstable : (prefixWord ++ tailWord_7806592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806592).length < 2 ^ (prefixWord ++ tailWord_7806592).sum := by decide
  have hdescent : baseEnd_7806592 < baseStart_7806592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806616 : List Nat := [2, 1, 2, 4, 1, 2, 4, 2, 1, 1, 3]
def baseStart_7806616 : Nat := 118140960795 + 7806616 * 2 ^ 59
def prefixEnd_7806616 : Nat := 4983230072969 + 3 ^ 40 * 7806616 * 2
def baseEnd_7806616 : Nat := 4008546293079733812698033

theorem tailTrace_7806616 : CollatzResearch.WordTrace tailWord_7806616 prefixEnd_7806616 4008546293079733812698033 := by
  unfold tailWord_7806616
  simp only [CollatzResearch.WordTrace]
  refine ⟨142365338542985485355675851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189820451390647313807567801 142365338542985485355675851)
  ·
    refine ⟨213548007814478228033513777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142365338542985485355675851 213548007814478228033513777)
    ·
      refine ⟨160161005860858671025135333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213548007814478228033513777 160161005860858671025135333)
      ·
        refine ⟨30030188598911000817212875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160161005860858671025135333 30030188598911000817212875)
        ·
          refine ⟨45045282898366501225819313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30030188598911000817212875 45045282898366501225819313)
          ·
            refine ⟨33783962173774875919364485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45045282898366501225819313 33783962173774875919364485)
            ·
              refine ⟨6334492907582789234880841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33783962173774875919364485 6334492907582789234880841)
              ·
                refine ⟨4750869680687091926160631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6334492907582789234880841 4750869680687091926160631)
                ·
                  refine ⟨7126304521030637889240947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4750869680687091926160631 7126304521030637889240947)
                  ·
                    refine ⟨10689456781545956833861421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7126304521030637889240947 10689456781545956833861421)
                    ·
                      refine ⟨4008546293079733812698033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10689456781545956833861421 4008546293079733812698033)
                      ·
                        rfl

theorem cell23_7806616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_7806616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806616 prefixEnd_7806616 := by exact prefixLift 7806616
  have htrace : WordTrace (prefixWord ++ tailWord_7806616) baseStart_7806616 baseEnd_7806616 := by
    simpa [prefixWord, tailWord_7806616, baseEnd_7806616] using wordTrace_append hprefix tailTrace_7806616
  have hstable : (prefixWord ++ tailWord_7806616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806616).length < 2 ^ (prefixWord ++ tailWord_7806616).sum := by decide
  have hdescent : baseEnd_7806616 < baseStart_7806616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806622 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7806622 : Nat := 118140960795 + 7806622 * 2 ^ 59
def prefixEnd_7806622 : Nat := 4983230072969 + 3 ^ 40 * 7806622 * 2
def baseEnd_7806622 : Nat := 4008549373963660789223005

theorem tailTrace_7806622 : CollatzResearch.WordTrace tailWord_7806622 prefixEnd_7806622 4008549373963660789223005 := by
  unfold tailWord_7806622
  simp only [CollatzResearch.WordTrace]
  refine ⟨35591361990493654217008765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189820597282632822490713413 35591361990493654217008765)
  ·
    refine ⟨13346760746435120331378287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35591361990493654217008765 13346760746435120331378287)
    ·
      refine ⟨20020141119652680497067431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13346760746435120331378287 20020141119652680497067431)
      ·
        refine ⟨30030211679479020745601147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20020141119652680497067431 30030211679479020745601147)
        ·
          refine ⟨45045317519218531118401721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30030211679479020745601147 45045317519218531118401721)
          ·
            refine ⟨33783988139413898338801291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45045317519218531118401721 33783988139413898338801291)
            ·
              refine ⟨50675982209120847508201937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33783988139413898338801291 50675982209120847508201937)
              ·
                refine ⟨38006986656840635631151453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50675982209120847508201937 38006986656840635631151453)
                ·
                  refine ⟨14252619996315238361681795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38006986656840635631151453 14252619996315238361681795)
                  ·
                    refine ⟨21378929994472857542522693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14252619996315238361681795 21378929994472857542522693)
                    ·
                      refine ⟨4008549373963660789223005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21378929994472857542522693 4008549373963660789223005)
                      ·
                        rfl

theorem cell23_7806622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7806622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806622 prefixEnd_7806622 := by exact prefixLift 7806622
  have htrace : WordTrace (prefixWord ++ tailWord_7806622) baseStart_7806622 baseEnd_7806622 := by
    simpa [prefixWord, tailWord_7806622, baseEnd_7806622] using wordTrace_append hprefix tailTrace_7806622
  have hstable : (prefixWord ++ tailWord_7806622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806622).length < 2 ^ (prefixWord ++ tailWord_7806622).sum := by decide
  have hdescent : baseEnd_7806622 < baseStart_7806622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806655 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 3]
def baseStart_7806655 : Nat := 118140960795 + 7806655 * 2 ^ 59
def prefixEnd_7806655 : Nat := 4983230072969 + 3 ^ 40 * 7806655 * 2
def baseEnd_7806655 : Nat := 4008566318825259160110353

theorem tailTrace_7806655 : CollatzResearch.WordTrace tailWord_7806655 prefixEnd_7806655 4008566318825259160110353 := by
  unfold tailWord_7806655
  simp only [CollatzResearch.WordTrace]
  refine ⟨284732099532829680372021419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189821399688553120248014279 284732099532829680372021419)
  ·
    refine ⟨427098149299244520558032129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284732099532829680372021419 427098149299244520558032129)
    ·
      refine ⟨320323611974433390418524097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427098149299244520558032129 320323611974433390418524097)
      ·
        refine ⟨240242708980825042813893073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320323611974433390418524097 240242708980825042813893073)
        ·
          refine ⟨180182031735618782110419805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240242708980825042813893073 180182031735618782110419805)
          ·
            refine ⟨67568261900857043291407427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180182031735618782110419805 67568261900857043291407427)
            ·
              refine ⟨101352392851285564937111141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67568261900857043291407427 101352392851285564937111141)
              ·
                refine ⟨19003573659616043425708339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101352392851285564937111141 19003573659616043425708339)
                ·
                  refine ⟨28505360489424065138562509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19003573659616043425708339 28505360489424065138562509)
                  ·
                    refine ⟨10689510183534024426960941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28505360489424065138562509 10689510183534024426960941)
                    ·
                      refine ⟨4008566318825259160110353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10689510183534024426960941 4008566318825259160110353)
                      ·
                        rfl

theorem cell23_7806655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_7806655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806655 prefixEnd_7806655 := by exact prefixLift 7806655
  have htrace : WordTrace (prefixWord ++ tailWord_7806655) baseStart_7806655 baseEnd_7806655 := by
    simpa [prefixWord, tailWord_7806655, baseEnd_7806655] using wordTrace_append hprefix tailTrace_7806655
  have hstable : (prefixWord ++ tailWord_7806655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806655).length < 2 ^ (prefixWord ++ tailWord_7806655).sum := by decide
  have hdescent : baseEnd_7806655 < baseStart_7806655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806656 : List Nat := [2, 1, 1, 2, 4, 1, 4, 3, 1, 2, 2]
def baseStart_7806656 : Nat := 118140960795 + 7806656 * 2 ^ 59
def prefixEnd_7806656 : Nat := 4983230072969 + 3 ^ 40 * 7806656 * 2
def baseEnd_7806656 : Nat := 4008566832305913656197849

theorem tailTrace_7806656 : CollatzResearch.WordTrace tailWord_7806656 prefixEnd_7806656 4008566832305913656197849 := by
  unfold tailWord_7806656
  simp only [CollatzResearch.WordTrace]
  refine ⟨142366068002913028771403911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189821424003884038361871881 142366068002913028771403911)
  ·
    refine ⟨213549102004369543157105867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142366068002913028771403911 213549102004369543157105867)
    ·
      refine ⟨320323653006554314735658801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213549102004369543157105867 320323653006554314735658801)
      ·
        refine ⟨240242739754915736051744101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320323653006554314735658801 240242739754915736051744101)
        ·
          refine ⟨45045513704046700509702019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240242739754915736051744101 45045513704046700509702019)
          ·
            refine ⟨67568270556070050764553029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45045513704046700509702019 67568270556070050764553029)
            ·
              refine ⟨12669050729263134518353693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67568270556070050764553029 12669050729263134518353693)
              ·
                refine ⟨4750894023473675444382635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12669050729263134518353693 4750894023473675444382635)
                ·
                  refine ⟨7126341035210513166573953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4750894023473675444382635 7126341035210513166573953)
                  ·
                    refine ⟨5344755776407884874930465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7126341035210513166573953 5344755776407884874930465)
                    ·
                      refine ⟨4008566832305913656197849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344755776407884874930465 4008566832305913656197849)
                      ·
                        rfl

theorem cell23_7806656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 1, 2, 2].length) (baseStart_7806656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806656 prefixEnd_7806656 := by exact prefixLift 7806656
  have htrace : WordTrace (prefixWord ++ tailWord_7806656) baseStart_7806656 baseEnd_7806656 := by
    simpa [prefixWord, tailWord_7806656, baseEnd_7806656] using wordTrace_append hprefix tailTrace_7806656
  have hstable : (prefixWord ++ tailWord_7806656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806656).length < 2 ^ (prefixWord ++ tailWord_7806656).sum := by decide
  have hdescent : baseEnd_7806656 < baseStart_7806656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806666 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 2, 4]
def baseStart_7806666 : Nat := 118140960795 + 7806666 * 2 ^ 59
def prefixEnd_7806666 : Nat := 4983230072969 + 3 ^ 40 * 7806666 * 2
def baseEnd_7806666 : Nat := 1336190655704152872357601

theorem tailTrace_7806666 : CollatzResearch.WordTrace tailWord_7806666 prefixEnd_7806666 1336190655704152872357601 := by
  unfold tailWord_7806666
  simp only [CollatzResearch.WordTrace]
  refine ⟨71183125183947457312667963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189821667157193219500447901 71183125183947457312667963)
  ·
    refine ⟨106774687775921185969001945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71183125183947457312667963 106774687775921185969001945)
    ·
      refine ⟨80081015831940889476751459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106774687775921185969001945 80081015831940889476751459)
      ·
        refine ⟨120121523747911334215127189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80081015831940889476751459 120121523747911334215127189)
        ·
          refine ⟨5630696425683343791334087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120121523747911334215127189 5630696425683343791334087)
          ·
            refine ⟨8446044638525015687001131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5630696425683343791334087 8446044638525015687001131)
            ·
              refine ⟨12669066957787523530501697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8446044638525015687001131 12669066957787523530501697)
              ·
                refine ⟨9501800218340642647876273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12669066957787523530501697 9501800218340642647876273)
                ·
                  refine ⟨7126350163755481985907205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9501800218340642647876273 7126350163755481985907205)
                  ·
                    refine ⟨1336190655704152872357601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7126350163755481985907205 1336190655704152872357601)
                    ·
                      rfl

theorem cell23_7806666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_7806666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806666 prefixEnd_7806666 := by exact prefixLift 7806666
  have htrace : WordTrace (prefixWord ++ tailWord_7806666) baseStart_7806666 baseEnd_7806666 := by
    simpa [prefixWord, tailWord_7806666, baseEnd_7806666] using wordTrace_append hprefix tailTrace_7806666
  have hstable : (prefixWord ++ tailWord_7806666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806666).length < 2 ^ (prefixWord ++ tailWord_7806666).sum := by decide
  have hdescent : baseEnd_7806666 < baseStart_7806666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806672 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 2, 1, 3]
def baseStart_7806672 : Nat := 118140960795 + 7806672 * 2 ^ 59
def prefixEnd_7806672 : Nat := 4983230072969 + 3 ^ 40 * 7806672 * 2
def baseEnd_7806672 : Nat := 4008575047996385593597775

theorem tailTrace_7806672 : CollatzResearch.WordTrace tailWord_7806672 prefixEnd_7806672 4008575047996385593597775 := by
  unfold tailWord_7806672
  simp only [CollatzResearch.WordTrace]
  refine ⟨142366359786884046137695135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189821813049178728183593513 142366359786884046137695135)
  ·
    refine ⟨213549539680326069206542703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142366359786884046137695135 213549539680326069206542703)
    ·
      refine ⟨320324309520489103809814055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213549539680326069206542703 320324309520489103809814055)
      ·
        refine ⟨480486464280733655714721083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320324309520489103809814055 480486464280733655714721083)
        ·
          refine ⟨720729696421100483572081625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480486464280733655714721083 720729696421100483572081625)
          ·
            refine ⟨540547272315825362679061219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720729696421100483572081625 540547272315825362679061219)
            ·
              refine ⟨810820908473738044018591829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540547272315825362679061219 810820908473738044018591829)
              ·
                refine ⟨9501807521176617703342873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 810820908473738044018591829 9501807521176617703342873)
                ·
                  refine ⟨7126355640882463277507155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9501807521176617703342873 7126355640882463277507155)
                  ·
                    refine ⟨10689533461323694916260733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7126355640882463277507155 10689533461323694916260733)
                    ·
                      refine ⟨4008575047996385593597775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10689533461323694916260733 4008575047996385593597775)
                      ·
                        rfl

theorem cell23_7806672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2, 1, 3].length) (baseStart_7806672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806672 prefixEnd_7806672 := by exact prefixLift 7806672
  have htrace : WordTrace (prefixWord ++ tailWord_7806672) baseStart_7806672 baseEnd_7806672 := by
    simpa [prefixWord, tailWord_7806672, baseEnd_7806672] using wordTrace_append hprefix tailTrace_7806672
  have hstable : (prefixWord ++ tailWord_7806672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806672).length < 2 ^ (prefixWord ++ tailWord_7806672).sum := by decide
  have hdescent : baseEnd_7806672 < baseStart_7806672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806689 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_7806689 : Nat := 118140960795 + 7806689 * 2 ^ 59
def prefixEnd_7806689 : Nat := 4983230072969 + 3 ^ 40 * 7806689 * 2
def baseEnd_7806689 : Nat := 4008583777167512027085197

theorem tailTrace_7806689 : CollatzResearch.WordTrace tailWord_7806689 prefixEnd_7806689 4008583777167512027085197 := by
  unfold tailWord_7806689
  simp only [CollatzResearch.WordTrace]
  refine ⟨284733339614706504178759121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189822226409804336119172747 284733339614706504178759121)
  ·
    refine ⟨213550004711029878134069341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284733339614706504178759121 213550004711029878134069341)
    ·
      refine ⟨80081251766636204300276003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213550004711029878134069341 80081251766636204300276003)
      ·
        refine ⟨120121877649954306450414005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80081251766636204300276003 120121877649954306450414005)
        ·
          refine ⟨11261426029683216229726313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120121877649954306450414005 11261426029683216229726313)
          ·
            refine ⟨8446069522262412172294735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11261426029683216229726313 8446069522262412172294735)
            ·
              refine ⟨12669104283393618258442103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8446069522262412172294735 12669104283393618258442103)
              ·
                refine ⟨19003656425090427387663155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12669104283393618258442103 19003656425090427387663155)
                ·
                  refine ⟨28505484637635641081494733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19003656425090427387663155 28505484637635641081494733)
                  ·
                    refine ⟨10689556739113365405560525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28505484637635641081494733 10689556739113365405560525)
                    ·
                      refine ⟨4008583777167512027085197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10689556739113365405560525 4008583777167512027085197)
                      ·
                        rfl

theorem cell23_7806689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_7806689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806689 prefixEnd_7806689 := by exact prefixLift 7806689
  have htrace : WordTrace (prefixWord ++ tailWord_7806689) baseStart_7806689 baseEnd_7806689 := by
    simpa [prefixWord, tailWord_7806689, baseEnd_7806689] using wordTrace_append hprefix tailTrace_7806689
  have hstable : (prefixWord ++ tailWord_7806689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806689).length < 2 ^ (prefixWord ++ tailWord_7806689).sum := by decide
  have hdescent : baseEnd_7806689 < baseStart_7806689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806729 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 2, 2, 2]
def baseStart_7806729 : Nat := 118140960795 + 7806729 * 2 ^ 59
def prefixEnd_7806729 : Nat := 4983230072969 + 3 ^ 40 * 7806729 * 2
def baseEnd_7806729 : Nat := 4008604316393691870585013

theorem tailTrace_7806729 : CollatzResearch.WordTrace tailWord_7806729 prefixEnd_7806729 4008604316393691870585013 := by
  unfold tailWord_7806729
  simp only [CollatzResearch.WordTrace]
  refine ⟨284734798534561591010215241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189823199023041060673476827 284734798534561591010215241)
  ·
    refine ⟨213551098900921193257661431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284734798534561591010215241 213551098900921193257661431)
    ·
      refine ⟨320326648351381789886492147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213551098900921193257661431 320326648351381789886492147)
      ·
        refine ⟨480489972527072684829738221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320326648351381789886492147 480489972527072684829738221)
        ·
          refine ⟨180183739697652256811151833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480489972527072684829738221 180183739697652256811151833)
          ·
            refine ⟨135137804773239192608363875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180183739697652256811151833 135137804773239192608363875)
            ·
              refine ⟨202706707159858788912545813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135137804773239192608363875 202706707159858788912545813)
              ·
                refine ⟨9501876898118380730275585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 202706707159858788912545813 9501876898118380730275585)
                ·
                  refine ⟨7126407673588785547706689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9501876898118380730275585 7126407673588785547706689)
                  ·
                    refine ⟨5344805755191589160780017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7126407673588785547706689 5344805755191589160780017)
                    ·
                      refine ⟨4008604316393691870585013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344805755191589160780017 4008604316393691870585013)
                      ·
                        rfl

theorem cell23_7806729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 2, 2].length) (baseStart_7806729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806729 prefixEnd_7806729 := by exact prefixLift 7806729
  have htrace : WordTrace (prefixWord ++ tailWord_7806729) baseStart_7806729 baseEnd_7806729 := by
    simpa [prefixWord, tailWord_7806729, baseEnd_7806729] using wordTrace_append hprefix tailTrace_7806729
  have hstable : (prefixWord ++ tailWord_7806729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806729).length < 2 ^ (prefixWord ++ tailWord_7806729).sum := by decide
  have hdescent : baseEnd_7806729 < baseStart_7806729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806740 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7806740 : Nat := 118140960795 + 7806740 * 2 ^ 59
def prefixEnd_7806740 : Nat := 4983230072969 + 3 ^ 40 * 7806740 * 2
def baseEnd_7806740 : Nat := 4008609964680891327547463

theorem tailTrace_7806740 : CollatzResearch.WordTrace tailWord_7806740 prefixEnd_7806740 4008609964680891327547463 := by
  unfold tailWord_7806740
  simp only [CollatzResearch.WordTrace]
  refine ⟨142367599868760869944432837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189823466491681159925910449 142367599868760869944432837)
  ·
    refine ⟨26693924975392663114581157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142367599868760869944432837 26693924975392663114581157)
    ·
      refine ⟨5005110932886124333983967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26693924975392663114581157 5005110932886124333983967)
      ·
        refine ⟨7507666399329186500975951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5005110932886124333983967 7507666399329186500975951)
        ·
          refine ⟨11261499598993779751463927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7507666399329186500975951 11261499598993779751463927)
          ·
            refine ⟨16892249398490669627195891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11261499598993779751463927 16892249398490669627195891)
            ·
              refine ⟨25338374097736004440793837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16892249398490669627195891 25338374097736004440793837)
              ·
                refine ⟨9501890286651001665297689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25338374097736004440793837 9501890286651001665297689)
                ·
                  refine ⟨7126417714988251248973267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9501890286651001665297689 7126417714988251248973267)
                  ·
                    refine ⟨10689626572482376873459901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7126417714988251248973267 10689626572482376873459901)
                    ·
                      refine ⟨4008609964680891327547463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10689626572482376873459901 4008609964680891327547463)
                      ·
                        rfl

theorem cell23_7806740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7806740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806740 prefixEnd_7806740 := by exact prefixLift 7806740
  have htrace : WordTrace (prefixWord ++ tailWord_7806740) baseStart_7806740 baseEnd_7806740 := by
    simpa [prefixWord, tailWord_7806740, baseEnd_7806740] using wordTrace_append hprefix tailTrace_7806740
  have hstable : (prefixWord ++ tailWord_7806740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806740).length < 2 ^ (prefixWord ++ tailWord_7806740).sum := by decide
  have hdescent : baseEnd_7806740 < baseStart_7806740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806745 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 6, 3, 3]
def baseStart_7806745 : Nat := 118140960795 + 7806745 * 2 ^ 59
def prefixEnd_7806745 : Nat := 4983230072969 + 3 ^ 40 * 7806745 * 2
def baseEnd_7806745 : Nat := 4008612532084163807984939

theorem tailTrace_7806745 : CollatzResearch.WordTrace tailWord_7806745 prefixEnd_7806745 4008612532084163807984939 := by
  unfold tailWord_7806745
  simp only [CollatzResearch.WordTrace]
  refine ⟨284735382102503625742797689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189823588068335750495198459 284735382102503625742797689)
  ·
    refine ⟨213551536576877719307098267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284735382102503625742797689 213551536576877719307098267)
    ·
      refine ⟨320327304865316578960647401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213551536576877719307098267 320327304865316578960647401)
      ·
        refine ⟨240245478648987434220485551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320327304865316578960647401 240245478648987434220485551)
        ·
          refine ⟨360368217973481151330728327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240245478648987434220485551 360368217973481151330728327)
          ·
            refine ⟨540552326960221726996092491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360368217973481151330728327 540552326960221726996092491)
            ·
              refine ⟨810828490440332590494138737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540552326960221726996092491 810828490440332590494138737)
              ·
                refine ⟨608121367830249442870604053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810828490440332590494138737 608121367830249442870604053)
                ·
                  refine ⟨28505689117042942634559565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 608121367830249442870604053 28505689117042942634559565)
                  ·
                    refine ⟨10689633418891103487959837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28505689117042942634559565 10689633418891103487959837)
                    ·
                      refine ⟨4008612532084163807984939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10689633418891103487959837 4008612532084163807984939)
                      ·
                        rfl

theorem cell23_7806745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_7806745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806745 prefixEnd_7806745 := by exact prefixLift 7806745
  have htrace : WordTrace (prefixWord ++ tailWord_7806745) baseStart_7806745 baseEnd_7806745 := by
    simpa [prefixWord, tailWord_7806745, baseEnd_7806745] using wordTrace_append hprefix tailTrace_7806745
  have hstable : (prefixWord ++ tailWord_7806745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806745).length < 2 ^ (prefixWord ++ tailWord_7806745).sum := by decide
  have hdescent : baseEnd_7806745 < baseStart_7806745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806746 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2]
def baseStart_7806746 : Nat := 118140960795 + 7806746 * 2 ^ 59
def prefixEnd_7806746 : Nat := 4983230072969 + 3 ^ 40 * 7806746 * 2
def baseEnd_7806746 : Nat := 4008613045564818304072435

theorem tailTrace_7806746 : CollatzResearch.WordTrace tailWord_7806746 prefixEnd_7806746 4008613045564818304072435 := by
  unfold tailWord_7806746
  simp only [CollatzResearch.WordTrace]
  refine ⟨71183854643875000728396023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189823612383666668609056061 71183854643875000728396023)
  ·
    refine ⟨106775781965812501092594035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71183854643875000728396023 106775781965812501092594035)
    ·
      refine ⟨160163672948718751638891053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106775781965812501092594035 160163672948718751638891053)
      ·
        refine ⟨60061377355769531864584145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160163672948718751638891053 60061377355769531864584145)
        ·
          refine ⟨45046033016827148898438109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60061377355769531864584145 45046033016827148898438109)
          ·
            refine ⟨16892262381310180836914291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45046033016827148898438109 16892262381310180836914291)
            ·
              refine ⟨25338393571965271255371437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16892262381310180836914291 25338393571965271255371437)
              ·
                refine ⟨9501897589486976720764289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25338393571965271255371437 9501897589486976720764289)
                ·
                  refine ⟨7126423192115232540573217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9501897589486976720764289 7126423192115232540573217)
                  ·
                    refine ⟨5344817394086424405429913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7126423192115232540573217 5344817394086424405429913)
                    ·
                      refine ⟨4008613045564818304072435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344817394086424405429913 4008613045564818304072435)
                      ·
                        rfl

theorem cell23_7806746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_7806746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806746 prefixEnd_7806746 := by exact prefixLift 7806746
  have htrace : WordTrace (prefixWord ++ tailWord_7806746) baseStart_7806746 baseEnd_7806746 := by
    simpa [prefixWord, tailWord_7806746, baseEnd_7806746] using wordTrace_append hprefix tailTrace_7806746
  have hstable : (prefixWord ++ tailWord_7806746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806746).length < 2 ^ (prefixWord ++ tailWord_7806746).sum := by decide
  have hdescent : baseEnd_7806746 < baseStart_7806746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806842 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 6]
def baseStart_7806842 : Nat := 118140960795 + 7806842 * 2 ^ 59
def prefixEnd_7806842 : Nat := 4983230072969 + 3 ^ 40 * 7806842 * 2
def baseEnd_7806842 : Nat := 445406926634183325385777

theorem tailTrace_7806842 : CollatzResearch.WordTrace tailWord_7806842 prefixEnd_7806842 445406926634183325385777 := by
  unfold tailWord_7806842
  simp only [CollatzResearch.WordTrace]
  refine ⟨71184729995788052827269695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189825946655434807539385853 71184729995788052827269695)
  ·
    refine ⟨106777094993682079240904543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71184729995788052827269695 106777094993682079240904543)
    ·
      refine ⟨160165642490523118861356815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106777094993682079240904543 160165642490523118861356815)
      ·
        refine ⟨240248463735784678292035223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160165642490523118861356815 240248463735784678292035223)
        ·
          refine ⟨360372695603677017438052835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240248463735784678292035223 360372695603677017438052835)
          ·
            refine ⟨540559043405515526157079253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360372695603677017438052835 540559043405515526157079253)
            ·
              refine ⟨12669352579816770144306545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 540559043405515526157079253 12669352579816770144306545)
              ·
                refine ⟨9502014434862577608229909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12669352579816770144306545 9502014434862577608229909)
                ·
                  refine ⟨445406926634183325385777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9502014434862577608229909 445406926634183325385777)
                  ·
                    rfl

theorem cell23_7806842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_7806842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806842 prefixEnd_7806842 := by exact prefixLift 7806842
  have htrace : WordTrace (prefixWord ++ tailWord_7806842) baseStart_7806842 baseEnd_7806842 := by
    simpa [prefixWord, tailWord_7806842, baseEnd_7806842] using wordTrace_append hprefix tailTrace_7806842
  have hstable : (prefixWord ++ tailWord_7806842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806842).length < 2 ^ (prefixWord ++ tailWord_7806842).sum := by decide
  have hdescent : baseEnd_7806842 < baseStart_7806842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806846 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7806846 : Nat := 118140960795 + 7806846 * 2 ^ 59
def prefixEnd_7806846 : Nat := 4983230072969 + 3 ^ 40 * 7806846 * 2
def baseEnd_7806846 : Nat := 1336221464543422637607325

theorem tailTrace_7806846 : CollatzResearch.WordTrace tailWord_7806846 prefixEnd_7806846 1336221464543422637607325 := by
  unfold tailWord_7806846
  simp only [CollatzResearch.WordTrace]
  refine ⟨35592383234392214999028049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189826043916758479994816261 35592383234392214999028049)
  ·
    refine ⟨26694287425794161249271037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35592383234392214999028049 26694287425794161249271037)
    ·
      refine ⟨10010357784672810468476639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26694287425794161249271037 10010357784672810468476639)
      ·
        refine ⟨15015536677009215702714959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10010357784672810468476639 15015536677009215702714959)
        ·
          refine ⟨22523305015513823554072439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15015536677009215702714959 22523305015513823554072439)
          ·
            refine ⟨33784957523270735331108659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22523305015513823554072439 33784957523270735331108659)
            ·
              refine ⟨50677436284906102996662989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33784957523270735331108659 50677436284906102996662989)
              ·
                refine ⟨19004038606839788623748621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50677436284906102996662989 19004038606839788623748621)
                ·
                  refine ⟨7126514477564920733905733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19004038606839788623748621 7126514477564920733905733)
                  ·
                    refine ⟨1336221464543422637607325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7126514477564920733905733 1336221464543422637607325)
                    ·
                      rfl

theorem cell23_7806846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7806846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806846 prefixEnd_7806846 := by exact prefixLift 7806846
  have htrace : WordTrace (prefixWord ++ tailWord_7806846) baseStart_7806846 baseEnd_7806846 := by
    simpa [prefixWord, tailWord_7806846, baseEnd_7806846] using wordTrace_append hprefix tailTrace_7806846
  have hstable : (prefixWord ++ tailWord_7806846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806846).length < 2 ^ (prefixWord ++ tailWord_7806846).sum := by decide
  have hdescent : baseEnd_7806846 < baseStart_7806846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806865 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_7806865 : Nat := 118140960795 + 7806865 * 2 ^ 59
def prefixEnd_7806865 : Nat := 4983230072969 + 3 ^ 40 * 7806865 * 2
def baseEnd_7806865 : Nat := 4008674149762703338484387

theorem tailTrace_7806865 : CollatzResearch.WordTrace tailWord_7806865 prefixEnd_7806865 4008674149762703338484387 := by
  unfold tailWord_7806865
  simp only [CollatzResearch.WordTrace]
  refine ⟨284739758862068886237166049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189826505908045924158110699 284739758862068886237166049)
  ·
    refine ⟨213554819146551664677874537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284739758862068886237166049 213554819146551664677874537)
    ·
      refine ⟨160166114359913748508405903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213554819146551664677874537 160166114359913748508405903)
      ·
        refine ⟨240249171539870622762608855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160166114359913748508405903 240249171539870622762608855)
        ·
          refine ⟨360373757309805934143913283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240249171539870622762608855 360373757309805934143913283)
          ·
            refine ⟨540560635964708901215869925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360373757309805934143913283 540560635964708901215869925)
            ·
              refine ⟨101355119243382918977975611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540560635964708901215869925 101355119243382918977975611)
              ·
                refine ⟨152032678865074378466963417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101355119243382918977975611 152032678865074378466963417)
                ·
                  refine ⟨114024509148805783850222563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152032678865074378466963417 114024509148805783850222563)
                  ·
                    refine ⟨171036763723208675775333845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114024509148805783850222563 171036763723208675775333845)
                    ·
                      refine ⟨4008674149762703338484387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171036763723208675775333845 4008674149762703338484387)
                      ·
                        rfl

theorem cell23_7806865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_7806865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806865 prefixEnd_7806865 := by exact prefixLift 7806865
  have htrace : WordTrace (prefixWord ++ tailWord_7806865) baseStart_7806865 baseEnd_7806865 := by
    simpa [prefixWord, tailWord_7806865, baseEnd_7806865] using wordTrace_append hprefix tailTrace_7806865
  have hstable : (prefixWord ++ tailWord_7806865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806865).length < 2 ^ (prefixWord ++ tailWord_7806865).sum := by decide
  have hdescent : baseEnd_7806865 < baseStart_7806865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806869 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_7806869 : Nat := 118140960795 + 7806869 * 2 ^ 59
def prefixEnd_7806869 : Nat := 4983230072969 + 3 ^ 40 * 7806869 * 2
def baseEnd_7806869 : Nat := 4008676203685321322834369

theorem tailTrace_7806869 : CollatzResearch.WordTrace tailWord_7806869 prefixEnd_7806869 4008676203685321322834369 := by
  unfold tailWord_7806869
  simp only [CollatzResearch.WordTrace]
  refine ⟨284739904754054394920311661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189826603169369596613541107 284739904754054394920311661)
  ·
    refine ⟨106777464282770398095116873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284739904754054394920311661 106777464282770398095116873)
    ·
      refine ⟨80083098212077798571337655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106777464282770398095116873 80083098212077798571337655)
      ·
        refine ⟨120124647318116697857006483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80083098212077798571337655 120124647318116697857006483)
        ·
          refine ⟨180186970977175046785509725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120124647318116697857006483 180186970977175046785509725)
          ·
            refine ⟨67570114116440642544566147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180186970977175046785509725 67570114116440642544566147)
            ·
              refine ⟨101355171174660963816849221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67570114116440642544566147 101355171174660963816849221)
              ·
                refine ⟨19004094595248930715659229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101355171174660963816849221 19004094595248930715659229)
                ·
                  refine ⟨7126535473218349018372211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19004094595248930715659229 7126535473218349018372211)
                  ·
                    refine ⟨10689803209827523527558317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7126535473218349018372211 10689803209827523527558317)
                    ·
                      refine ⟨4008676203685321322834369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10689803209827523527558317 4008676203685321322834369)
                      ·
                        rfl

theorem cell23_7806869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_7806869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806869 prefixEnd_7806869 := by exact prefixLift 7806869
  have htrace : WordTrace (prefixWord ++ tailWord_7806869) baseStart_7806869 baseEnd_7806869 := by
    simpa [prefixWord, tailWord_7806869, baseEnd_7806869] using wordTrace_append hprefix tailTrace_7806869
  have hstable : (prefixWord ++ tailWord_7806869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806869).length < 2 ^ (prefixWord ++ tailWord_7806869).sum := by decide
  have hdescent : baseEnd_7806869 < baseStart_7806869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806912 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 5]
def baseStart_7806912 : Nat := 118140960795 + 7806912 * 2 ^ 59
def prefixEnd_7806912 : Nat := 4983230072969 + 3 ^ 40 * 7806912 * 2
def baseEnd_7806912 : Nat := 4008698283353464654596671

theorem tailTrace_7806912 : CollatzResearch.WordTrace tailWord_7806912 prefixEnd_7806912 4008698283353464654596671 := by
  unfold tailWord_7806912
  simp only [CollatzResearch.WordTrace]
  refine ⟨142370736546449306632063495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189827648728599075509417993 142370736546449306632063495)
  ·
    refine ⟨213556104819673959948095243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142370736546449306632063495 213556104819673959948095243)
    ·
      refine ⟨320334157229510939922142865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213556104819673959948095243 320334157229510939922142865)
      ·
        refine ⟨240250617922133204941607149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320334157229510939922142865 240250617922133204941607149)
        ·
          refine ⟨90093981720799951853102681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240250617922133204941607149 90093981720799951853102681)
          ·
            refine ⟨67570486290599963889827011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90093981720799951853102681 67570486290599963889827011)
            ·
              refine ⟨101355729435899945834740517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67570486290599963889827011 101355729435899945834740517)
              ·
                refine ⟨19004199269231239844013847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101355729435899945834740517 19004199269231239844013847)
                ·
                  refine ⟨28506298903846859766020771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19004199269231239844013847 28506298903846859766020771)
                  ·
                    refine ⟨42759448355770289649031157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28506298903846859766020771 42759448355770289649031157)
                    ·
                      refine ⟨4008698283353464654596671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42759448355770289649031157 4008698283353464654596671)
                      ·
                        rfl

theorem cell23_7806912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_7806912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806912 prefixEnd_7806912 := by exact prefixLift 7806912
  have htrace : WordTrace (prefixWord ++ tailWord_7806912) baseStart_7806912 baseEnd_7806912 := by
    simpa [prefixWord, tailWord_7806912, baseEnd_7806912] using wordTrace_append hprefix tailTrace_7806912
  have hstable : (prefixWord ++ tailWord_7806912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806912).length < 2 ^ (prefixWord ++ tailWord_7806912).sum := by decide
  have hdescent : baseEnd_7806912 < baseStart_7806912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806922 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_7806922 : Nat := 118140960795 + 7806922 * 2 ^ 59
def prefixEnd_7806922 : Nat := 4983230072969 + 3 ^ 40 * 7806922 * 2
def baseEnd_7806922 : Nat := 4008703418160009615471625

theorem tailTrace_7806922 : CollatzResearch.WordTrace tailWord_7806922 prefixEnd_7806922 4008703418160009615471625 := by
  unfold tailWord_7806922
  simp only [CollatzResearch.WordTrace]
  refine ⟨71185459455715596242997755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189827891881908256647994013 71185459455715596242997755)
  ·
    refine ⟨106778189183573394364496633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71185459455715596242997755 106778189183573394364496633)
    ·
      refine ⟨80083641887680045773372475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106778189183573394364496633 80083641887680045773372475)
      ·
        refine ⟨120125462831520068660058713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80083641887680045773372475 120125462831520068660058713)
        ·
          refine ⟨90094097123640051495044035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120125462831520068660058713 90094097123640051495044035)
          ·
            refine ⟨135141145685460077242566053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90094097123640051495044035 135141145685460077242566053)
            ·
              refine ⟨25338964816023764482981135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135141145685460077242566053 25338964816023764482981135)
              ·
                refine ⟨38008447224035646724471703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25338964816023764482981135 38008447224035646724471703)
                ·
                  refine ⟨57012670836053470086707555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38008447224035646724471703 57012670836053470086707555)
                  ·
                    refine ⟨85519006254080205130061333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57012670836053470086707555 85519006254080205130061333)
                    ·
                      refine ⟨4008703418160009615471625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85519006254080205130061333 4008703418160009615471625)
                      ·
                        rfl

theorem cell23_7806922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_7806922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806922 prefixEnd_7806922 := by exact prefixLift 7806922
  have htrace : WordTrace (prefixWord ++ tailWord_7806922) baseStart_7806922 baseEnd_7806922 := by
    simpa [prefixWord, tailWord_7806922, baseEnd_7806922] using wordTrace_append hprefix tailTrace_7806922
  have hstable : (prefixWord ++ tailWord_7806922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806922).length < 2 ^ (prefixWord ++ tailWord_7806922).sum := by decide
  have hdescent : baseEnd_7806922 < baseStart_7806922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806926 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2]
def baseStart_7806926 : Nat := 118140960795 + 7806926 * 2 ^ 59
def prefixEnd_7806926 : Nat := 4983230072969 + 3 ^ 40 * 7806926 * 2
def baseEnd_7806926 : Nat := 4008705472082627599821607

theorem tailTrace_7806926 : CollatzResearch.WordTrace tailWord_7806926 prefixEnd_7806926 4008705472082627599821607 := by
  unfold tailWord_7806926
  simp only [CollatzResearch.WordTrace]
  refine ⟨35592747964355986706892079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189827989143231929103424421 35592747964355986706892079)
  ·
    refine ⟨53389121946533980060338119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35592747964355986706892079 53389121946533980060338119)
    ·
      refine ⟨80083682919800970090507179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53389121946533980060338119 80083682919800970090507179)
      ·
        refine ⟨120125524379701455135760769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80083682919800970090507179 120125524379701455135760769)
        ·
          refine ⟨90094143284776091351820577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120125524379701455135760769 90094143284776091351820577)
          ·
            refine ⟨67570607463582068513865433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90094143284776091351820577 67570607463582068513865433)
            ·
              refine ⟨50677955597686551385399075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67570607463582068513865433 50677955597686551385399075)
              ·
                refine ⟨76016933396529827078098613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50677955597686551385399075 76016933396529827078098613)
                ·
                  refine ⟨7126587505924671288571745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76016933396529827078098613 7126587505924671288571745)
                  ·
                    refine ⟨5344940629443503466428809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7126587505924671288571745 5344940629443503466428809)
                    ·
                      refine ⟨4008705472082627599821607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344940629443503466428809 4008705472082627599821607)
                      ·
                        rfl

theorem cell23_7806926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_7806926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806926 prefixEnd_7806926 := by exact prefixLift 7806926
  have htrace : WordTrace (prefixWord ++ tailWord_7806926) baseStart_7806926 baseEnd_7806926 := by
    simpa [prefixWord, tailWord_7806926, baseEnd_7806926] using wordTrace_append hprefix tailTrace_7806926
  have hstable : (prefixWord ++ tailWord_7806926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806926).length < 2 ^ (prefixWord ++ tailWord_7806926).sum := by decide
  have hdescent : baseEnd_7806926 < baseStart_7806926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806929 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 1, 2, 3]
def baseStart_7806929 : Nat := 118140960795 + 7806929 * 2 ^ 59
def prefixEnd_7806929 : Nat := 4983230072969 + 3 ^ 40 * 7806929 * 2
def baseEnd_7806929 : Nat := 4008707012524591088084093

theorem tailTrace_7806929 : CollatzResearch.WordTrace tailWord_7806929 prefixEnd_7806929 4008707012524591088084093 := by
  unfold tailWord_7806929
  simp only [CollatzResearch.WordTrace]
  refine ⟨284742093133837025167495841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189828062089224683444997227 284742093133837025167495841)
  ·
    refine ⟨213556569850377768875621881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284742093133837025167495841 213556569850377768875621881)
    ·
      refine ⟨160167427387783326656716411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213556569850377768875621881 160167427387783326656716411)
      ·
        refine ⟨240251141081674989985074617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160167427387783326656716411 240251141081674989985074617)
        ·
          refine ⟨180188355811256242488805963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240251141081674989985074617 180188355811256242488805963)
          ·
            refine ⟨270282533716884363733208945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180188355811256242488805963 270282533716884363733208945)
            ·
              refine ⟨202711900287663272799906709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270282533716884363733208945 202711900287663272799906709)
              ·
                refine ⟨9502120325984215912495627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 202711900287663272799906709 9502120325984215912495627)
                ·
                  refine ⟨14253180488976323868743441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9502120325984215912495627 14253180488976323868743441)
                  ·
                    refine ⟨10689885366732242901557581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14253180488976323868743441 10689885366732242901557581)
                    ·
                      refine ⟨4008707012524591088084093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10689885366732242901557581 4008707012524591088084093)
                      ·
                        rfl

theorem cell23_7806929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_7806929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806929 prefixEnd_7806929 := by exact prefixLift 7806929
  have htrace : WordTrace (prefixWord ++ tailWord_7806929) baseStart_7806929 baseEnd_7806929 := by
    simpa [prefixWord, tailWord_7806929, baseEnd_7806929] using wordTrace_append hprefix tailTrace_7806929
  have hstable : (prefixWord ++ tailWord_7806929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806929).length < 2 ^ (prefixWord ++ tailWord_7806929).sum := by decide
  have hdescent : baseEnd_7806929 < baseStart_7806929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806932 : List Nat := [2, 4, 1, 2, 1, 1, 1, 11]
def baseStart_7806932 : Nat := 118140960795 + 7806932 * 2 ^ 59
def prefixEnd_7806932 : Nat := 4983230072969 + 3 ^ 40 * 7806932 * 2
def baseEnd_7806932 : Nat := 148470687146909428753577

theorem tailTrace_7806932 : CollatzResearch.WordTrace tailWord_7806932 prefixEnd_7806932 148470687146909428753577 := by
  unfold tailWord_7806932
  simp only [CollatzResearch.WordTrace]
  refine ⟨142371101276413078339927525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189828135035217437786570033 142371101276413078339927525)
  ·
    refine ⟨26694581489327452188736411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142371101276413078339927525 26694581489327452188736411)
    ·
      refine ⟨40041872233991178283104617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26694581489327452188736411 40041872233991178283104617)
      ·
        refine ⟨30031404175493383712328463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40041872233991178283104617 30031404175493383712328463)
        ·
          refine ⟨45047106263240075568492695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30031404175493383712328463 45047106263240075568492695)
          ·
            refine ⟨67570659394860113352739043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45047106263240075568492695 67570659394860113352739043)
            ·
              refine ⟨101355989092290170029108565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67570659394860113352739043 101355989092290170029108565)
              ·
                refine ⟨148470687146909428753577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 101355989092290170029108565 148470687146909428753577)
                ·
                  rfl

theorem cell23_7806932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 11].length) (baseStart_7806932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806932 prefixEnd_7806932 := by exact prefixLift 7806932
  have htrace : WordTrace (prefixWord ++ tailWord_7806932) baseStart_7806932 baseEnd_7806932 := by
    simpa [prefixWord, tailWord_7806932, baseEnd_7806932] using wordTrace_append hprefix tailTrace_7806932
  have hstable : (prefixWord ++ tailWord_7806932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806932).length < 2 ^ (prefixWord ++ tailWord_7806932).sum := by decide
  have hdescent : baseEnd_7806932 < baseStart_7806932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806960 : List Nat := [2, 1, 1, 1, 3, 2, 6, 2, 1, 2, 2]
def baseStart_7806960 : Nat := 118140960795 + 7806960 * 2 ^ 59
def prefixEnd_7806960 : Nat := 4983230072969 + 3 ^ 40 * 7806960 * 2
def baseEnd_7806960 : Nat := 4008722930424880466796451

theorem tailTrace_7806960 : CollatzResearch.WordTrace tailWord_7806960 prefixEnd_7806960 4008722930424880466796451 := by
  unfold tailWord_7806960
  simp only [CollatzResearch.WordTrace]
  refine ⟨142371611898362358730937167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189828815864483144974582889 142371611898362358730937167)
  ·
    refine ⟨213557417847543538096405751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142371611898362358730937167 213557417847543538096405751)
    ·
      refine ⟨320336126771315307144608627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213557417847543538096405751 320336126771315307144608627)
      ·
        refine ⟨480504190156972960716912941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320336126771315307144608627 480504190156972960716912941)
        ·
          refine ⟨180189071308864860268842353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480504190156972960716912941 180189071308864860268842353)
          ·
            refine ⟨135141803481648645201631765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180189071308864860268842353 135141803481648645201631765)
            ·
              refine ⟨6334772038202280243826489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135141803481648645201631765 6334772038202280243826489)
              ·
                refine ⟨4751079028651710182869867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6334772038202280243826489 4751079028651710182869867)
                ·
                  refine ⟨7126618542977565274304801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4751079028651710182869867 7126618542977565274304801)
                  ·
                    refine ⟨5344963907233173955728601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7126618542977565274304801 5344963907233173955728601)
                    ·
                      refine ⟨4008722930424880466796451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344963907233173955728601 4008722930424880466796451)
                      ·
                        rfl

theorem cell23_7806960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 1, 2, 2].length) (baseStart_7806960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806960 prefixEnd_7806960 := by exact prefixLift 7806960
  have htrace : WordTrace (prefixWord ++ tailWord_7806960) baseStart_7806960 baseEnd_7806960 := by
    simpa [prefixWord, tailWord_7806960, baseEnd_7806960] using wordTrace_append hprefix tailTrace_7806960
  have hstable : (prefixWord ++ tailWord_7806960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806960).length < 2 ^ (prefixWord ++ tailWord_7806960).sum := by decide
  have hdescent : baseEnd_7806960 < baseStart_7806960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806966 : List Nat := [5, 1, 1, 1, 4, 2, 1, 8]
def baseStart_7806966 : Nat := 118140960795 + 7806966 * 2 ^ 59
def prefixEnd_7806966 : Nat := 4983230072969 + 3 ^ 40 * 7806966 * 2
def baseEnd_7806966 : Nat := 148471333752178053456349

theorem tailTrace_7806966 : CollatzResearch.WordTrace tailWord_7806966 prefixEnd_7806966 148471333752178053456349 := by
  unfold tailWord_7806966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17796465164668936280412047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189828961756468653657728501 17796465164668936280412047)
  ·
    refine ⟨26694697747003404420618071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17796465164668936280412047 26694697747003404420618071)
    ·
      refine ⟨40042046620505106630927107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26694697747003404420618071 40042046620505106630927107)
      ·
        refine ⟨60063069930757659946390661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40042046620505106630927107 60063069930757659946390661)
        ·
          refine ⟨11261825612017061239948249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60063069930757659946390661 11261825612017061239948249)
          ·
            refine ⟨8446369209012795929961187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11261825612017061239948249 8446369209012795929961187)
            ·
              refine ⟨12669553813519193894941781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8446369209012795929961187 12669553813519193894941781)
              ·
                refine ⟨148471333752178053456349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12669553813519193894941781 148471333752178053456349)
                ·
                  rfl

theorem cell23_7806966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_7806966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806966 prefixEnd_7806966 := by exact prefixLift 7806966
  have htrace : WordTrace (prefixWord ++ tailWord_7806966) baseStart_7806966 baseEnd_7806966 := by
    simpa [prefixWord, tailWord_7806966, baseEnd_7806966] using wordTrace_append hprefix tailTrace_7806966
  have hstable : (prefixWord ++ tailWord_7806966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806966).length < 2 ^ (prefixWord ++ tailWord_7806966).sum := by decide
  have hdescent : baseEnd_7806966 < baseStart_7806966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807029 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_7807029 : Nat := 118140960795 + 7807029 * 2 ^ 59
def prefixEnd_7807029 : Nat := 4983230072969 + 3 ^ 40 * 7807029 * 2
def baseEnd_7807029 : Nat := 4008758360590040696833633

theorem tailTrace_7807029 : CollatzResearch.WordTrace tailWord_7807029 prefixEnd_7807029 4008758360590040696833633 := by
  unfold tailWord_7807029
  simp only [CollatzResearch.WordTrace]
  refine ⟨284745740433474742246136141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189830493622316494830757427 284745740433474742246136141)
  ·
    refine ⟨106779652662553028342301053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284745740433474742246136141 106779652662553028342301053)
    ·
      refine ⟨40042369748457385628362895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106779652662553028342301053 40042369748457385628362895)
      ·
        refine ⟨60063554622686078442544343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40042369748457385628362895 60063554622686078442544343)
        ·
          refine ⟨90095331934029117663816515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60063554622686078442544343 90095331934029117663816515)
          ·
            refine ⟨135142997901043676495724773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90095331934029117663816515 135142997901043676495724773)
            ·
              refine ⟨25339312106445689342948395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135142997901043676495724773 25339312106445689342948395)
              ·
                refine ⟨38008968159668534014422593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25339312106445689342948395 38008968159668534014422593)
                ·
                  refine ⟨28506726119751400510816945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38008968159668534014422593 28506726119751400510816945)
                  ·
                    refine ⟨21380044589813550383112709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28506726119751400510816945 21380044589813550383112709)
                    ·
                      refine ⟨4008758360590040696833633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21380044589813550383112709 4008758360590040696833633)
                      ·
                        rfl

theorem cell23_7807029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_7807029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807029 prefixEnd_7807029 := by exact prefixLift 7807029
  have htrace : WordTrace (prefixWord ++ tailWord_7807029) baseStart_7807029 baseEnd_7807029 := by
    simpa [prefixWord, tailWord_7807029, baseEnd_7807029] using wordTrace_append hprefix tailTrace_7807029
  have hstable : (prefixWord ++ tailWord_7807029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807029).length < 2 ^ (prefixWord ++ tailWord_7807029).sum := by decide
  have hdescent : baseEnd_7807029 < baseStart_7807029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807079 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_7807079 : Nat := 118140960795 + 7807079 * 2 ^ 59
def prefixEnd_7807079 : Nat := 4983230072969 + 3 ^ 40 * 7807079 * 2
def baseEnd_7807079 : Nat := 4008784034622765501208403

theorem tailTrace_7807079 : CollatzResearch.WordTrace tailWord_7807079 prefixEnd_7807079 4008784034622765501208403 := by
  unfold tailWord_7807079
  simp only [CollatzResearch.WordTrace]
  refine ⟨284747564083293600785456291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189831709388862400523637527 284747564083293600785456291)
  ·
    refine ⟨427121346124940401178184437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284747564083293600785456291 427121346124940401178184437)
    ·
      refine ⟨40042626199213162610454791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427121346124940401178184437 40042626199213162610454791)
      ·
        refine ⟨60063939298819743915682187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40042626199213162610454791 60063939298819743915682187)
        ·
          refine ⟨90095908948229615873523281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60063939298819743915682187 90095908948229615873523281)
          ·
            refine ⟨67571931711172211905142461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90095908948229615873523281 67571931711172211905142461)
            ·
              refine ⟨25339474391689579464428423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67571931711172211905142461 25339474391689579464428423)
              ·
                refine ⟨38009211587534369196642635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25339474391689579464428423 38009211587534369196642635)
                ·
                  refine ⟨57013817381301553794963953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38009211587534369196642635 57013817381301553794963953)
                  ·
                    refine ⟨42760363035976165346222965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57013817381301553794963953 42760363035976165346222965)
                    ·
                      refine ⟨4008784034622765501208403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42760363035976165346222965 4008784034622765501208403)
                      ·
                        rfl

theorem cell23_7807079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_7807079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807079 prefixEnd_7807079 := by exact prefixLift 7807079
  have htrace : WordTrace (prefixWord ++ tailWord_7807079) baseStart_7807079 baseEnd_7807079 := by
    simpa [prefixWord, tailWord_7807079, baseEnd_7807079] using wordTrace_append hprefix tailTrace_7807079
  have hstable : (prefixWord ++ tailWord_7807079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807079).length < 2 ^ (prefixWord ++ tailWord_7807079).sum := by decide
  have hdescent : baseEnd_7807079 < baseStart_7807079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807089 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_7807089 : Nat := 118140960795 + 7807089 * 2 ^ 59
def prefixEnd_7807089 : Nat := 4983230072969 + 3 ^ 40 * 7807089 * 2
def baseEnd_7807089 : Nat := 4008789169429310462083357

theorem tailTrace_7807089 : CollatzResearch.WordTrace tailWord_7807089 prefixEnd_7807089 4008789169429310462083357 := by
  unfold tailWord_7807089
  simp only [CollatzResearch.WordTrace]
  refine ⟨284747928813257372493320321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189831952542171581662213547 284747928813257372493320321)
  ·
    refine ⟨213560946609943029369990241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284747928813257372493320321 213560946609943029369990241)
    ·
      refine ⟨160170709957457272027492681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213560946609943029369990241 160170709957457272027492681)
      ·
        refine ⟨120128032468092954020619511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160170709957457272027492681 120128032468092954020619511)
        ·
          refine ⟨180192048702139431030929267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120128032468092954020619511 180192048702139431030929267)
          ·
            refine ⟨270288073053209146546393901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180192048702139431030929267 270288073053209146546393901)
            ·
              refine ⟨101358027394953429954897713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270288073053209146546393901 101358027394953429954897713)
              ·
                refine ⟨76018520546215072466173285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101358027394953429954897713 76018520546215072466173285)
                ·
                  refine ⟨14253472602415326087407491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76018520546215072466173285 14253472602415326087407491)
                  ·
                    refine ⟨21380208903622989131111237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14253472602415326087407491 21380208903622989131111237)
                    ·
                      refine ⟨4008789169429310462083357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21380208903622989131111237 4008789169429310462083357)
                      ·
                        rfl

theorem cell23_7807089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_7807089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807089 prefixEnd_7807089 := by exact prefixLift 7807089
  have htrace : WordTrace (prefixWord ++ tailWord_7807089) baseStart_7807089 baseEnd_7807089 := by
    simpa [prefixWord, tailWord_7807089, baseEnd_7807089] using wordTrace_append hprefix tailTrace_7807089
  have hstable : (prefixWord ++ tailWord_7807089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807089).length < 2 ^ (prefixWord ++ tailWord_7807089).sum := by decide
  have hdescent : baseEnd_7807089 < baseStart_7807089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807124 : List Nat := [2, 4, 2, 3, 2, 1, 2, 2, 5]
def baseStart_7807124 : Nat := 118140960795 + 7807124 * 2 ^ 59
def prefixEnd_7807124 : Nat := 4983230072969 + 3 ^ 40 * 7807124 * 2
def baseEnd_7807124 : Nat := 445423015694690869460633

theorem tailTrace_7807124 : CollatzResearch.WordTrace tailWord_7807124 prefixEnd_7807124 445423015694690869460633 := by
  unfold tailWord_7807124
  simp only [CollatzResearch.WordTrace]
  refine ⟨142374602684065286735422213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189832803578753715647229617 142374602684065286735422213)
  ·
    refine ⟨26695238003262241262891665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142374602684065286735422213 26695238003262241262891665)
    ·
      refine ⟨20021428502446680947168749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26695238003262241262891665 20021428502446680947168749)
      ·
        refine ⟨7508035688417505355188281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20021428502446680947168749 7508035688417505355188281)
        ·
          refine ⟨5631026766313129016391211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7508035688417505355188281 5631026766313129016391211)
          ·
            refine ⟨8446540149469693524586817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631026766313129016391211 8446540149469693524586817)
            ·
              refine ⟨6334905112102270143440113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8446540149469693524586817 6334905112102270143440113)
              ·
                refine ⟨4751178834076702607580085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6334905112102270143440113 4751178834076702607580085)
                ·
                  refine ⟨445423015694690869460633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4751178834076702607580085 445423015694690869460633)
                  ·
                    rfl

theorem cell23_7807124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_7807124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807124 prefixEnd_7807124 := by exact prefixLift 7807124
  have htrace : WordTrace (prefixWord ++ tailWord_7807124) baseStart_7807124 baseEnd_7807124 := by
    simpa [prefixWord, tailWord_7807124, baseEnd_7807124] using wordTrace_append hprefix tailTrace_7807124
  have hstable : (prefixWord ++ tailWord_7807124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807124).length < 2 ^ (prefixWord ++ tailWord_7807124).sum := by decide
  have hdescent : baseEnd_7807124 < baseStart_7807124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807139 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 3]
def baseStart_7807139 : Nat := 118140960795 + 7807139 * 2 ^ 59
def prefixEnd_7807139 : Nat := 4983230072969 + 3 ^ 40 * 7807139 * 2
def baseEnd_7807139 : Nat := 4008814843462035266458127

theorem tailTrace_7807139 : CollatzResearch.WordTrace tailWord_7807139 prefixEnd_7807139 4008814843462035266458127 := by
  unfold tailWord_7807139
  simp only [CollatzResearch.WordTrace]
  refine ⟨284749752463076231032640471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189833168308717487355093647 284749752463076231032640471)
  ·
    refine ⟨427124628694614346548960707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284749752463076231032640471 427124628694614346548960707)
    ·
      refine ⟨640686943041921519823441061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427124628694614346548960707 640686943041921519823441061)
      ·
        refine ⟨120128801820360284966895199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 640686943041921519823441061 120128801820360284966895199)
        ·
          refine ⟨180193202730540427450342799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120128801820360284966895199 180193202730540427450342799)
          ·
            refine ⟨270289804095810641175514199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180193202730540427450342799 270289804095810641175514199)
            ·
              refine ⟨405434706143715961763271299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270289804095810641175514199 405434706143715961763271299)
              ·
                refine ⟨608152059215573942644906949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405434706143715961763271299 608152059215573942644906949)
                ·
                  refine ⟨114028511102920114245920053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 608152059215573942644906949 114028511102920114245920053)
                  ·
                    refine ⟨10690172915898760710555005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114028511102920114245920053 10690172915898760710555005)
                    ·
                      refine ⟨4008814843462035266458127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10690172915898760710555005 4008814843462035266458127)
                      ·
                        rfl

theorem cell23_7807139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_7807139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807139 prefixEnd_7807139 := by exact prefixLift 7807139
  have htrace : WordTrace (prefixWord ++ tailWord_7807139) baseStart_7807139 baseEnd_7807139 := by
    simpa [prefixWord, tailWord_7807139, baseEnd_7807139] using wordTrace_append hprefix tailTrace_7807139
  have hstable : (prefixWord ++ tailWord_7807139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807139).length < 2 ^ (prefixWord ++ tailWord_7807139).sum := by decide
  have hdescent : baseEnd_7807139 < baseStart_7807139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807157 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_7807157 : Nat := 118140960795 + 7807157 * 2 ^ 59
def prefixEnd_7807157 : Nat := 4983230072969 + 3 ^ 40 * 7807157 * 2
def baseEnd_7807157 : Nat := 4008824086113816196033045

theorem tailTrace_7807157 : CollatzResearch.WordTrace tailWord_7807157 prefixEnd_7807157 4008824086113816196033045 := by
  unfold tailWord_7807157
  simp only [CollatzResearch.WordTrace]
  refine ⟨284750408977011020106795725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189833605984674013404530483 284750408977011020106795725)
  ·
    refine ⟨106781403366379132540048397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284750408977011020106795725 106781403366379132540048397)
    ·
      refine ⟨40043026262392174702518149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106781403366379132540048397 40043026262392174702518149)
      ·
        refine ⟨7508067424198532756722153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40043026262392174702518149 7508067424198532756722153)
        ·
          refine ⟨5631050568148899567541615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7508067424198532756722153 5631050568148899567541615)
          ·
            refine ⟨8446575852223349351312423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631050568148899567541615 8446575852223349351312423)
            ·
              refine ⟨12669863778335024026968635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8446575852223349351312423 12669863778335024026968635)
              ·
                refine ⟨19004795667502536040452953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12669863778335024026968635 19004795667502536040452953)
                ·
                  refine ⟨14253596750626902030339715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19004795667502536040452953 14253596750626902030339715)
                  ·
                    refine ⟨21380395125940353045509573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14253596750626902030339715 21380395125940353045509573)
                    ·
                      refine ⟨4008824086113816196033045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21380395125940353045509573 4008824086113816196033045)
                      ·
                        rfl

theorem cell23_7807157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_7807157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807157 prefixEnd_7807157 := by exact prefixLift 7807157
  have htrace : WordTrace (prefixWord ++ tailWord_7807157) baseStart_7807157 baseEnd_7807157 := by
    simpa [prefixWord, tailWord_7807157, baseEnd_7807157] using wordTrace_append hprefix tailTrace_7807157
  have hstable : (prefixWord ++ tailWord_7807157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807157).length < 2 ^ (prefixWord ++ tailWord_7807157).sum := by decide
  have hdescent : baseEnd_7807157 < baseStart_7807157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807180 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 6]
def baseStart_7807180 : Nat := 118140960795 + 7807180 * 2 ^ 59
def prefixEnd_7807180 : Nat := 4983230072969 + 3 ^ 40 * 7807180 * 2
def baseEnd_7807180 : Nat := 445426210685429956227271

theorem tailTrace_7807180 : CollatzResearch.WordTrace tailWord_7807180 prefixEnd_7807180 445426210685429956227271 := by
  unfold tailWord_7807180
  simp only [CollatzResearch.WordTrace]
  refine ⟨142375623927963847517441497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189834165237285130023255329 142375623927963847517441497)
  ·
    refine ⟨106781717945972885638081123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142375623927963847517441497 106781717945972885638081123)
    ·
      refine ⟨160172576918959328457121685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106781717945972885638081123 160172576918959328457121685)
      ·
        refine ⟨7508089543076218521427579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160172576918959328457121685 7508089543076218521427579)
        ·
          refine ⟨11262134314614327782141369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7508089543076218521427579 11262134314614327782141369)
          ·
            refine ⟨8446600735960745836606027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11262134314614327782141369 8446600735960745836606027)
            ·
              refine ⟨12669901103941118754909041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8446600735960745836606027 12669901103941118754909041)
              ·
                refine ⟨9502425827955839066181781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12669901103941118754909041 9502425827955839066181781)
                ·
                  refine ⟨445426210685429956227271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9502425827955839066181781 445426210685429956227271)
                  ·
                    rfl

theorem cell23_7807180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_7807180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807180 prefixEnd_7807180 := by exact prefixLift 7807180
  have htrace : WordTrace (prefixWord ++ tailWord_7807180) baseStart_7807180 baseEnd_7807180 := by
    simpa [prefixWord, tailWord_7807180, baseEnd_7807180] using wordTrace_append hprefix tailTrace_7807180
  have hstable : (prefixWord ++ tailWord_7807180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807180).length < 2 ^ (prefixWord ++ tailWord_7807180).sum := by decide
  have hdescent : baseEnd_7807180 < baseStart_7807180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807209 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_7807209 : Nat := 118140960795 + 7807209 * 2 ^ 59
def prefixEnd_7807209 : Nat := 4983230072969 + 3 ^ 40 * 7807209 * 2
def baseEnd_7807209 : Nat := 4008850787107849992582805

theorem tailTrace_7807209 : CollatzResearch.WordTrace tailWord_7807209 prefixEnd_7807209 4008850787107849992582805 := by
  unfold tailWord_7807209
  simp only [CollatzResearch.WordTrace]
  refine ⟨284752305572822632987688681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189834870381881755325125787 284752305572822632987688681)
  ·
    refine ⟨213564229179616974740766511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284752305572822632987688681 213564229179616974740766511)
    ·
      refine ⟨320346343769425462111149767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213564229179616974740766511 320346343769425462111149767)
      ·
        refine ⟨480519515654138193166724651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320346343769425462111149767 480519515654138193166724651)
        ·
          refine ⟨720779273481207289750086977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480519515654138193166724651 720779273481207289750086977)
          ·
            refine ⟨540584455110905467312565233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720779273481207289750086977 540584455110905467312565233)
            ·
              refine ⟨405438341333179100484423925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540584455110905467312565233 405438341333179100484423925)
              ·
                refine ⟨38009844499985540670414743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405438341333179100484423925 38009844499985540670414743)
                ·
                  refine ⟨57014766749978311005622115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38009844499985540670414743 57014766749978311005622115)
                  ·
                    refine ⟨85522150124967466508433173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57014766749978311005622115 85522150124967466508433173)
                    ·
                      refine ⟨4008850787107849992582805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85522150124967466508433173 4008850787107849992582805)
                      ·
                        rfl

theorem cell23_7807209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_7807209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807209 prefixEnd_7807209 := by exact prefixLift 7807209
  have htrace : WordTrace (prefixWord ++ tailWord_7807209) baseStart_7807209 baseEnd_7807209 := by
    simpa [prefixWord, tailWord_7807209, baseEnd_7807209] using wordTrace_append hprefix tailTrace_7807209
  have hstable : (prefixWord ++ tailWord_7807209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807209).length < 2 ^ (prefixWord ++ tailWord_7807209).sum := by decide
  have hdescent : baseEnd_7807209 < baseStart_7807209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807216 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 3]
def baseStart_7807216 : Nat := 118140960795 + 7807216 * 2 ^ 59
def prefixEnd_7807216 : Nat := 4983230072969 + 3 ^ 40 * 7807216 * 2
def baseEnd_7807216 : Nat := 4008854381472431465195273

theorem tailTrace_7807216 : CollatzResearch.WordTrace tailWord_7807216 prefixEnd_7807216 4008854381472431465195273 := by
  unfold tailWord_7807216
  simp only [CollatzResearch.WordTrace]
  refine ⟨142376280441898636591596751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189835040589198182122129001 142376280441898636591596751)
  ·
    refine ⟨213564420662847954887395127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142376280441898636591596751 213564420662847954887395127)
    ·
      refine ⟨320346630994271932331092691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213564420662847954887395127 320346630994271932331092691)
      ·
        refine ⟨480519946491407898496639037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320346630994271932331092691 480519946491407898496639037)
        ·
          refine ⟨180194979934277961936239639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480519946491407898496639037 180194979934277961936239639)
          ·
            refine ⟨270292469901416942904359459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180194979934277961936239639 270292469901416942904359459)
            ·
              refine ⟨405438704852125414356539189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270292469901416942904359459 405438704852125414356539189)
              ·
                refine ⟨38009878579886757595925549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405438704852125414356539189 38009878579886757595925549)
                ·
                  refine ⟨14253704467457534098472081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38009878579886757595925549 14253704467457534098472081)
                  ·
                    refine ⟨10690278350593150573854061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14253704467457534098472081 10690278350593150573854061)
                    ·
                      refine ⟨4008854381472431465195273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10690278350593150573854061 4008854381472431465195273)
                      ·
                        rfl

theorem cell23_7807216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 3].length) (baseStart_7807216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807216 prefixEnd_7807216 := by exact prefixLift 7807216
  have htrace : WordTrace (prefixWord ++ tailWord_7807216) baseStart_7807216 baseEnd_7807216 := by
    simpa [prefixWord, tailWord_7807216, baseEnd_7807216] using wordTrace_append hprefix tailTrace_7807216
  have hstable : (prefixWord ++ tailWord_7807216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807216).length < 2 ^ (prefixWord ++ tailWord_7807216).sum := by decide
  have hdescent : baseEnd_7807216 < baseStart_7807216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807219 : List Nat := [1, 1, 1, 2, 2, 4, 3, 9]
def baseStart_7807219 : Nat := 118140960795 + 7807219 * 2 ^ 59
def prefixEnd_7807219 : Nat := 4983230072969 + 3 ^ 40 * 7807219 * 2
def baseEnd_7807219 : Nat := 148476145256088701979917

theorem tailTrace_7807219 : CollatzResearch.WordTrace tailWord_7807219 prefixEnd_7807219 148476145256088701979917 := by
  unfold tailWord_7807219
  simp only [CollatzResearch.WordTrace]
  refine ⟨284752670302786404695552711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189835113535190936463701807 284752670302786404695552711)
  ·
    refine ⟨427129005454179607043329067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284752670302786404695552711 427129005454179607043329067)
    ·
      refine ⟨640693508181269410564993601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427129005454179607043329067 640693508181269410564993601)
      ·
        refine ⟨480520131135952057923745201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640693508181269410564993601 480520131135952057923745201)
        ·
          refine ⟨360390098351964043442808901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480520131135952057923745201 360390098351964043442808901)
          ·
            refine ⟨67573143440993258145526669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360390098351964043442808901 67573143440993258145526669)
            ·
              refine ⟨25339928790372471804572501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67573143440993258145526669 25339928790372471804572501)
              ·
                refine ⟨148476145256088701979917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25339928790372471804572501 148476145256088701979917)
                ·
                  rfl

theorem cell23_7807219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 9].length) (baseStart_7807219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807219 prefixEnd_7807219 := by exact prefixLift 7807219
  have htrace : WordTrace (prefixWord ++ tailWord_7807219) baseStart_7807219 baseEnd_7807219 := by
    simpa [prefixWord, tailWord_7807219, baseEnd_7807219] using wordTrace_append hprefix tailTrace_7807219
  have hstable : (prefixWord ++ tailWord_7807219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807219).length < 2 ^ (prefixWord ++ tailWord_7807219).sum := by decide
  have hdescent : baseEnd_7807219 < baseStart_7807219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807233 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_7807233 : Nat := 118140960795 + 7807233 * 2 ^ 59
def prefixEnd_7807233 : Nat := 4983230072969 + 3 ^ 40 * 7807233 * 2
def baseEnd_7807233 : Nat := 4008863110643557898682695

theorem tailTrace_7807233 : CollatzResearch.WordTrace tailWord_7807233 prefixEnd_7807233 4008863110643557898682695 := by
  unfold tailWord_7807233
  simp only [CollatzResearch.WordTrace]
  refine ⟨284753180924735685086562353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189835453949823790057708235 284753180924735685086562353)
  ·
    refine ⟨213564885693551763814921765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284753180924735685086562353 213564885693551763814921765)
    ·
      refine ⟨40043416067540955715297831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213564885693551763814921765 40043416067540955715297831)
      ·
        refine ⟨60065124101311433572946747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40043416067540955715297831 60065124101311433572946747)
        ·
          refine ⟨90097686151967150359420121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60065124101311433572946747 90097686151967150359420121)
          ·
            refine ⟨67573264613975362769565091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90097686151967150359420121 67573264613975362769565091)
            ·
              refine ⟨101359896920963044154347637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67573264613975362769565091 101359896920963044154347637)
              ·
                refine ⟨9502490336340285389470091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101359896920963044154347637 9502490336340285389470091)
                ·
                  refine ⟨14253735504510428084205137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9502490336340285389470091 14253735504510428084205137)
                  ·
                    refine ⟨10690301628382821063153853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14253735504510428084205137 10690301628382821063153853)
                    ·
                      refine ⟨4008863110643557898682695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10690301628382821063153853 4008863110643557898682695)
                      ·
                        rfl

theorem cell23_7807233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_7807233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807233 prefixEnd_7807233 := by exact prefixLift 7807233
  have htrace : WordTrace (prefixWord ++ tailWord_7807233) baseStart_7807233 baseEnd_7807233 := by
    simpa [prefixWord, tailWord_7807233, baseEnd_7807233] using wordTrace_append hprefix tailTrace_7807233
  have hstable : (prefixWord ++ tailWord_7807233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807233).length < 2 ^ (prefixWord ++ tailWord_7807233).sum := by decide
  have hdescent : baseEnd_7807233 < baseStart_7807233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807303 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 3, 4, 2]
def baseStart_7807303 : Nat := 118140960795 + 7807303 * 2 ^ 59
def prefixEnd_7807303 : Nat := 4983230072969 + 3 ^ 40 * 7807303 * 2
def baseEnd_7807303 : Nat := 4008899054289372624807373

theorem tailTrace_7807303 : CollatzResearch.WordTrace tailWord_7807303 prefixEnd_7807303 4008899054289372624807373 := by
  unfold tailWord_7807303
  simp only [CollatzResearch.WordTrace]
  refine ⟨284755734034482087041610563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189837156022988058027740375 284755734034482087041610563)
  ·
    refine ⟨427133601051723130562415845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284755734034482087041610563 427133601051723130562415845)
    ·
      refine ⟨80087550197198086980452971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427133601051723130562415845 80087550197198086980452971)
      ·
        refine ⟨120131325295797130470679457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80087550197198086980452971 120131325295797130470679457)
        ·
          refine ⟨90098493971847847853009593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120131325295797130470679457 90098493971847847853009593)
          ·
            refine ⟨67573870478885885889757195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90098493971847847853009593 67573870478885885889757195)
            ·
              refine ⟨101360805718328828834635793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67573870478885885889757195 101360805718328828834635793)
              ·
                refine ⟨76020604288746621625976845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101360805718328828834635793 76020604288746621625976845)
                ·
                  refine ⟨28507726608279983109741317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76020604288746621625976845 28507726608279983109741317)
                  ·
                    refine ⟨5345198739052496833076497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28507726608279983109741317 5345198739052496833076497)
                    ·
                      refine ⟨4008899054289372624807373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5345198739052496833076497 4008899054289372624807373)
                      ·
                        rfl

theorem cell23_7807303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_7807303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807303 prefixEnd_7807303 := by exact prefixLift 7807303
  have htrace : WordTrace (prefixWord ++ tailWord_7807303) baseStart_7807303 baseEnd_7807303 := by
    simpa [prefixWord, tailWord_7807303, baseEnd_7807303] using wordTrace_append hprefix tailTrace_7807303
  have hstable : (prefixWord ++ tailWord_7807303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807303).length < 2 ^ (prefixWord ++ tailWord_7807303).sum := by decide
  have hdescent : baseEnd_7807303 < baseStart_7807303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807390 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7807390 : Nat := 118140960795 + 7807390 * 2 ^ 59
def prefixEnd_7807390 : Nat := 4983230072969 + 3 ^ 40 * 7807390 * 2
def baseEnd_7807390 : Nat := 1336314575702104594806491

theorem tailTrace_7807390 : CollatzResearch.WordTrace tailWord_7807390 prefixEnd_7807390 1336314575702104594806491 := by
  unfold tailWord_7807390
  simp only [CollatzResearch.WordTrace]
  refine ⟨35594863398145862612503453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189839271456777933933351749 35594863398145862612503453)
  ·
    refine ⟨13348073774304698479688795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35594863398145862612503453 13348073774304698479688795)
    ·
      refine ⟨20022110661457047719533193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13348073774304698479688795 20022110661457047719533193)
      ·
        refine ⟨15016582996092785789649895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20022110661457047719533193 15016582996092785789649895)
        ·
          refine ⟨22524874494139178684474843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15016582996092785789649895 22524874494139178684474843)
          ·
            refine ⟨33787311741208768026712265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22524874494139178684474843 33787311741208768026712265)
            ·
              refine ⟨25340483805906576020034199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33787311741208768026712265 25340483805906576020034199)
              ·
                refine ⟨38010725708859864030051299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25340483805906576020034199 38010725708859864030051299)
                ·
                  refine ⟨57016088563289796045076949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38010725708859864030051299 57016088563289796045076949)
                  ·
                    refine ⟨1336314575702104594806491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57016088563289796045076949 1336314575702104594806491)
                    ·
                      rfl

theorem cell23_7807390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7807390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807390 prefixEnd_7807390 := by exact prefixLift 7807390
  have htrace : WordTrace (prefixWord ++ tailWord_7807390) baseStart_7807390 baseEnd_7807390 := by
    simpa [prefixWord, tailWord_7807390, baseEnd_7807390] using wordTrace_append hprefix tailTrace_7807390
  have hstable : (prefixWord ++ tailWord_7807390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807390).length < 2 ^ (prefixWord ++ tailWord_7807390).sum := by decide
  have hdescent : baseEnd_7807390 < baseStart_7807390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807493 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_7807493 : Nat := 118140960795 + 7807493 * 2 ^ 59
def prefixEnd_7807493 : Nat := 4983230072969 + 3 ^ 40 * 7807493 * 2
def baseEnd_7807493 : Nat := 1336332205204575627143833

theorem tailTrace_7807493 : CollatzResearch.WordTrace tailWord_7807493 prefixEnd_7807493 1336332205204575627143833 := by
  unfold tailWord_7807493
  simp only [CollatzResearch.WordTrace]
  refine ⟨284762663903793749491027133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189841775935862499660684755 284762663903793749491027133)
  ·
    refine ⟨106785998963922656059135175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284762663903793749491027133 106785998963922656059135175)
    ·
      refine ⟨160178998445883984088702763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106785998963922656059135175 160178998445883984088702763)
      ·
        refine ⟨240268497668825976133054145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160178998445883984088702763 240268497668825976133054145)
        ·
          refine ⟨180201373251619482099790609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240268497668825976133054145 180201373251619482099790609)
          ·
            refine ⟨135151029938714611574842957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180201373251619482099790609 135151029938714611574842957)
            ·
              refine ⟨50681636227017979340566109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135151029938714611574842957 50681636227017979340566109)
              ·
                refine ⟨19005613585131742252712291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50681636227017979340566109 19005613585131742252712291)
                ·
                  refine ⟨28508420377697613379068437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19005613585131742252712291 28508420377697613379068437)
                  ·
                    refine ⟨1336332205204575627143833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28508420377697613379068437 1336332205204575627143833)
                    ·
                      rfl

theorem cell23_7807493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_7807493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807493 prefixEnd_7807493 := by exact prefixLift 7807493
  have htrace : WordTrace (prefixWord ++ tailWord_7807493) baseStart_7807493 baseEnd_7807493 := by
    simpa [prefixWord, tailWord_7807493, baseEnd_7807493] using wordTrace_append hprefix tailTrace_7807493
  have hstable : (prefixWord ++ tailWord_7807493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807493).length < 2 ^ (prefixWord ++ tailWord_7807493).sum := by decide
  have hdescent : baseEnd_7807493 < baseStart_7807493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807500 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_7807500 : Nat := 118140960795 + 7807500 * 2 ^ 59
def prefixEnd_7807500 : Nat := 4983230072969 + 3 ^ 40 * 7807500 * 2
def baseEnd_7807500 : Nat := 4009000209978308354043967

theorem tailTrace_7807500 : CollatzResearch.WordTrace tailWord_7807500 prefixEnd_7807500 4009000209978308354043967 := by
  unfold tailWord_7807500
  simp only [CollatzResearch.WordTrace]
  refine ⟨142381459607384194843265977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189841946143178926457687969 142381459607384194843265977)
  ·
    refine ⟨106786094705538146132449483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142381459607384194843265977 106786094705538146132449483)
    ·
      refine ⟨160179142058307219198674225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106786094705538146132449483 160179142058307219198674225)
      ·
        refine ⟨120134356543730414399005669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160179142058307219198674225 120134356543730414399005669)
        ·
          refine ⟨22525191851949452699813563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120134356543730414399005669 22525191851949452699813563)
          ·
            refine ⟨33787787777924179049720345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22525191851949452699813563 33787787777924179049720345)
            ·
              refine ⟨25340840833443134287290259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33787787777924179049720345 25340840833443134287290259)
              ·
                refine ⟨38011261250164701430935389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25340840833443134287290259 38011261250164701430935389)
                ·
                  refine ⟨14254222968811763036600771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38011261250164701430935389 14254222968811763036600771)
                  ·
                    refine ⟨21381334453217644554901157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14254222968811763036600771 21381334453217644554901157)
                    ·
                      refine ⟨4009000209978308354043967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21381334453217644554901157 4009000209978308354043967)
                      ·
                        rfl

theorem cell23_7807500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_7807500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807500 prefixEnd_7807500 := by exact prefixLift 7807500
  have htrace : WordTrace (prefixWord ++ tailWord_7807500) baseStart_7807500 baseEnd_7807500 := by
    simpa [prefixWord, tailWord_7807500, baseEnd_7807500] using wordTrace_append hprefix tailTrace_7807500
  have hstable : (prefixWord ++ tailWord_7807500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807500).length < 2 ^ (prefixWord ++ tailWord_7807500).sum := by decide
  have hdescent : baseEnd_7807500 < baseStart_7807500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807517 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_7807517 : Nat := 118140960795 + 7807517 * 2 ^ 59
def prefixEnd_7807517 : Nat := 4983230072969 + 3 ^ 40 * 7807517 * 2
def baseEnd_7807517 : Nat := 4009008939149434787531389

theorem tailTrace_7807517 : CollatzResearch.WordTrace tailWord_7807517 prefixEnd_7807517 4009008939149434787531389 := by
  unfold tailWord_7807517
  simp only [CollatzResearch.WordTrace]
  refine ⟨284763539255706801589900805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189842359503804534393267203 284763539255706801589900805)
  ·
    refine ⟨53393163610445025298106401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284763539255706801589900805 53393163610445025298106401)
    ·
      refine ⟨40044872707833768973579801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53393163610445025298106401 40044872707833768973579801)
      ·
        refine ⟨30033654530875326730184851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40044872707833768973579801 30033654530875326730184851)
        ·
          refine ⟨45050481796312990095277277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30033654530875326730184851 45050481796312990095277277)
          ·
            refine ⟨16893930673617371285728979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45050481796312990095277277 16893930673617371285728979)
            ·
              refine ⟨25340896010426056928593469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16893930673617371285728979 25340896010426056928593469)
              ·
                refine ⟨9502836003909771348222551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25340896010426056928593469 9502836003909771348222551)
                ·
                  refine ⟨14254254005864657022333827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9502836003909771348222551 14254254005864657022333827)
                  ·
                    refine ⟨21381381008796985533500741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14254254005864657022333827 21381381008796985533500741)
                    ·
                      refine ⟨4009008939149434787531389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21381381008796985533500741 4009008939149434787531389)
                      ·
                        rfl

theorem cell23_7807517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_7807517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807517 prefixEnd_7807517 := by exact prefixLift 7807517
  have htrace : WordTrace (prefixWord ++ tailWord_7807517) baseStart_7807517 baseEnd_7807517 := by
    simpa [prefixWord, tailWord_7807517, baseEnd_7807517] using wordTrace_append hprefix tailTrace_7807517
  have hstable : (prefixWord ++ tailWord_7807517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807517).length < 2 ^ (prefixWord ++ tailWord_7807517).sum := by decide
  have hdescent : baseEnd_7807517 < baseStart_7807517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807523 : List Nat := [1, 1, 1, 4, 4, 2, 10]
def baseStart_7807523 : Nat := 118140960795 + 7807523 * 2 ^ 59
def prefixEnd_7807523 : Nat := 4983230072969 + 3 ^ 40 * 7807523 * 2
def baseEnd_7807523 : Nat := 49493975555967429185881

theorem tailTrace_7807523 : CollatzResearch.WordTrace tailWord_7807523 prefixEnd_7807523 49493975555967429185881 := by
  unfold tailWord_7807523
  simp only [CollatzResearch.WordTrace]
  refine ⟨284763758093685064614619223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189842505395790043076412815 284763758093685064614619223)
  ·
    refine ⟨427145637140527596921928835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284763758093685064614619223 427145637140527596921928835)
    ·
      refine ⟨640718455710791395382893253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427145637140527596921928835 640718455710791395382893253)
      ·
        refine ⟨120134710445773386634292485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 640718455710791395382893253 120134710445773386634292485)
        ·
          refine ⟨22525258208582509993929841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120134710445773386634292485 22525258208582509993929841)
          ·
            refine ⟨16893943656436882495447381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22525258208582509993929841 16893943656436882495447381)
            ·
              refine ⟨49493975555967429185881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16893943656436882495447381 49493975555967429185881)
              ·
                rfl

theorem cell23_7807523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 10].length) (baseStart_7807523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807523 prefixEnd_7807523 := by exact prefixLift 7807523
  have htrace : WordTrace (prefixWord ++ tailWord_7807523) baseStart_7807523 baseEnd_7807523 := by
    simpa [prefixWord, tailWord_7807523, baseEnd_7807523] using wordTrace_append hprefix tailTrace_7807523
  have hstable : (prefixWord ++ tailWord_7807523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807523).length < 2 ^ (prefixWord ++ tailWord_7807523).sum := by decide
  have hdescent : baseEnd_7807523 < baseStart_7807523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807560 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 2, 7, 2]
def baseStart_7807560 : Nat := 118140960795 + 7807560 * 2 ^ 59
def prefixEnd_7807560 : Nat := 4983230072969 + 3 ^ 40 * 7807560 * 2
def baseEnd_7807560 : Nat := 4009031018817578119293691

theorem tailTrace_7807560 : CollatzResearch.WordTrace tailWord_7807560 prefixEnd_7807560 4009031018817578119293691 := by
  unfold tailWord_7807560
  simp only [CollatzResearch.WordTrace]
  refine ⟨142382553797275509966858067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189843405063034013289144089 142382553797275509966858067)
  ·
    refine ⟨213573830695913264950287101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142382553797275509966858067 213573830695913264950287101)
    ·
      refine ⟨80090186510967474356357663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213573830695913264950287101 80090186510967474356357663)
      ·
        refine ⟨120135279766451211534536495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80090186510967474356357663 120135279766451211534536495)
        ·
          refine ⟨180202919649676817301804743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120135279766451211534536495 180202919649676817301804743)
          ·
            refine ⟨270304379474515225952707115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180202919649676817301804743 270304379474515225952707115)
            ·
              refine ⟨405456569211772838929060673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270304379474515225952707115 405456569211772838929060673)
              ·
                refine ⟨304092426908829629196795505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405456569211772838929060673 304092426908829629196795505)
                ·
                  refine ⟨228069320181622221897596629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304092426908829629196795505 228069320181622221897596629)
                  ·
                    refine ⟨5345374691756770825724921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 228069320181622221897596629 5345374691756770825724921)
                    ·
                      refine ⟨4009031018817578119293691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5345374691756770825724921 4009031018817578119293691)
                      ·
                        rfl

theorem cell23_7807560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_7807560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807560 prefixEnd_7807560 := by exact prefixLift 7807560
  have htrace : WordTrace (prefixWord ++ tailWord_7807560) baseStart_7807560 baseEnd_7807560 := by
    simpa [prefixWord, tailWord_7807560, baseEnd_7807560] using wordTrace_append hprefix tailTrace_7807560
  have hstable : (prefixWord ++ tailWord_7807560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807560).length < 2 ^ (prefixWord ++ tailWord_7807560).sum := by decide
  have hdescent : baseEnd_7807560 < baseStart_7807560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807563 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 5]
def baseStart_7807563 : Nat := 118140960795 + 7807563 * 2 ^ 59
def prefixEnd_7807563 : Nat := 4983230072969 + 3 ^ 40 * 7807563 * 2
def baseEnd_7807563 : Nat := 4009032559259541607556177

theorem tailTrace_7807563 : CollatzResearch.WordTrace tailWord_7807563 prefixEnd_7807563 4009032559259541607556177 := by
  unfold tailWord_7807563
  simp only [CollatzResearch.WordTrace]
  refine ⟨284765217013540151446075343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189843478009026767630716895 284765217013540151446075343)
  ·
    refine ⟨427147825520310227169113015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284765217013540151446075343 427147825520310227169113015)
    ·
      refine ⟨640721738280465340753669523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427147825520310227169113015 640721738280465340753669523)
      ·
        refine ⟨961082607420698011130504285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640721738280465340753669523 961082607420698011130504285)
        ·
          refine ⟨360405977782761754173939107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 961082607420698011130504285 360405977782761754173939107)
          ·
            refine ⟨540608966674142631260908661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360405977782761754173939107 540608966674142631260908661)
            ·
              refine ⟨50682090625700871680710187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 540608966674142631260908661 50682090625700871680710187)
              ·
                refine ⟨76023135938551307521065281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50682090625700871680710187 76023135938551307521065281)
                ·
                  refine ⟨57017351953913480640798961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76023135938551307521065281 57017351953913480640798961)
                  ·
                    refine ⟨42763013965435110480599221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57017351953913480640798961 42763013965435110480599221)
                    ·
                      refine ⟨4009032559259541607556177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42763013965435110480599221 4009032559259541607556177)
                      ·
                        rfl

theorem cell23_7807563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_7807563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807563 prefixEnd_7807563 := by exact prefixLift 7807563
  have htrace : WordTrace (prefixWord ++ tailWord_7807563) baseStart_7807563 baseEnd_7807563 := by
    simpa [prefixWord, tailWord_7807563, baseEnd_7807563] using wordTrace_append hprefix tailTrace_7807563
  have hstable : (prefixWord ++ tailWord_7807563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807563).length < 2 ^ (prefixWord ++ tailWord_7807563).sum := by decide
  have hdescent : baseEnd_7807563 < baseStart_7807563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807583 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 4, 6]
def baseStart_7807583 : Nat := 118140960795 + 7807583 * 2 ^ 59
def prefixEnd_7807583 : Nat := 4983230072969 + 3 ^ 40 * 7807583 * 2
def baseEnd_7807583 : Nat := 1336347609624210509768695

theorem tailTrace_7807583 : CollatzResearch.WordTrace tailWord_7807583 prefixEnd_7807583 1336347609624210509768695 := by
  unfold tailWord_7807583
  simp only [CollatzResearch.WordTrace]
  refine ⟨284765946473467694861803403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189843964315645129907868935 284765946473467694861803403)
  ·
    refine ⟨427148919710201542292705105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284765946473467694861803403 427148919710201542292705105)
    ·
      refine ⟨320361689782651156719528829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427148919710201542292705105 320361689782651156719528829)
      ·
        refine ⟨120135633668494183769823311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320361689782651156719528829 120135633668494183769823311)
        ·
          refine ⟨180203450502741275654734967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120135633668494183769823311 180203450502741275654734967)
          ·
            refine ⟨270305175754111913482102451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180203450502741275654734967 270305175754111913482102451)
            ·
              refine ⟨405457763631167870223153677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270305175754111913482102451 405457763631167870223153677)
              ·
                refine ⟨152046661361687951333682629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405457763631167870223153677 152046661361687951333682629)
                ·
                  refine ⟨28508749005316490875065493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152046661361687951333682629 28508749005316490875065493)
                  ·
                    refine ⟨1336347609624210509768695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28508749005316490875065493 1336347609624210509768695)
                    ·
                      rfl

theorem cell23_7807583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_7807583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807583 prefixEnd_7807583 := by exact prefixLift 7807583
  have htrace : WordTrace (prefixWord ++ tailWord_7807583) baseStart_7807583 baseEnd_7807583 := by
    simpa [prefixWord, tailWord_7807583, baseEnd_7807583] using wordTrace_append hprefix tailTrace_7807583
  have hstable : (prefixWord ++ tailWord_7807583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807583).length < 2 ^ (prefixWord ++ tailWord_7807583).sum := by decide
  have hdescent : baseEnd_7807583 < baseStart_7807583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807593 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_7807593 : Nat := 118140960795 + 7807593 * 2 ^ 59
def prefixEnd_7807593 : Nat := 4983230072969 + 3 ^ 40 * 7807593 * 2
def baseEnd_7807593 : Nat := 4009047963679176490181039

theorem tailTrace_7807593 : CollatzResearch.WordTrace tailWord_7807593 prefixEnd_7807593 4009047963679176490181039 := by
  unfold tailWord_7807593
  simp only [CollatzResearch.WordTrace]
  refine ⟨284766311203431466569667433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189844207468954311046444955 284766311203431466569667433)
  ·
    refine ⟨213574733402573599927250575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284766311203431466569667433 213574733402573599927250575)
    ·
      refine ⟨320362100103860399890875863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213574733402573599927250575 320362100103860399890875863)
      ·
        refine ⟨480543150155790599836313795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320362100103860399890875863 480543150155790599836313795)
        ·
          refine ⟨720814725233685899754470693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480543150155790599836313795 720814725233685899754470693)
          ·
            refine ⟨135152760981316106203963255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 720814725233685899754470693 135152760981316106203963255)
            ·
              refine ⟨202729141471974159305944883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135152760981316106203963255 202729141471974159305944883)
              ·
                refine ⟨304093712207961238958917325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202729141471974159305944883 304093712207961238958917325)
                ·
                  refine ⟨114035142077985464609593997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304093712207961238958917325 114035142077985464609593997)
                  ·
                    refine ⟨42763178279244549228597749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114035142077985464609593997 42763178279244549228597749)
                    ·
                      refine ⟨4009047963679176490181039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42763178279244549228597749 4009047963679176490181039)
                      ·
                        rfl

theorem cell23_7807593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_7807593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807593 prefixEnd_7807593 := by exact prefixLift 7807593
  have htrace : WordTrace (prefixWord ++ tailWord_7807593) baseStart_7807593 baseEnd_7807593 := by
    simpa [prefixWord, tailWord_7807593, baseEnd_7807593] using wordTrace_append hprefix tailTrace_7807593
  have hstable : (prefixWord ++ tailWord_7807593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807593).length < 2 ^ (prefixWord ++ tailWord_7807593).sum := by decide
  have hdescent : baseEnd_7807593 < baseStart_7807593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807618 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7807618 : Nat := 118140960795 + 7807618 * 2 ^ 59
def prefixEnd_7807618 : Nat := 4983230072969 + 3 ^ 40 * 7807618 * 2
def baseEnd_7807618 : Nat := 4009060800695538892368425

theorem tailTrace_7807618 : CollatzResearch.WordTrace tailWord_7807618 prefixEnd_7807618 4009060800695538892368425 := by
  unfold tailWord_7807618
  simp only [CollatzResearch.WordTrace]
  refine ⟨71191805757085223959831877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189844815352227263892885005 71191805757085223959831877)
  ·
    refine ⟨13348463579453479492468477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71191805757085223959831877 13348463579453479492468477)
    ·
      refine ⟨5005673842295054809675679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13348463579453479492468477 5005673842295054809675679)
      ·
        refine ⟨7508510763442582214513519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5005673842295054809675679 7508510763442582214513519)
        ·
          refine ⟨11262766145163873321770279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7508510763442582214513519 11262766145163873321770279)
          ·
            refine ⟨16894149217745809982655419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11262766145163873321770279 16894149217745809982655419)
            ·
              refine ⟨25341223826618714973983129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16894149217745809982655419 25341223826618714973983129)
              ·
                refine ⟨19005917869964036230487347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25341223826618714973983129 19005917869964036230487347)
                ·
                  refine ⟨28508876804946054345731021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19005917869964036230487347 28508876804946054345731021)
                  ·
                    refine ⟨10690828801854770379649133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28508876804946054345731021 10690828801854770379649133)
                    ·
                      refine ⟨4009060800695538892368425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10690828801854770379649133 4009060800695538892368425)
                      ·
                        rfl

theorem cell23_7807618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7807618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807618 prefixEnd_7807618 := by exact prefixLift 7807618
  have htrace : WordTrace (prefixWord ++ tailWord_7807618) baseStart_7807618 baseEnd_7807618 := by
    simpa [prefixWord, tailWord_7807618, baseEnd_7807618] using wordTrace_append hprefix tailTrace_7807618
  have hstable : (prefixWord ++ tailWord_7807618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807618).length < 2 ^ (prefixWord ++ tailWord_7807618).sum := by decide
  have hdescent : baseEnd_7807618 < baseStart_7807618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807633 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_7807633 : Nat := 118140960795 + 7807633 * 2 ^ 59
def prefixEnd_7807633 : Nat := 4983230072969 + 3 ^ 40 * 7807633 * 2
def baseEnd_7807633 : Nat := 4009068502905356333680855

theorem tailTrace_7807633 : CollatzResearch.WordTrace tailWord_7807633 prefixEnd_7807633 4009068502905356333680855 := by
  unfold tailWord_7807633
  simp only [CollatzResearch.WordTrace]
  refine ⟨284767770123286553401123553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189845180082191035600749035 284767770123286553401123553)
  ·
    refine ⟨213575827592464915050842665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284767770123286553401123553 213575827592464915050842665)
    ·
      refine ⟨160181870694348686288131999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213575827592464915050842665 160181870694348686288131999)
      ·
        refine ⟨240272806041523029432197999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160181870694348686288131999 240272806041523029432197999)
        ·
          refine ⟨360409209062284544148296999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240272806041523029432197999 360409209062284544148296999)
          ·
            refine ⟨540613813593426816222445499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360409209062284544148296999 540613813593426816222445499)
            ·
              refine ⟨810920720390140224333668249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540613813593426816222445499 810920720390140224333668249)
              ·
                refine ⟨608190540292605168250251187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810920720390140224333668249 608190540292605168250251187)
                ·
                  refine ⟨912285810438907752375376781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608190540292605168250251187 912285810438907752375376781)
                  ·
                    refine ⟨342107178914590407140766293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912285810438907752375376781 342107178914590407140766293)
                    ·
                      refine ⟨4009068502905356333680855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 342107178914590407140766293 4009068502905356333680855)
                      ·
                        rfl

theorem cell23_7807633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_7807633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807633 prefixEnd_7807633 := by exact prefixLift 7807633
  have htrace : WordTrace (prefixWord ++ tailWord_7807633) baseStart_7807633 baseEnd_7807633 := by
    simpa [prefixWord, tailWord_7807633, baseEnd_7807633] using wordTrace_append hprefix tailTrace_7807633
  have hstable : (prefixWord ++ tailWord_7807633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807633).length < 2 ^ (prefixWord ++ tailWord_7807633).sum := by decide
  have hdescent : baseEnd_7807633 < baseStart_7807633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807658 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7807658 : Nat := 118140960795 + 7807658 * 2 ^ 59
def prefixEnd_7807658 : Nat := 4983230072969 + 3 ^ 40 * 7807658 * 2
def baseEnd_7807658 : Nat := 4009081339921718735868241

theorem tailTrace_7807658 : CollatzResearch.WordTrace tailWord_7807658 prefixEnd_7807658 4009081339921718735868241 := by
  unfold tailWord_7807658
  simp only [CollatzResearch.WordTrace]
  refine ⟨71192170487048995667695907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189845787965463988447189085 71192170487048995667695907)
  ·
    refine ⟨106788255730573493501543861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71192170487048995667695907 106788255730573493501543861)
    ·
      refine ⟨10011398974741265015769737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106788255730573493501543861 10011398974741265015769737)
      ·
        refine ⟨7508549231055948761827303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10011398974741265015769737 7508549231055948761827303)
        ·
          refine ⟨11262823846583923142740955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7508549231055948761827303 11262823846583923142740955)
          ·
            refine ⟨16894235769875884714111433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11262823846583923142740955 16894235769875884714111433)
            ·
              refine ⟨12670676827406913535583575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16894235769875884714111433 12670676827406913535583575)
              ·
                refine ⟨19006015241110370303375363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12670676827406913535583575 19006015241110370303375363)
                ·
                  refine ⟨28509022861665555455063045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19006015241110370303375363 28509022861665555455063045)
                  ·
                    refine ⟨5345441786562291647824321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28509022861665555455063045 5345441786562291647824321)
                    ·
                      refine ⟨4009081339921718735868241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5345441786562291647824321 4009081339921718735868241)
                      ·
                        rfl

theorem cell23_7807658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7807658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807658 prefixEnd_7807658 := by exact prefixLift 7807658
  have htrace : WordTrace (prefixWord ++ tailWord_7807658) baseStart_7807658 baseEnd_7807658 := by
    simpa [prefixWord, tailWord_7807658, baseEnd_7807658] using wordTrace_append hprefix tailTrace_7807658
  have hstable : (prefixWord ++ tailWord_7807658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807658).length < 2 ^ (prefixWord ++ tailWord_7807658).sum := by decide
  have hdescent : baseEnd_7807658 < baseStart_7807658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807677 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_7807677 : Nat := 118140960795 + 7807677 * 2 ^ 59
def prefixEnd_7807677 : Nat := 4983230072969 + 3 ^ 40 * 7807677 * 2
def baseEnd_7807677 : Nat := 1336363698684718053843551

theorem tailTrace_7807677 : CollatzResearch.WordTrace tailWord_7807677 prefixEnd_7807677 1336363698684718053843551 := by
  unfold tailWord_7807677
  simp only [CollatzResearch.WordTrace]
  refine ⟨284769374935127148915725285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189846249956751432610483523 284769374935127148915725285)
  ·
    refine ⟨53394257800336340421698491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284769374935127148915725285 53394257800336340421698491)
    ·
      refine ⟨80091386700504510632547737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53394257800336340421698491 80091386700504510632547737)
      ·
        refine ⟨60068540025378382974410803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80091386700504510632547737 60068540025378382974410803)
        ·
          refine ⟨90102810038067574461616205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60068540025378382974410803 90102810038067574461616205)
          ·
            refine ⟨33788553764275340423106077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90102810038067574461616205 33788553764275340423106077)
            ·
              refine ⟨12670707661603252658664779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33788553764275340423106077 12670707661603252658664779)
              ·
                refine ⟨19006061492404878987997169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12670707661603252658664779 19006061492404878987997169)
                ·
                  refine ⟨14254546119303659240997877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19006061492404878987997169 14254546119303659240997877)
                  ·
                    refine ⟨1336363698684718053843551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14254546119303659240997877 1336363698684718053843551)
                    ·
                      rfl

theorem cell23_7807677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_7807677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807677 prefixEnd_7807677 := by exact prefixLift 7807677
  have htrace : WordTrace (prefixWord ++ tailWord_7807677) baseStart_7807677 baseEnd_7807677 := by
    simpa [prefixWord, tailWord_7807677, baseEnd_7807677] using wordTrace_append hprefix tailTrace_7807677
  have hstable : (prefixWord ++ tailWord_7807677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807677).length < 2 ^ (prefixWord ++ tailWord_7807677).sum := by decide
  have hdescent : baseEnd_7807677 < baseStart_7807677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807697 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 4, 4, 2]
def baseStart_7807697 : Nat := 118140960795 + 7807697 * 2 ^ 59
def prefixEnd_7807697 : Nat := 4983230072969 + 3 ^ 40 * 7807697 * 2
def baseEnd_7807697 : Nat := 4009101365667244083280561

theorem tailTrace_7807697 : CollatzResearch.WordTrace tailWord_7807697 prefixEnd_7807697 4009101365667244083280561 := by
  unfold tailWord_7807697
  simp only [CollatzResearch.WordTrace]
  refine ⟨284770104395054692331453345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189846736263369794887635563 284770104395054692331453345)
  ·
    refine ⟨213577578296291019248590009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284770104395054692331453345 213577578296291019248590009)
    ·
      refine ⟨160183183722218264436442507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213577578296291019248590009 160183183722218264436442507)
      ·
        refine ⟨240274775583327396654663761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160183183722218264436442507 240274775583327396654663761)
        ·
          refine ⟨180206081687495547490997821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240274775583327396654663761 180206081687495547490997821)
          ·
            refine ⟨67577280632810830309124183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180206081687495547490997821 67577280632810830309124183)
            ·
              refine ⟨101365920949216245463686275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67577280632810830309124183 101365920949216245463686275)
              ·
                refine ⟨152048881423824368195529413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101365920949216245463686275 152048881423824368195529413)
                ·
                  refine ⟨28509165266967069036661765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152048881423824368195529413 28509165266967069036661765)
                  ·
                    refine ⟨5345468487556325444374081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28509165266967069036661765 5345468487556325444374081)
                    ·
                      refine ⟨4009101365667244083280561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5345468487556325444374081 4009101365667244083280561)
                      ·
                        rfl

theorem cell23_7807697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_7807697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807697 prefixEnd_7807697 := by exact prefixLift 7807697
  have htrace : WordTrace (prefixWord ++ tailWord_7807697) baseStart_7807697 baseEnd_7807697 := by
    simpa [prefixWord, tailWord_7807697, baseEnd_7807697] using wordTrace_append hprefix tailTrace_7807697
  have hstable : (prefixWord ++ tailWord_7807697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807697).length < 2 ^ (prefixWord ++ tailWord_7807697).sum := by decide
  have hdescent : baseEnd_7807697 < baseStart_7807697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807717 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 1, 4, 3]
def baseStart_7807717 : Nat := 118140960795 + 7807717 * 2 ^ 59
def prefixEnd_7807717 : Nat := 4983230072969 + 3 ^ 40 * 7807717 * 2
def baseEnd_7807717 : Nat := 4009111635280334005030469

theorem tailTrace_7807717 : CollatzResearch.WordTrace tailWord_7807717 prefixEnd_7807717 4009111635280334005030469 := by
  unfold tailWord_7807717
  simp only [CollatzResearch.WordTrace]
  refine ⟨284770833854982235747181405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189847222569988157164787603 284770833854982235747181405)
  ·
    refine ⟨106789062695618338405193027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284770833854982235747181405 106789062695618338405193027)
    ·
      refine ⟨160183594043427507607789541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106789062695618338405193027 160183594043427507607789541)
      ·
        refine ⟨30034423883142657676460539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160183594043427507607789541 30034423883142657676460539)
        ·
          refine ⟨45051635824713986514690809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30034423883142657676460539 45051635824713986514690809)
          ·
            refine ⟨33788726868535489886018107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45051635824713986514690809 33788726868535489886018107)
            ·
              refine ⟨50683090302803234829027161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33788726868535489886018107 50683090302803234829027161)
              ·
                refine ⟨38012317727102426121770371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50683090302803234829027161 38012317727102426121770371)
                ·
                  refine ⟨57018476590653639182655557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38012317727102426121770371 57018476590653639182655557)
                  ·
                    refine ⟨10690964360747557346747917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57018476590653639182655557 10690964360747557346747917)
                    ·
                      refine ⟨4009111635280334005030469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10690964360747557346747917 4009111635280334005030469)
                      ·
                        rfl

theorem cell23_7807717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_7807717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807717 prefixEnd_7807717 := by exact prefixLift 7807717
  have htrace : WordTrace (prefixWord ++ tailWord_7807717) baseStart_7807717 baseEnd_7807717 := by
    simpa [prefixWord, tailWord_7807717, baseEnd_7807717] using wordTrace_append hprefix tailTrace_7807717
  have hstable : (prefixWord ++ tailWord_7807717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807717).length < 2 ^ (prefixWord ++ tailWord_7807717).sum := by decide
  have hdescent : baseEnd_7807717 < baseStart_7807717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807734 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_7807734 : Nat := 118140960795 + 7807734 * 2 ^ 59
def prefixEnd_7807734 : Nat := 4983230072969 + 3 ^ 40 * 7807734 * 2
def baseEnd_7807734 : Nat := 4009120364451460438517891

theorem tailTrace_7807734 : CollatzResearch.WordTrace tailWord_7807734 prefixEnd_7807734 4009120364451460438517891 := by
  unfold tailWord_7807734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17798215868495040478159391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189847635930613765100366837 17798215868495040478159391)
  ·
    refine ⟨26697323802742560717239087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17798215868495040478159391 26697323802742560717239087)
    ·
      refine ⟨40045985704113841075858631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26697323802742560717239087 40045985704113841075858631)
      ·
        refine ⟨60068978556170761613787947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40045985704113841075858631 60068978556170761613787947)
        ·
          refine ⟨90103467834256142420681921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60068978556170761613787947 90103467834256142420681921)
          ·
            refine ⟨67577600875692106815511441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90103467834256142420681921 67577600875692106815511441)
            ·
              refine ⟨50683200656769080111633581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67577600875692106815511441 50683200656769080111633581)
              ·
                refine ⟨19006200246288405041862593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50683200656769080111633581 19006200246288405041862593)
                ·
                  refine ⟨14254650184716303781396945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19006200246288405041862593 14254650184716303781396945)
                  ·
                    refine ⟨10690987638537227836047709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14254650184716303781396945 10690987638537227836047709)
                    ·
                      refine ⟨4009120364451460438517891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10690987638537227836047709 4009120364451460438517891)
                      ·
                        rfl

theorem cell23_7807734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_7807734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807734 prefixEnd_7807734 := by exact prefixLift 7807734
  have htrace : WordTrace (prefixWord ++ tailWord_7807734) baseStart_7807734 baseEnd_7807734 := by
    simpa [prefixWord, tailWord_7807734, baseEnd_7807734] using wordTrace_append hprefix tailTrace_7807734
  have hstable : (prefixWord ++ tailWord_7807734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807734).length < 2 ^ (prefixWord ++ tailWord_7807734).sum := by decide
  have hdescent : baseEnd_7807734 < baseStart_7807734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807787 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 1, 8, 2]
def baseStart_7807787 : Nat := 118140960795 + 7807787 * 2 ^ 59
def prefixEnd_7807787 : Nat := 4983230072969 + 3 ^ 40 * 7807787 * 2
def baseEnd_7807787 : Nat := 4009147578926148731155147

theorem tailTrace_7807787 : CollatzResearch.WordTrace tailWord_7807787 prefixEnd_7807787 4009147578926148731155147 := by
  unfold tailWord_7807787
  simp only [CollatzResearch.WordTrace]
  refine ⟨284773386964728637702229615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189848924643152425134819743 284773386964728637702229615)
  ·
    refine ⟨427160080447092956553344423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284773386964728637702229615 427160080447092956553344423)
    ·
      refine ⟨640740120670639434830016635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427160080447092956553344423 640740120670639434830016635)
      ·
        refine ⟨961110181005959152245024953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640740120670639434830016635 961110181005959152245024953)
        ·
          refine ⟨720832635754469364183768715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 961110181005959152245024953 720832635754469364183768715)
          ·
            refine ⟨1081248953631704046275653073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720832635754469364183768715 1081248953631704046275653073)
            ·
              refine ⟨810936715223778034706739805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081248953631704046275653073 810936715223778034706739805)
              ·
                refine ⟨304101268208916763015027427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 810936715223778034706739805 304101268208916763015027427)
                ·
                  refine ⟨456151902313375144522541141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304101268208916763015027427 456151902313375144522541141)
                  ·
                    refine ⟨5345530105234864974873529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 456151902313375144522541141 5345530105234864974873529)
                    ·
                      refine ⟨4009147578926148731155147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5345530105234864974873529 4009147578926148731155147)
                      ·
                        rfl

theorem cell23_7807787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 8, 2].length) (baseStart_7807787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807787 prefixEnd_7807787 := by exact prefixLift 7807787
  have htrace : WordTrace (prefixWord ++ tailWord_7807787) baseStart_7807787 baseEnd_7807787 := by
    simpa [prefixWord, tailWord_7807787, baseEnd_7807787] using wordTrace_append hprefix tailTrace_7807787
  have hstable : (prefixWord ++ tailWord_7807787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807787).length < 2 ^ (prefixWord ++ tailWord_7807787).sum := by decide
  have hdescent : baseEnd_7807787 < baseStart_7807787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807797 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_7807797 : Nat := 118140960795 + 7807797 * 2 ^ 59
def prefixEnd_7807797 : Nat := 4983230072969 + 3 ^ 40 * 7807797 * 2
def baseEnd_7807797 : Nat := 1336384237910897897343367

theorem tailTrace_7807797 : CollatzResearch.WordTrace tailWord_7807797 prefixEnd_7807797 1336384237910897897343367 := by
  unfold tailWord_7807797
  simp only [CollatzResearch.WordTrace]
  refine ⟨284773751694692409410093645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189849167796461606273395763 284773751694692409410093645)
  ·
    refine ⟨106790156885509653528785117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284773751694692409410093645 106790156885509653528785117)
    ·
      refine ⟨40046308832066120073294419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106790156885509653528785117 40046308832066120073294419)
      ·
        refine ⟨60069463248099180109941629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40046308832066120073294419 60069463248099180109941629)
        ·
          refine ⟨22526048718037192541228111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60069463248099180109941629 22526048718037192541228111)
          ·
            refine ⟨33789073077055788811842167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22526048718037192541228111 33789073077055788811842167)
            ·
              refine ⟨50683609615583683217763251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33789073077055788811842167 50683609615583683217763251)
              ·
                refine ⟨76025414423375524826644877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50683609615583683217763251 76025414423375524826644877)
                ·
                  refine ⟨28509530408765821809991829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76025414423375524826644877 28509530408765821809991829)
                  ·
                    refine ⟨1336384237910897897343367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28509530408765821809991829 1336384237910897897343367)
                    ·
                      rfl

theorem cell23_7807797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_7807797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807797 prefixEnd_7807797 := by exact prefixLift 7807797
  have htrace : WordTrace (prefixWord ++ tailWord_7807797) baseStart_7807797 baseEnd_7807797 := by
    simpa [prefixWord, tailWord_7807797, baseEnd_7807797] using wordTrace_append hprefix tailTrace_7807797
  have hstable : (prefixWord ++ tailWord_7807797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807797).length < 2 ^ (prefixWord ++ tailWord_7807797).sum := by decide
  have hdescent : baseEnd_7807797 < baseStart_7807797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807834 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4]
def baseStart_7807834 : Nat := 118140960795 + 7807834 * 2 ^ 59
def prefixEnd_7807834 : Nat := 4983230072969 + 3 ^ 40 * 7807834 * 2
def baseEnd_7807834 : Nat := 4009171712516910047267431

theorem tailTrace_7807834 : CollatzResearch.WordTrace tailWord_7807834 prefixEnd_7807834 4009171712516910047267431 := by
  unfold tailWord_7807834
  simp only [CollatzResearch.WordTrace]
  refine ⟨71193775298889591182297639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189850067463705576486127037 71193775298889591182297639)
  ·
    refine ⟨106790662948334386773446459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71193775298889591182297639 106790662948334386773446459)
    ·
      refine ⟨160185994422501580160169689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106790662948334386773446459 160185994422501580160169689)
      ·
        refine ⟨120139495816876185120127267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160185994422501580160169689 120139495816876185120127267)
        ·
          refine ⟨180209243725314277680190901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120139495816876185120127267 180209243725314277680190901)
          ·
            refine ⟨16894616599248213532517897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180209243725314277680190901 16894616599248213532517897)
            ·
              refine ⟨12670962449436160149388423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16894616599248213532517897 12670962449436160149388423)
              ·
                refine ⟨19006443674154240224082635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12670962449436160149388423 19006443674154240224082635)
                ·
                  refine ⟨28509665511231360336123953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19006443674154240224082635 28509665511231360336123953)
                  ·
                    refine ⟨21382249133423520252092965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28509665511231360336123953 21382249133423520252092965)
                    ·
                      refine ⟨4009171712516910047267431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21382249133423520252092965 4009171712516910047267431)
                      ·
                        rfl

theorem cell23_7807834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_7807834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807834 prefixEnd_7807834 := by exact prefixLift 7807834
  have htrace : WordTrace (prefixWord ++ tailWord_7807834) baseStart_7807834 baseEnd_7807834 := by
    simpa [prefixWord, tailWord_7807834, baseEnd_7807834] using wordTrace_append hprefix tailTrace_7807834
  have hstable : (prefixWord ++ tailWord_7807834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807834).length < 2 ^ (prefixWord ++ tailWord_7807834).sum := by decide
  have hdescent : baseEnd_7807834 < baseStart_7807834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807844 : List Nat := [2, 3, 1, 1, 4, 2, 3, 7]
def baseStart_7807844 : Nat := 118140960795 + 7807844 * 2 ^ 59
def prefixEnd_7807844 : Nat := 4983230072969 + 3 ^ 40 * 7807844 * 2
def baseEnd_7807844 : Nat := 148488031382350185486755

theorem tailTrace_7807844 : CollatzResearch.WordTrace tailWord_7807844 prefixEnd_7807844 148488031382350185486755 := by
  unfold tailWord_7807844
  simp only [CollatzResearch.WordTrace]
  refine ⟨142387732962761068218527293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189850310617014757624703057 142387732962761068218527293)
  ·
    refine ⟨53395399861035400581947735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142387732962761068218527293 53395399861035400581947735)
    ·
      refine ⟨80093099791553100872921603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53395399861035400581947735 80093099791553100872921603)
      ·
        refine ⟨120139649687329651309382405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80093099791553100872921603 120139649687329651309382405)
        ·
          refine ⟨22526184316374309620509201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120139649687329651309382405 22526184316374309620509201)
          ·
            refine ⟨16894638237280732215381901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22526184316374309620509201 16894638237280732215381901)
            ·
              refine ⟨6335489338980274580768213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16894638237280732215381901 6335489338980274580768213)
              ·
                refine ⟨148488031382350185486755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6335489338980274580768213 148488031382350185486755)
                ·
                  rfl

theorem cell23_7807844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 7].length) (baseStart_7807844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807844 prefixEnd_7807844 := by exact prefixLift 7807844
  have htrace : WordTrace (prefixWord ++ tailWord_7807844) baseStart_7807844 baseEnd_7807844 := by
    simpa [prefixWord, tailWord_7807844, baseEnd_7807844] using wordTrace_append hprefix tailTrace_7807844
  have hstable : (prefixWord ++ tailWord_7807844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807844).length < 2 ^ (prefixWord ++ tailWord_7807844).sum := by decide
  have hdescent : baseEnd_7807844 < baseStart_7807844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807864 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 5, 3, 2]
def baseStart_7807864 : Nat := 118140960795 + 7807864 * 2 ^ 59
def prefixEnd_7807864 : Nat := 4983230072969 + 3 ^ 40 * 7807864 * 2
def baseEnd_7807864 : Nat := 4009187116936544929892293

theorem tailTrace_7807864 : CollatzResearch.WordTrace tailWord_7807864 prefixEnd_7807864 4009187116936544929892293 := by
  unfold tailWord_7807864
  simp only [CollatzResearch.WordTrace]
  refine ⟨142388097692724839926391323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189850796923633119901855097 142388097692724839926391323)
  ·
    refine ⟨213582146539087259889586985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142388097692724839926391323 213582146539087259889586985)
    ·
      refine ⟨160186609904315444917190239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213582146539087259889586985 160186609904315444917190239)
      ·
        refine ⟨240279914856473167375785359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160186609904315444917190239 240279914856473167375785359)
        ·
          refine ⟨360419872284709751063678039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240279914856473167375785359 360419872284709751063678039)
          ·
            refine ⟨540629808427064626595517059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360419872284709751063678039 540629808427064626595517059)
            ·
              refine ⟨810944712640596939893275589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540629808427064626595517059 810944712640596939893275589)
              ·
                refine ⟨152052133620111926229989173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 810944712640596939893275589 152052133620111926229989173)
                ·
                  refine ⟨14254887526885493084061485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152052133620111926229989173 14254887526885493084061485)
                  ·
                    refine ⟨5345582822582059906523057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14254887526885493084061485 5345582822582059906523057)
                    ·
                      refine ⟨4009187116936544929892293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5345582822582059906523057 4009187116936544929892293)
                      ·
                        rfl

theorem cell23_7807864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_7807864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807864 prefixEnd_7807864 := by exact prefixLift 7807864
  have htrace : WordTrace (prefixWord ++ tailWord_7807864) baseStart_7807864 baseEnd_7807864 := by
    simpa [prefixWord, tailWord_7807864, baseEnd_7807864] using wordTrace_append hprefix tailTrace_7807864
  have hstable : (prefixWord ++ tailWord_7807864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807864).length < 2 ^ (prefixWord ++ tailWord_7807864).sum := by decide
  have hdescent : baseEnd_7807864 < baseStart_7807864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807871 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 2, 1, 3]
def baseStart_7807871 : Nat := 118140960795 + 7807871 * 2 ^ 59
def prefixEnd_7807871 : Nat := 4983230072969 + 3 ^ 40 * 7807871 * 2
def baseEnd_7807871 : Nat := 4009190711301126402504761

theorem tailTrace_7807871 : CollatzResearch.WordTrace tailWord_7807871 prefixEnd_7807871 4009190711301126402504761 := by
  unfold tailWord_7807871
  simp only [CollatzResearch.WordTrace]
  refine ⟨284776450696424320048287467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189850967130949546698858311 284776450696424320048287467)
  ·
    refine ⟨427164676044636480072431201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284776450696424320048287467 427164676044636480072431201)
    ·
      refine ⟨320373507033477360054323401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427164676044636480072431201 320373507033477360054323401)
      ·
        refine ⟨240280130275108020040742551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320373507033477360054323401 240280130275108020040742551)
        ·
          refine ⟨360420195412662030061113827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240280130275108020040742551 360420195412662030061113827)
          ·
            refine ⟨540630293118993045091670741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360420195412662030061113827 540630293118993045091670741)
            ·
              refine ⟨12671022494976399494336033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 540630293118993045091670741 12671022494976399494336033)
              ·
                refine ⟨9503266871232299620752025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12671022494976399494336033 9503266871232299620752025)
                ·
                  refine ⟨7127450153424224715564019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9503266871232299620752025 7127450153424224715564019)
                  ·
                    refine ⟨10691175230136337073346029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7127450153424224715564019 10691175230136337073346029)
                    ·
                      refine ⟨4009190711301126402504761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10691175230136337073346029 4009190711301126402504761)
                      ·
                        rfl

theorem cell23_7807871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_7807871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807871 prefixEnd_7807871 := by exact prefixLift 7807871
  have htrace : WordTrace (prefixWord ++ tailWord_7807871) baseStart_7807871 baseEnd_7807871 := by
    simpa [prefixWord, tailWord_7807871, baseEnd_7807871] using wordTrace_append hprefix tailTrace_7807871
  have hstable : (prefixWord ++ tailWord_7807871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807871).length < 2 ^ (prefixWord ++ tailWord_7807871).sum := by decide
  have hdescent : baseEnd_7807871 < baseStart_7807871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807897 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_7807897 : Nat := 118140960795 + 7807897 * 2 ^ 59
def prefixEnd_7807897 : Nat := 4983230072969 + 3 ^ 40 * 7807897 * 2
def baseEnd_7807897 : Nat := 4009204061798143300779641

theorem tailTrace_7807897 : CollatzResearch.WordTrace tailWord_7807897 prefixEnd_7807897 4009204061798143300779641 := by
  unfold tailWord_7807897
  simp only [CollatzResearch.WordTrace]
  refine ⟨284777398994330126488733945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189851599329553417659155963 284777398994330126488733945)
  ·
    refine ⟨213583049245747594866550459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284777398994330126488733945 213583049245747594866550459)
    ·
      refine ⟨320374573868621392299825689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213583049245747594866550459 320374573868621392299825689)
      ·
        refine ⟨240280930401466044224869267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320374573868621392299825689 240280930401466044224869267)
        ·
          refine ⟨360421395602199066337303901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240280930401466044224869267 360421395602199066337303901)
          ·
            refine ⟨135158023350824649876488963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360421395602199066337303901 135158023350824649876488963)
            ·
              refine ⟨202737035026236974814733445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135158023350824649876488963 202737035026236974814733445)
              ·
                refine ⟨38013194067419432777762521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202737035026236974814733445 38013194067419432777762521)
                ·
                  refine ⟨28509895550564574583321891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38013194067419432777762521 28509895550564574583321891)
                  ·
                    refine ⟨42764843325846861874982837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28509895550564574583321891 42764843325846861874982837)
                    ·
                      refine ⟨4009204061798143300779641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42764843325846861874982837 4009204061798143300779641)
                      ·
                        rfl

theorem cell23_7807897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_7807897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807897 prefixEnd_7807897 := by exact prefixLift 7807897
  have htrace : WordTrace (prefixWord ++ tailWord_7807897) baseStart_7807897 baseEnd_7807897 := by
    simpa [prefixWord, tailWord_7807897, baseEnd_7807897] using wordTrace_append hprefix tailTrace_7807897
  have hstable : (prefixWord ++ tailWord_7807897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807897).length < 2 ^ (prefixWord ++ tailWord_7807897).sum := by decide
  have hdescent : baseEnd_7807897 < baseStart_7807897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807907 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 4]
def baseStart_7807907 : Nat := 118140960795 + 7807907 * 2 ^ 59
def prefixEnd_7807907 : Nat := 4983230072969 + 3 ^ 40 * 7807907 * 2
def baseEnd_7807907 : Nat := 4009209196604688261654595

theorem tailTrace_7807907 : CollatzResearch.WordTrace tailWord_7807907 prefixEnd_7807907 4009209196604688261654595 := by
  unfold tailWord_7807907
  simp only [CollatzResearch.WordTrace]
  refine ⟨284777763724293898196597975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189851842482862598797731983 284777763724293898196597975)
  ·
    refine ⟨427166645586440847294896963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284777763724293898196597975 427166645586440847294896963)
    ·
      refine ⟨640749968379661270942345445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427166645586440847294896963 640749968379661270942345445)
      ·
        refine ⟨120140619071186488301689771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 640749968379661270942345445 120140619071186488301689771)
        ·
          refine ⟨180210928606779732452534657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120140619071186488301689771 180210928606779732452534657)
          ·
            refine ⟨135158196455084799339400993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180210928606779732452534657 135158196455084799339400993)
            ·
              refine ⟨101368647341313599504550745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135158196455084799339400993 101368647341313599504550745)
              ·
                refine ⟨76026485505985199628413059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101368647341313599504550745 76026485505985199628413059)
                ·
                  refine ⟨114039728258977799442619589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76026485505985199628413059 114039728258977799442619589)
                  ·
                    refine ⟨21382449048558337395491173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114039728258977799442619589 21382449048558337395491173)
                    ·
                      refine ⟨4009209196604688261654595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21382449048558337395491173 4009209196604688261654595)
                      ·
                        rfl

theorem cell23_7807907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_7807907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807907 prefixEnd_7807907 := by exact prefixLift 7807907
  have htrace : WordTrace (prefixWord ++ tailWord_7807907) baseStart_7807907 baseEnd_7807907 := by
    simpa [prefixWord, tailWord_7807907, baseEnd_7807907] using wordTrace_append hprefix tailTrace_7807907
  have hstable : (prefixWord ++ tailWord_7807907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807907).length < 2 ^ (prefixWord ++ tailWord_7807907).sum := by decide
  have hdescent : baseEnd_7807907 < baseStart_7807907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7807994 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_7807994 : Nat := 118140960795 + 7807994 * 2 ^ 59
def prefixEnd_7807994 : Nat := 4983230072969 + 3 ^ 40 * 7807994 * 2
def baseEnd_7807994 : Nat := 1336417956473876473755565

theorem tailTrace_7807994 : CollatzResearch.WordTrace tailWord_7807994 prefixEnd_7807994 1336417956473876473755565 := by
  unfold tailWord_7807994
  simp only [CollatzResearch.WordTrace]
  refine ⟨71195234218744678013753759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189853957916652474703343357 71195234218744678013753759)
  ·
    refine ⟨106792851328117017020630639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71195234218744678013753759 106792851328117017020630639)
    ·
      refine ⟨160189276992175525530945959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106792851328117017020630639 160189276992175525530945959)
      ·
        refine ⟨240283915488263288296418939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160189276992175525530945959 240283915488263288296418939)
        ·
          refine ⟨360425873232394932444628409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240283915488263288296418939 360425873232394932444628409)
          ·
            refine ⟨270319404924296199333471307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360425873232394932444628409 270319404924296199333471307)
            ·
              refine ⟨405479107386444299000206961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270319404924296199333471307 405479107386444299000206961)
              ·
                refine ⟨304109330539833224250155221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405479107386444299000206961 304109330539833224250155221)
                ·
                  refine ⟨7127562434527341193363013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 304109330539833224250155221 7127562434527341193363013)
                  ·
                    refine ⟨1336417956473876473755565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7127562434527341193363013 1336417956473876473755565)
                    ·
                      rfl

theorem cell23_7807994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_7807994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7807994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7807994 prefixEnd_7807994 := by exact prefixLift 7807994
  have htrace : WordTrace (prefixWord ++ tailWord_7807994) baseStart_7807994 baseEnd_7807994 := by
    simpa [prefixWord, tailWord_7807994, baseEnd_7807994] using wordTrace_append hprefix tailTrace_7807994
  have hstable : (prefixWord ++ tailWord_7807994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7807994).length < 2 ^ (prefixWord ++ tailWord_7807994).sum := by decide
  have hdescent : baseEnd_7807994 < baseStart_7807994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7807994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808001 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_7808001 : Nat := 118140960795 + 7808001 * 2 ^ 59
def prefixEnd_7808001 : Nat := 4983230072969 + 3 ^ 40 * 7808001 * 2
def baseEnd_7808001 : Nat := 4009257463786210893879163

theorem tailTrace_7808001 : CollatzResearch.WordTrace tailWord_7808001 prefixEnd_7808001 4009257463786210893879163 := by
  unfold tailWord_7808001
  simp only [CollatzResearch.WordTrace]
  refine ⟨284781192185953352250519857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189854128123968901500346571 284781192185953352250519857)
  ·
    refine ⟨213585894139465014187889893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284781192185953352250519857 213585894139465014187889893)
    ·
      refine ⟨40047355151149690160229355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213585894139465014187889893 40047355151149690160229355)
      ·
        refine ⟨60071032726724535240344033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40047355151149690160229355 60071032726724535240344033)
        ·
          refine ⟨45053274545043401430258025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60071032726724535240344033 45053274545043401430258025)
          ·
            refine ⟨33789955908782551072693519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45053274545043401430258025 33789955908782551072693519)
            ·
              refine ⟨50684933863173826609040279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33789955908782551072693519 50684933863173826609040279)
              ·
                refine ⟨76027400794760739913560419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50684933863173826609040279 76027400794760739913560419)
                ·
                  refine ⟨114041101192141109870340629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76027400794760739913560419 114041101192141109870340629)
                  ·
                    refine ⟨5345676618381614525172217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114041101192141109870340629 5345676618381614525172217)
                    ·
                      refine ⟨4009257463786210893879163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5345676618381614525172217 4009257463786210893879163)
                      ·
                        rfl

theorem cell23_7808001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_7808001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808001 prefixEnd_7808001 := by exact prefixLift 7808001
  have htrace : WordTrace (prefixWord ++ tailWord_7808001) baseStart_7808001 baseEnd_7808001 := by
    simpa [prefixWord, tailWord_7808001, baseEnd_7808001] using wordTrace_append hprefix tailTrace_7808001
  have hstable : (prefixWord ++ tailWord_7808001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808001).length < 2 ^ (prefixWord ++ tailWord_7808001).sum := by decide
  have hdescent : baseEnd_7808001 < baseStart_7808001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808011 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 3, 4]
def baseStart_7808011 : Nat := 118140960795 + 7808011 * 2 ^ 59
def prefixEnd_7808011 : Nat := 4983230072969 + 3 ^ 40 * 7808011 * 2
def baseEnd_7808011 : Nat := 1336420866197585284918039

theorem tailTrace_7808011 : CollatzResearch.WordTrace tailWord_7808011 prefixEnd_7808011 1336420866197585284918039 := by
  unfold tailWord_7808011
  simp only [CollatzResearch.WordTrace]
  refine ⟨284781556915917123958383887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189854371277278082638922591 284781556915917123958383887)
  ·
    refine ⟨427172335373875685937575831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284781556915917123958383887 427172335373875685937575831)
    ·
      refine ⟨640758503060813528906363747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427172335373875685937575831 640758503060813528906363747)
      ·
        refine ⟨961137754591220293359545621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640758503060813528906363747 961137754591220293359545621)
        ·
          refine ⟨45053332246463451251228701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 961137754591220293359545621 45053332246463451251228701)
          ·
            refine ⟨16894999592423794219210763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45053332246463451251228701 16894999592423794219210763)
            ·
              refine ⟨25342499388635691328816145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16894999592423794219210763 25342499388635691328816145)
              ·
                refine ⟨19006874541476768496612109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25342499388635691328816145 19006874541476768496612109)
                ·
                  refine ⟨7127577953053788186229541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19006874541476768496612109 7127577953053788186229541)
                  ·
                    refine ⟨1336420866197585284918039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7127577953053788186229541 1336420866197585284918039)
                    ·
                      rfl

theorem cell23_7808011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 4].length) (baseStart_7808011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808011 prefixEnd_7808011 := by exact prefixLift 7808011
  have htrace : WordTrace (prefixWord ++ tailWord_7808011) baseStart_7808011 baseEnd_7808011 := by
    simpa [prefixWord, tailWord_7808011, baseEnd_7808011] using wordTrace_append hprefix tailTrace_7808011
  have hstable : (prefixWord ++ tailWord_7808011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808011).length < 2 ^ (prefixWord ++ tailWord_7808011).sum := by decide
  have hdescent : baseEnd_7808011 < baseStart_7808011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808021 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_7808021 : Nat := 118140960795 + 7808021 * 2 ^ 59
def prefixEnd_7808021 : Nat := 4983230072969 + 3 ^ 40 * 7808021 * 2
def baseEnd_7808021 : Nat := 4009267733399300815629071

theorem tailTrace_7808021 : CollatzResearch.WordTrace tailWord_7808021 prefixEnd_7808021 4009267733399300815629071 := by
  unfold tailWord_7808021
  simp only [CollatzResearch.WordTrace]
  refine ⟨284781921645880895666247917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189854614430587263777498611 284781921645880895666247917)
  ·
    refine ⟨106793220617205335874842969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284781921645880895666247917 106793220617205335874842969)
    ·
      refine ⟨80094915462904001906132227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106793220617205335874842969 80094915462904001906132227)
      ·
        refine ⟨120142373194356002859198341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80094915462904001906132227 120142373194356002859198341)
        ·
          refine ⟨22526694973941750536099689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120142373194356002859198341 22526694973941750536099689)
          ·
            refine ⟨16895021230456312902074767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22526694973941750536099689 16895021230456312902074767)
            ·
              refine ⟨25342531845684469353112151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16895021230456312902074767 25342531845684469353112151)
              ·
                refine ⟨38013797768526704029668227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25342531845684469353112151 38013797768526704029668227)
                ·
                  refine ⟨57020696652790056044502341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38013797768526704029668227 57020696652790056044502341)
                  ·
                    refine ⟨10691380622398135508344189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57020696652790056044502341 10691380622398135508344189)
                    ·
                      refine ⟨4009267733399300815629071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10691380622398135508344189 4009267733399300815629071)
                      ·
                        rfl

theorem cell23_7808021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_7808021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808021 prefixEnd_7808021 := by exact prefixLift 7808021
  have htrace : WordTrace (prefixWord ++ tailWord_7808021) baseStart_7808021 baseEnd_7808021 := by
    simpa [prefixWord, tailWord_7808021, baseEnd_7808021] using wordTrace_append hprefix tailTrace_7808021
  have hstable : (prefixWord ++ tailWord_7808021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808021).length < 2 ^ (prefixWord ++ tailWord_7808021).sum := by decide
  have hdescent : baseEnd_7808021 < baseStart_7808021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808071 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 1, 5]
def baseStart_7808071 : Nat := 118140960795 + 7808071 * 2 ^ 59
def prefixEnd_7808071 : Nat := 4983230072969 + 3 ^ 40 * 7808071 * 2
def baseEnd_7808071 : Nat := 1336431135810675206667947

theorem tailTrace_7808071 : CollatzResearch.WordTrace tailWord_7808071 prefixEnd_7808071 1336431135810675206667947 := by
  unfold tailWord_7808071
  simp only [CollatzResearch.WordTrace]
  refine ⟨284783745295699754205568067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189855830197133169470378711 284783745295699754205568067)
  ·
    refine ⟨427175617943549631308352101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284783745295699754205568067 427175617943549631308352101)
    ·
      refine ⟨80095428364415555870316019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427175617943549631308352101 80095428364415555870316019)
      ·
        refine ⟨120143142546623333805474029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80095428364415555870316019 120143142546623333805474029)
        ·
          refine ⟨45053678454983750177052761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120143142546623333805474029 45053678454983750177052761)
          ·
            refine ⟨33790258841237812632789571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45053678454983750177052761 33790258841237812632789571)
            ·
              refine ⟨50685388261856718949184357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33790258841237812632789571 50685388261856718949184357)
              ·
                refine ⟨9503510299098134802972067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50685388261856718949184357 9503510299098134802972067)
                ·
                  refine ⟨14255265448647202204458101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9503510299098134802972067 14255265448647202204458101)
                  ·
                    refine ⟨1336431135810675206667947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14255265448647202204458101 1336431135810675206667947)
                    ·
                      rfl

theorem cell23_7808071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_7808071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808071 prefixEnd_7808071 := by exact prefixLift 7808071
  have htrace : WordTrace (prefixWord ++ tailWord_7808071) baseStart_7808071 baseEnd_7808071 := by
    simpa [prefixWord, tailWord_7808071, baseEnd_7808071] using wordTrace_append hprefix tailTrace_7808071
  have hstable : (prefixWord ++ tailWord_7808071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808071).length < 2 ^ (prefixWord ++ tailWord_7808071).sum := by decide
  have hdescent : baseEnd_7808071 < baseStart_7808071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808078 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2]
def baseStart_7808078 : Nat := 118140960795 + 7808078 * 2 ^ 59
def prefixEnd_7808078 : Nat := 4983230072969 + 3 ^ 40 * 7808078 * 2
def baseEnd_7808078 : Nat := 4009297001796607092616309

theorem tailTrace_7808078 : CollatzResearch.WordTrace tailWord_7808078 prefixEnd_7808078 4009297001796607092616309 := by
  unfold tailWord_7808078
  simp only [CollatzResearch.WordTrace]
  refine ⟨35598000075834299300134111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189856000404449596267381925 35598000075834299300134111)
  ·
    refine ⟨53397000113751448950201167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35598000075834299300134111 53397000113751448950201167)
    ·
      refine ⟨80095500170627173425301751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53397000113751448950201167 80095500170627173425301751)
      ·
        refine ⟨120143250255940760137952627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80095500170627173425301751 120143250255940760137952627)
        ·
          refine ⟨180214875383911140206928941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120143250255940760137952627 180214875383911140206928941)
          ·
            refine ⟨67580578268966677577598353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180214875383911140206928941 67580578268966677577598353)
            ·
              refine ⟨50685433701725008183198765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67580578268966677577598353 50685433701725008183198765)
              ·
                refine ⟨19007037638146878068699537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50685433701725008183198765 19007037638146878068699537)
                ·
                  refine ⟨14255278228610158551524653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19007037638146878068699537 14255278228610158551524653)
                  ·
                    refine ⟨5345729335728809456821745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14255278228610158551524653 5345729335728809456821745)
                    ·
                      refine ⟨4009297001796607092616309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5345729335728809456821745 4009297001796607092616309)
                      ·
                        rfl

theorem cell23_7808078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_7808078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808078 prefixEnd_7808078 := by exact prefixLift 7808078
  have htrace : WordTrace (prefixWord ++ tailWord_7808078) baseStart_7808078 baseEnd_7808078 := by
    simpa [prefixWord, tailWord_7808078, baseEnd_7808078] using wordTrace_append hprefix tailTrace_7808078
  have hstable : (prefixWord ++ tailWord_7808078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808078).length < 2 ^ (prefixWord ++ tailWord_7808078).sum := by decide
  have hdescent : baseEnd_7808078 < baseStart_7808078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808101 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_7808101 : Nat := 118140960795 + 7808101 * 2 ^ 59
def prefixEnd_7808101 : Nat := 4983230072969 + 3 ^ 40 * 7808101 * 2
def baseEnd_7808101 : Nat := 1336436270617220167542901

theorem tailTrace_7808101 : CollatzResearch.WordTrace tailWord_7808101 prefixEnd_7808101 1336436270617220167542901 := by
  unfold tailWord_7808101
  simp only [CollatzResearch.WordTrace]
  refine ⟨284784839485591069329160157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189856559657060712886106771 284784839485591069329160157)
  ·
    refine ⟨106794314807096650998435059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284784839485591069329160157 106794314807096650998435059)
    ·
      refine ⟨160191472210644976497652589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106794314807096650998435059 160191472210644976497652589)
      ·
        refine ⟨60071802078991866186619721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160191472210644976497652589 60071802078991866186619721)
        ·
          refine ⟨45053851559243899639964791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60071802078991866186619721 45053851559243899639964791)
          ·
            refine ⟨67580777338865849459947187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45053851559243899639964791 67580777338865849459947187)
            ·
              refine ⟨101371166008298774189920781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67580777338865849459947187 101371166008298774189920781)
              ·
                refine ⟨38014187253112040321220293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101371166008298774189920781 38014187253112040321220293)
                ·
                  refine ⟨7127660109958507560228805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38014187253112040321220293 7127660109958507560228805)
                  ·
                    refine ⟨1336436270617220167542901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7127660109958507560228805 1336436270617220167542901)
                    ·
                      rfl

theorem cell23_7808101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_7808101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808101 prefixEnd_7808101 := by exact prefixLift 7808101
  have htrace : WordTrace (prefixWord ++ tailWord_7808101) baseStart_7808101 baseEnd_7808101 := by
    simpa [prefixWord, tailWord_7808101, baseEnd_7808101] using wordTrace_append hprefix tailTrace_7808101
  have hstable : (prefixWord ++ tailWord_7808101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808101).length < 2 ^ (prefixWord ++ tailWord_7808101).sum := by decide
  have hdescent : baseEnd_7808101 < baseStart_7808101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808111 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 3]
def baseStart_7808111 : Nat := 118140960795 + 7808111 * 2 ^ 59
def prefixEnd_7808111 : Nat := 4983230072969 + 3 ^ 40 * 7808111 * 2
def baseEnd_7808111 : Nat := 4009313946658205463503657

theorem tailTrace_7808111 : CollatzResearch.WordTrace tailWord_7808111 prefixEnd_7808111 4009313946658205463503657 := by
  unfold tailWord_7808111
  simp only [CollatzResearch.WordTrace]
  refine ⟨284785204215554841037024187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189856802810369894024682791 284785204215554841037024187)
  ·
    refine ⟨427177806323332261555536281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284785204215554841037024187 427177806323332261555536281)
    ·
      refine ⟨320383354742499196166652211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427177806323332261555536281 320383354742499196166652211)
      ·
        refine ⟨480575032113748794249978317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320383354742499196166652211 480575032113748794249978317)
        ·
          refine ⟨180215637042655797843741869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480575032113748794249978317 180215637042655797843741869)
          ·
            refine ⟨67580863890995924191403201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180215637042655797843741869 67580863890995924191403201)
            ·
              refine ⟨50685647918246943143552401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67580863890995924191403201 50685647918246943143552401)
              ·
                refine ⟨38014235938685207357664301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50685647918246943143552401 38014235938685207357664301)
                ·
                  refine ⟨14255338477006952759124113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38014235938685207357664301 14255338477006952759124113)
                  ·
                    refine ⟨10691503857755214569343085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14255338477006952759124113 10691503857755214569343085)
                    ·
                      refine ⟨4009313946658205463503657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10691503857755214569343085 4009313946658205463503657)
                      ·
                        rfl

theorem cell23_7808111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 3].length) (baseStart_7808111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808111 prefixEnd_7808111 := by exact prefixLift 7808111
  have htrace : WordTrace (prefixWord ++ tailWord_7808111) baseStart_7808111 baseEnd_7808111 := by
    simpa [prefixWord, tailWord_7808111, baseEnd_7808111] using wordTrace_append hprefix tailTrace_7808111
  have hstable : (prefixWord ++ tailWord_7808111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808111).length < 2 ^ (prefixWord ++ tailWord_7808111).sum := by decide
  have hdescent : baseEnd_7808111 < baseStart_7808111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808128 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 3]
def baseStart_7808128 : Nat := 118140960795 + 7808128 * 2 ^ 59
def prefixEnd_7808128 : Nat := 4983230072969 + 3 ^ 40 * 7808128 * 2
def baseEnd_7808128 : Nat := 4009322675829331896991079

theorem tailTrace_7808128 : CollatzResearch.WordTrace tailWord_7808128 prefixEnd_7808128 4009322675829331896991079 := by
  unfold tailWord_7808128
  simp only [CollatzResearch.WordTrace]
  refine ⟨142392912128246626470196519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189857216170995501960262025 142392912128246626470196519)
  ·
    refine ⟨213589368192369939705294779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142392912128246626470196519 213589368192369939705294779)
    ·
      refine ⟨320384052288554909557942169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213589368192369939705294779 320384052288554909557942169)
      ·
        refine ⟨240288039216416182168456627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320384052288554909557942169 240288039216416182168456627)
        ·
          refine ⟨360432058824624273252684941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240288039216416182168456627 360432058824624273252684941)
          ·
            refine ⟨135162022059234102469756853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360432058824624273252684941 135162022059234102469756853)
            ·
              refine ⟨12671439568053197106539705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135162022059234102469756853 12671439568053197106539705)
              ·
                refine ⟨9503579676039897829904779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12671439568053197106539705 9503579676039897829904779)
                ·
                  refine ⟨14255369514059846744857169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9503579676039897829904779 14255369514059846744857169)
                  ·
                    refine ⟨10691527135544885058642877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14255369514059846744857169 10691527135544885058642877)
                    ·
                      refine ⟨4009322675829331896991079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10691527135544885058642877 4009322675829331896991079)
                      ·
                        rfl

theorem cell23_7808128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_7808128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808128 prefixEnd_7808128 := by exact prefixLift 7808128
  have htrace : WordTrace (prefixWord ++ tailWord_7808128) baseStart_7808128 baseEnd_7808128 := by
    simpa [prefixWord, tailWord_7808128, baseEnd_7808128] using wordTrace_append hprefix tailTrace_7808128
  have hstable : (prefixWord ++ tailWord_7808128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808128).length < 2 ^ (prefixWord ++ tailWord_7808128).sum := by decide
  have hdescent : baseEnd_7808128 < baseStart_7808128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808159 : List Nat := [1, 1, 2, 6, 2, 1, 1, 4, 1, 2, 2]
def baseStart_7808159 : Nat := 118140960795 + 7808159 * 2 ^ 59
def prefixEnd_7808159 : Nat := 4983230072969 + 3 ^ 40 * 7808159 * 2
def baseEnd_7808159 : Nat := 4009338593729621275703437

theorem tailTrace_7808159 : CollatzResearch.WordTrace tailWord_7808159 prefixEnd_7808159 4009338593729621275703437 := by
  unfold tailWord_7808159
  simp only [CollatzResearch.WordTrace]
  refine ⟨284786954919380945234771531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189857969946253963489847687 284786954919380945234771531)
  ·
    refine ⟨427180432379071417852157297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284786954919380945234771531 427180432379071417852157297)
    ·
      refine ⟨320385324284303563389117973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427180432379071417852157297 320385324284303563389117973)
      ·
        refine ⟨15018062075826729533864905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 320385324284303563389117973 15018062075826729533864905)
        ·
          refine ⟨11263546556870047150398679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15018062075826729533864905 11263546556870047150398679)
          ·
            refine ⟨16895319835305070725598019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11263546556870047150398679 16895319835305070725598019)
            ·
              refine ⟨25342979752957606088397029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16895319835305070725598019 25342979752957606088397029)
              ·
                refine ⟨4751808703679551141574443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25342979752957606088397029 4751808703679551141574443)
                ·
                  refine ⟨7127713055519326712361665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4751808703679551141574443 7127713055519326712361665)
                  ·
                    refine ⟨5345784791639495034271249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7127713055519326712361665 5345784791639495034271249)
                    ·
                      refine ⟨4009338593729621275703437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5345784791639495034271249 4009338593729621275703437)
                      ·
                        rfl

theorem cell23_7808159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_7808159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808159 prefixEnd_7808159 := by exact prefixLift 7808159
  have htrace : WordTrace (prefixWord ++ tailWord_7808159) baseStart_7808159 baseEnd_7808159 := by
    simpa [prefixWord, tailWord_7808159, baseEnd_7808159] using wordTrace_append hprefix tailTrace_7808159
  have hstable : (prefixWord ++ tailWord_7808159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808159).length < 2 ^ (prefixWord ++ tailWord_7808159).sum := by decide
  have hdescent : baseEnd_7808159 < baseStart_7808159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808182 : List Nat := [5, 1, 3, 2, 1, 1, 3, 7]
def baseStart_7808182 : Nat := 118140960795 + 7808182 * 2 ^ 59
def prefixEnd_7808182 : Nat := 4983230072969 + 3 ^ 40 * 7808182 * 2
def baseEnd_7808182 : Nat := 148494459399432395767253

theorem tailTrace_7808182 : CollatzResearch.WordTrace tailWord_7808182 prefixEnd_7808182 148494459399432395767253 := by
  unfold tailWord_7808182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17799237112393601260178675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189858529198865080108572533 17799237112393601260178675)
  ·
    refine ⟨26698855668590401890268013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17799237112393601260178675 26698855668590401890268013)
    ·
      refine ⟨10012070875721400708850505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26698855668590401890268013 10012070875721400708850505)
      ·
        refine ⟨7509053156791050531637879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10012070875721400708850505 7509053156791050531637879)
        ·
          refine ⟨11263579735186575797456819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7509053156791050531637879 11263579735186575797456819)
          ·
            refine ⟨16895369602779863696185229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11263579735186575797456819 16895369602779863696185229)
            ·
              refine ⟨6335763601042448886069461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16895369602779863696185229 6335763601042448886069461)
              ·
                refine ⟨148494459399432395767253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6335763601042448886069461 148494459399432395767253)
                ·
                  rfl

theorem cell23_7808182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_7808182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808182 prefixEnd_7808182 := by exact prefixLift 7808182
  have htrace : WordTrace (prefixWord ++ tailWord_7808182) baseStart_7808182 baseEnd_7808182 := by
    simpa [prefixWord, tailWord_7808182, baseEnd_7808182] using wordTrace_append hprefix tailTrace_7808182
  have hstable : (prefixWord ++ tailWord_7808182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808182).length < 2 ^ (prefixWord ++ tailWord_7808182).sum := by decide
  have hdescent : baseEnd_7808182 < baseStart_7808182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808202 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2]
def baseStart_7808202 : Nat := 118140960795 + 7808202 * 2 ^ 59
def prefixEnd_7808202 : Nat := 4983230072969 + 3 ^ 40 * 7808202 * 2
def baseEnd_7808202 : Nat := 4009360673397764607465739

theorem tailTrace_7808202 : CollatzResearch.WordTrace tailWord_7808202 prefixEnd_7808202 4009360673397764607465739 := by
  unfold tailWord_7808202
  simp only [CollatzResearch.WordTrace]
  refine ⟨71197130814556290894646715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189859015505483442385724573 71197130814556290894646715)
  ·
    refine ⟨106795696221834436341970073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71197130814556290894646715 106795696221834436341970073)
    ·
      refine ⟨80096772166375827256477555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106795696221834436341970073 80096772166375827256477555)
      ·
        refine ⟨120145158249563740884716333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80096772166375827256477555 120145158249563740884716333)
        ·
          refine ⟨45054434343586402831768625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120145158249563740884716333 45054434343586402831768625)
          ·
            refine ⟨33790825757689802123826469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45054434343586402831768625 33790825757689802123826469)
            ·
              refine ⟨6335779829566837898217463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33790825757689802123826469 6335779829566837898217463)
              ·
                refine ⟨9503669744350256847326195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6335779829566837898217463 9503669744350256847326195)
                ·
                  refine ⟨14255504616525385270989293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9503669744350256847326195 14255504616525385270989293)
                  ·
                    refine ⟨5345814231197019476620985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14255504616525385270989293 5345814231197019476620985)
                    ·
                      refine ⟨4009360673397764607465739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5345814231197019476620985 4009360673397764607465739)
                      ·
                        rfl

theorem cell23_7808202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_7808202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808202 prefixEnd_7808202 := by exact prefixLift 7808202
  have htrace : WordTrace (prefixWord ++ tailWord_7808202) baseStart_7808202 baseEnd_7808202 := by
    simpa [prefixWord, tailWord_7808202, baseEnd_7808202] using wordTrace_append hprefix tailTrace_7808202
  have hstable : (prefixWord ++ tailWord_7808202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808202).length < 2 ^ (prefixWord ++ tailWord_7808202).sum := by decide
  have hdescent : baseEnd_7808202 < baseStart_7808202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808255 : List Nat := [1, 1, 2, 2, 1, 7, 1, 3, 5]
def baseStart_7808255 : Nat := 118140960795 + 7808255 * 2 ^ 59
def prefixEnd_7808255 : Nat := 4983230072969 + 3 ^ 40 * 7808255 * 2
def baseEnd_7808255 : Nat := 445487543096939211122555

theorem tailTrace_7808255 : CollatzResearch.WordTrace tailWord_7808255 prefixEnd_7808255 445487543096939211122555 := by
  unfold tailWord_7808255
  simp only [CollatzResearch.WordTrace]
  refine ⟨284790456327033153630266219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189860304218022102420177479 284790456327033153630266219)
  ·
    refine ⟨427185684490549730445399329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284790456327033153630266219 427185684490549730445399329)
    ·
      refine ⟨320389263367912297834049497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427185684490549730445399329 320389263367912297834049497)
      ·
        refine ⟨240291947525934223375537123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320389263367912297834049497 240291947525934223375537123)
        ·
          refine ⟨360437921288901335063305685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240291947525934223375537123 360437921288901335063305685)
          ·
            refine ⟨8447763780208625040546227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 360437921288901335063305685 8447763780208625040546227)
            ·
              refine ⟨12671645670312937560819341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8447763780208625040546227 12671645670312937560819341)
              ·
                refine ⟨4751867126367351585307253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12671645670312937560819341 4751867126367351585307253)
                ·
                  refine ⟨445487543096939211122555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4751867126367351585307253 445487543096939211122555)
                  ·
                    rfl

theorem cell23_7808255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 5].length) (baseStart_7808255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808255 prefixEnd_7808255 := by exact prefixLift 7808255
  have htrace : WordTrace (prefixWord ++ tailWord_7808255) baseStart_7808255 baseEnd_7808255 := by
    simpa [prefixWord, tailWord_7808255, baseEnd_7808255] using wordTrace_append hprefix tailTrace_7808255
  have hstable : (prefixWord ++ tailWord_7808255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808255).length < 2 ^ (prefixWord ++ tailWord_7808255).sum := by decide
  have hdescent : baseEnd_7808255 < baseStart_7808255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808261 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_7808261 : Nat := 118140960795 + 7808261 * 2 ^ 59
def prefixEnd_7808261 : Nat := 4983230072969 + 3 ^ 40 * 7808261 * 2
def baseEnd_7808261 : Nat := 4009390968756379876627967

theorem tailTrace_7808261 : CollatzResearch.WordTrace tailWord_7808261 prefixEnd_7808261 4009390968756379876627967 := by
  unfold tailWord_7808261
  simp only [CollatzResearch.WordTrace]
  refine ⟨284790675165011416654984637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189860450110007611103323091 284790675165011416654984637)
  ·
    refine ⟨106796503186879281245619239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284790675165011416654984637 106796503186879281245619239)
    ·
      refine ⟨160194754780318921868428859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106796503186879281245619239 160194754780318921868428859)
      ·
        refine ⟨240292132170478382802643289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160194754780318921868428859 240292132170478382802643289)
        ·
          refine ⟨180219099127858787101982467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240292132170478382802643289 180219099127858787101982467)
          ·
            refine ⟨270328648691788180652973701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180219099127858787101982467 270328648691788180652973701)
            ·
              refine ⟨50686621629710283872432569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270328648691788180652973701 50686621629710283872432569)
              ·
                refine ⟨38014966222282712904324427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50686621629710283872432569 38014966222282712904324427)
                ·
                  refine ⟨57022449333424069356486641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38014966222282712904324427 57022449333424069356486641)
                  ·
                    refine ⟨42766837000068052017364981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57022449333424069356486641 42766837000068052017364981)
                    ·
                      refine ⟨4009390968756379876627967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42766837000068052017364981 4009390968756379876627967)
                      ·
                        rfl

theorem cell23_7808261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_7808261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808261 prefixEnd_7808261 := by exact prefixLift 7808261
  have htrace : WordTrace (prefixWord ++ tailWord_7808261) baseStart_7808261 baseEnd_7808261 := by
    simpa [prefixWord, tailWord_7808261, baseEnd_7808261] using wordTrace_append hprefix tailTrace_7808261
  have hstable : (prefixWord ++ tailWord_7808261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808261).length < 2 ^ (prefixWord ++ tailWord_7808261).sum := by decide
  have hdescent : baseEnd_7808261 < baseStart_7808261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808268 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_7808268 : Nat := 118140960795 + 7808268 * 2 ^ 59
def prefixEnd_7808268 : Nat := 4983230072969 + 3 ^ 40 * 7808268 * 2
def baseEnd_7808268 : Nat := 1336464854373653783080145

theorem tailTrace_7808268 : CollatzResearch.WordTrace tailWord_7808268 prefixEnd_7808268 1336464854373653783080145 := by
  unfold tailWord_7808268
  simp only [CollatzResearch.WordTrace]
  refine ⟨142395465237993028425244729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189860620317324037900326305 142395465237993028425244729)
  ·
    refine ⟨106796598928494771318933547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142395465237993028425244729 106796598928494771318933547)
    ·
      refine ⟨160194898392742156978400321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106796598928494771318933547 160194898392742156978400321)
      ·
        refine ⟨120146173794556617733800241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160194898392742156978400321 120146173794556617733800241)
        ·
          refine ⟨90109630345917463300350181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120146173794556617733800241 90109630345917463300350181)
          ·
            refine ⟨16895555689859524368815659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90109630345917463300350181 16895555689859524368815659)
            ·
              refine ⟨25343333534789286553223489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16895555689859524368815659 25343333534789286553223489)
              ·
                refine ⟨19007500151091964914917617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25343333534789286553223489 19007500151091964914917617)
                ·
                  refine ⟨14255625113318973686188213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19007500151091964914917617 14255625113318973686188213)
                  ·
                    refine ⟨1336464854373653783080145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14255625113318973686188213 1336464854373653783080145)
                    ·
                      rfl

theorem cell23_7808268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_7808268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808268 prefixEnd_7808268 := by exact prefixLift 7808268
  have htrace : WordTrace (prefixWord ++ tailWord_7808268) baseStart_7808268 baseEnd_7808268 := by
    simpa [prefixWord, tailWord_7808268, baseEnd_7808268] using wordTrace_append hprefix tailTrace_7808268
  have hstable : (prefixWord ++ tailWord_7808268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808268).length < 2 ^ (prefixWord ++ tailWord_7808268).sum := by decide
  have hdescent : baseEnd_7808268 < baseStart_7808268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808305 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 4]
def baseStart_7808305 : Nat := 118140960795 + 7808305 * 2 ^ 59
def prefixEnd_7808305 : Nat := 4983230072969 + 3 ^ 40 * 7808305 * 2
def baseEnd_7808305 : Nat := 4009413561905177704477765

theorem tailTrace_7808305 : CollatzResearch.WordTrace tailWord_7808305 prefixEnd_7808305 4009413561905177704477765 := by
  unfold tailWord_7808305
  simp only [CollatzResearch.WordTrace]
  refine ⟨284792279976852012169586369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189861519984568008113057579 284792279976852012169586369)
  ·
    refine ⟨213594209982639009127189777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284792279976852012169586369 213594209982639009127189777)
    ·
      refine ⟨160195657486979256845392333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213594209982639009127189777 160195657486979256845392333)
      ·
        refine ⟨60073371557617221317022125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160195657486979256845392333 60073371557617221317022125)
        ·
          refine ⟨22527514334106457993883297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60073371557617221317022125 22527514334106457993883297)
          ·
            refine ⟨16895635750579843495412473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22527514334106457993883297 16895635750579843495412473)
            ·
              refine ⟨12671726812934882621559355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16895635750579843495412473 12671726812934882621559355)
              ·
                refine ⟨19007590219402323932339033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12671726812934882621559355 19007590219402323932339033)
                ·
                  refine ⟨14255692664551742949254275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19007590219402323932339033 14255692664551742949254275)
                  ·
                    refine ⟨21383538996827614423881413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14255692664551742949254275 21383538996827614423881413)
                    ·
                      refine ⟨4009413561905177704477765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21383538996827614423881413 4009413561905177704477765)
                      ·
                        rfl

theorem cell23_7808305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_7808305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808305 prefixEnd_7808305 := by exact prefixLift 7808305
  have htrace : WordTrace (prefixWord ++ tailWord_7808305) baseStart_7808305 baseEnd_7808305 := by
    simpa [prefixWord, tailWord_7808305, baseEnd_7808305] using wordTrace_append hprefix tailTrace_7808305
  have hstable : (prefixWord ++ tailWord_7808305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808305).length < 2 ^ (prefixWord ++ tailWord_7808305).sum := by decide
  have hdescent : baseEnd_7808305 < baseStart_7808305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808318 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_7808318 : Nat := 118140960795 + 7808318 * 2 ^ 59
def prefixEnd_7808318 : Nat := 4983230072969 + 3 ^ 40 * 7808318 * 2
def baseEnd_7808318 : Nat := 4009420237153686153615205

theorem tailTrace_7808318 : CollatzResearch.WordTrace tailWord_7808318 prefixEnd_7808318 4009420237153686153615205 := by
  unfold tailWord_7808318
  simp only [CollatzResearch.WordTrace]
  refine ⟨35599094265725614423726201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189861836083869943593206405 35599094265725614423726201)
  ·
    refine ⟨26699320699294210817794651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35599094265725614423726201 26699320699294210817794651)
    ·
      refine ⟨40048981048941316226691977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26699320699294210817794651 40048981048941316226691977)
      ·
        refine ⟨30036735786705987170018983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40048981048941316226691977 30036735786705987170018983)
        ·
          refine ⟨45055103680058980755028475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30036735786705987170018983 45055103680058980755028475)
          ·
            refine ⟨67582655520088471132542713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45055103680058980755028475 67582655520088471132542713)
            ·
              refine ⟨50686991640066353349407035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67582655520088471132542713 50686991640066353349407035)
              ·
                refine ⟨76030487460099530024110553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50686991640066353349407035 76030487460099530024110553)
                ·
                  refine ⟨57022865595074647518082915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76030487460099530024110553 57022865595074647518082915)
                  ·
                    refine ⟨85534298392611971277124373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57022865595074647518082915 85534298392611971277124373)
                    ·
                      refine ⟨4009420237153686153615205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85534298392611971277124373 4009420237153686153615205)
                      ·
                        rfl

theorem cell23_7808318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_7808318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808318 prefixEnd_7808318 := by exact prefixLift 7808318
  have htrace : WordTrace (prefixWord ++ tailWord_7808318) baseStart_7808318 baseEnd_7808318 := by
    simpa [prefixWord, tailWord_7808318, baseEnd_7808318] using wordTrace_append hprefix tailTrace_7808318
  have hstable : (prefixWord ++ tailWord_7808318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808318).length < 2 ^ (prefixWord ++ tailWord_7808318).sum := by decide
  have hdescent : baseEnd_7808318 < baseStart_7808318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808332 : List Nat := [2, 2, 1, 3, 2, 3, 1, 4, 1, 4]
def baseStart_7808332 : Nat := 118140960795 + 7808332 * 2 ^ 59
def prefixEnd_7808332 : Nat := 4983230072969 + 3 ^ 40 * 7808332 * 2
def baseEnd_7808332 : Nat := 1336475808627616366280047

theorem tailTrace_7808332 : CollatzResearch.WordTrace tailWord_7808332 prefixEnd_7808332 1336475808627616366280047 := by
  unfold tailWord_7808332
  simp only [CollatzResearch.WordTrace]
  refine ⟨142396632373877097890409625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189862176498502797187212833 142396632373877097890409625)
  ·
    refine ⟨106797474280407823417807219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142396632373877097890409625 106797474280407823417807219)
    ·
      refine ⟨160196211420611735126710829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106797474280407823417807219 160196211420611735126710829)
      ·
        refine ⟨60073579282729400672516561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160196211420611735126710829 60073579282729400672516561)
        ·
          refine ⟨45055184462047050504387421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60073579282729400672516561 45055184462047050504387421)
          ·
            refine ⟨16895694173267643939145283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45055184462047050504387421 16895694173267643939145283)
            ·
              refine ⟨25343541259901465908717925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16895694173267643939145283 25343541259901465908717925)
              ·
                refine ⟨4751913986231524857884611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25343541259901465908717925 4751913986231524857884611)
                ·
                  refine ⟨7127870979347287286826917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4751913986231524857884611 7127870979347287286826917)
                  ·
                    refine ⟨1336475808627616366280047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7127870979347287286826917 1336475808627616366280047)
                    ·
                      rfl

theorem cell23_7808332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_7808332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808332 prefixEnd_7808332 := by exact prefixLift 7808332
  have htrace : WordTrace (prefixWord ++ tailWord_7808332) baseStart_7808332 baseEnd_7808332 := by
    simpa [prefixWord, tailWord_7808332, baseEnd_7808332] using wordTrace_append hprefix tailTrace_7808332
  have hstable : (prefixWord ++ tailWord_7808332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808332).length < 2 ^ (prefixWord ++ tailWord_7808332).sum := by decide
  have hdescent : baseEnd_7808332 < baseStart_7808332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808338 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_7808338 : Nat := 118140960795 + 7808338 * 2 ^ 59
def prefixEnd_7808338 : Nat := 4983230072969 + 3 ^ 40 * 7808338 * 2
def baseEnd_7808338 : Nat := 4009430506766776075365113

theorem tailTrace_7808338 : CollatzResearch.WordTrace tailWord_7808338 prefixEnd_7808338 4009430506766776075365113 := by
  unfold tailWord_7808338
  simp only [CollatzResearch.WordTrace]
  refine ⟨71198370896433114701384417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189862322390488305870358445 71198370896433114701384417)
  ·
    refine ⟨53398778172324836026038313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71198370896433114701384417 53398778172324836026038313)
    ·
      refine ⟨40049083629243627019528735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53398778172324836026038313 40049083629243627019528735)
      ·
        refine ⟨60073625443865440529293103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40049083629243627019528735 60073625443865440529293103)
        ·
          refine ⟨90110438165798160793939655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60073625443865440529293103 90110438165798160793939655)
          ·
            refine ⟨135165657248697241190909483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90110438165798160793939655 135165657248697241190909483)
            ·
              refine ⟨202748485873045861786364225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135165657248697241190909483 202748485873045861786364225)
              ·
                refine ⟨152061364404784396339773169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202748485873045861786364225 152061364404784396339773169)
                ·
                  refine ⟨114046023303588297254829877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152061364404784396339773169 114046023303588297254829877)
                  ·
                    refine ⟨10691814684711402867640301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114046023303588297254829877 10691814684711402867640301)
                    ·
                      refine ⟨4009430506766776075365113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10691814684711402867640301 4009430506766776075365113)
                      ·
                        rfl

theorem cell23_7808338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_7808338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808338 prefixEnd_7808338 := by exact prefixLift 7808338
  have htrace : WordTrace (prefixWord ++ tailWord_7808338) baseStart_7808338 baseEnd_7808338 := by
    simpa [prefixWord, tailWord_7808338, baseEnd_7808338] using wordTrace_append hprefix tailTrace_7808338
  have hstable : (prefixWord ++ tailWord_7808338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808338).length < 2 ^ (prefixWord ++ tailWord_7808338).sum := by decide
  have hdescent : baseEnd_7808338 < baseStart_7808338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808351 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_7808351 : Nat := 118140960795 + 7808351 * 2 ^ 59
def prefixEnd_7808351 : Nat := 4983230072969 + 3 ^ 40 * 7808351 * 2
def baseEnd_7808351 : Nat := 4009437182015284524502553

theorem tailTrace_7808351 : CollatzResearch.WordTrace tailWord_7808351 prefixEnd_7808351 4009437182015284524502553 := by
  unfold tailWord_7808351
  simp only [CollatzResearch.WordTrace]
  refine ⟨284793957734685362025760907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189862638489790241350507271 284793957734685362025760907)
  ·
    refine ⟨427190936602028043038641361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284793957734685362025760907 427190936602028043038641361)
    ·
      refine ⟨320393202451521032278981021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427190936602028043038641361 320393202451521032278981021)
      ·
        refine ⟨120147450919320387104617883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320393202451521032278981021 120147450919320387104617883)
        ·
          refine ⟨180221176378980580656926825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120147450919320387104617883 180221176378980580656926825)
          ·
            refine ⟨135165882284235435492695119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180221176378980580656926825 135165882284235435492695119)
            ·
              refine ⟨202748823426353153239042679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135165882284235435492695119 202748823426353153239042679)
              ·
                refine ⟨304123235139529729858564019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202748823426353153239042679 304123235139529729858564019)
                ·
                  refine ⟨456184852709294594787846029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304123235139529729858564019 456184852709294594787846029)
                  ·
                    refine ⟨171069319765985473045442261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456184852709294594787846029 171069319765985473045442261)
                    ·
                      refine ⟨4009437182015284524502553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171069319765985473045442261 4009437182015284524502553)
                      ·
                        rfl

theorem cell23_7808351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_7808351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808351 prefixEnd_7808351 := by exact prefixLift 7808351
  have htrace : WordTrace (prefixWord ++ tailWord_7808351) baseStart_7808351 baseEnd_7808351 := by
    simpa [prefixWord, tailWord_7808351, baseEnd_7808351] using wordTrace_append hprefix tailTrace_7808351
  have hstable : (prefixWord ++ tailWord_7808351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808351).length < 2 ^ (prefixWord ++ tailWord_7808351).sum := by decide
  have hdescent : baseEnd_7808351 < baseStart_7808351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808355 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 5, 1, 3]
def baseStart_7808355 : Nat := 118140960795 + 7808355 * 2 ^ 59
def prefixEnd_7808355 : Nat := 4983230072969 + 3 ^ 40 * 7808355 * 2
def baseEnd_7808355 : Nat := 4009439235937902508852535

theorem tailTrace_7808355 : CollatzResearch.WordTrace tailWord_7808355 prefixEnd_7808355 4009439235937902508852535 := by
  unfold tailWord_7808355
  simp only [CollatzResearch.WordTrace]
  refine ⟨284794103626670870708906519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189862735751113913805937679 284794103626670870708906519)
  ·
    refine ⟨427191155440006306063359779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284794103626670870708906519 427191155440006306063359779)
    ·
      refine ⟨640786733160009459095039669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427191155440006306063359779 640786733160009459095039669)
      ·
        refine ⟨60073756233750886790159969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 640786733160009459095039669 60073756233750886790159969)
        ·
          refine ⟨45055317175313165092619977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60073756233750886790159969 45055317175313165092619977)
          ·
            refine ⟨33791487881484873819464983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45055317175313165092619977 33791487881484873819464983)
            ·
              refine ⟨50687231822227310729197475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33791487881484873819464983 50687231822227310729197475)
              ·
                refine ⟨76030847733340966093796213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50687231822227310729197475 76030847733340966093796213)
                ·
                  refine ⟨7127891975000715571293395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76030847733340966093796213 7127891975000715571293395)
                  ·
                    refine ⟨10691837962501073356940093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7127891975000715571293395 10691837962501073356940093)
                    ·
                      refine ⟨4009439235937902508852535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10691837962501073356940093 4009439235937902508852535)
                      ·
                        rfl

theorem cell23_7808355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_7808355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808355 prefixEnd_7808355 := by exact prefixLift 7808355
  have htrace : WordTrace (prefixWord ++ tailWord_7808355) baseStart_7808355 baseEnd_7808355 := by
    simpa [prefixWord, tailWord_7808355, baseEnd_7808355] using wordTrace_append hprefix tailTrace_7808355
  have hstable : (prefixWord ++ tailWord_7808355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808355).length < 2 ^ (prefixWord ++ tailWord_7808355).sum := by decide
  have hdescent : baseEnd_7808355 < baseStart_7808355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808359 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_7808359 : Nat := 118140960795 + 7808359 * 2 ^ 59
def prefixEnd_7808359 : Nat := 4983230072969 + 3 ^ 40 * 7808359 * 2
def baseEnd_7808359 : Nat := 4009441289860520493202517

theorem tailTrace_7808359 : CollatzResearch.WordTrace tailWord_7808359 prefixEnd_7808359 4009441289860520493202517 := by
  unfold tailWord_7808359
  simp only [CollatzResearch.WordTrace]
  refine ⟨284794249518656379392052131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189862833012437586261368087 284794249518656379392052131)
  ·
    refine ⟨427191374277984569088078197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284794249518656379392052131 427191374277984569088078197)
    ·
      refine ⟨40049191338561053352007331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427191374277984569088078197 40049191338561053352007331)
      ·
        refine ⟨60073787007841580028010997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40049191338561053352007331 60073787007841580028010997)
        ·
          refine ⟨5631917531985148127626031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60073787007841580028010997 5631917531985148127626031)
          ·
            refine ⟨8447876297977722191439047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631917531985148127626031 8447876297977722191439047)
            ·
              refine ⟨12671814446966583287158571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8447876297977722191439047 12671814446966583287158571)
              ·
                refine ⟨19007721670449874930737857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12671814446966583287158571 19007721670449874930737857)
                ·
                  refine ⟨14255791252837406198053393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19007721670449874930737857 14255791252837406198053393)
                  ·
                    refine ⟨10691843439628054648540045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14255791252837406198053393 10691843439628054648540045)
                    ·
                      refine ⟨4009441289860520493202517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10691843439628054648540045 4009441289860520493202517)
                      ·
                        rfl

theorem cell23_7808359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_7808359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808359 prefixEnd_7808359 := by exact prefixLift 7808359
  have htrace : WordTrace (prefixWord ++ tailWord_7808359) baseStart_7808359 baseEnd_7808359 := by
    simpa [prefixWord, tailWord_7808359, baseEnd_7808359] using wordTrace_append hprefix tailTrace_7808359
  have hstable : (prefixWord ++ tailWord_7808359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808359).length < 2 ^ (prefixWord ++ tailWord_7808359).sum := by decide
  have hdescent : baseEnd_7808359 < baseStart_7808359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808366 : List Nat := [4, 1, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_7808366 : Nat := 118140960795 + 7808366 * 2 ^ 59
def prefixEnd_7808366 : Nat := 4983230072969 + 3 ^ 40 * 7808366 * 2
def baseEnd_7808366 : Nat := 1336481628075033988604995

theorem tailTrace_7808366 : CollatzResearch.WordTrace tailWord_7808366 prefixEnd_7808366 1336481628075033988604995 := by
  unfold tailWord_7808366
  simp only [CollatzResearch.WordTrace]
  refine ⟨35599313103703877448444619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189863003219754013058371301 35599313103703877448444619)
  ·
    refine ⟨53398969655555816172666929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35599313103703877448444619 53398969655555816172666929)
    ·
      refine ⟨40049227241666862129500197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53398969655555816172666929 40049227241666862129500197)
      ·
        refine ⟨7509230107812536649281287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40049227241666862129500197 7509230107812536649281287)
        ·
          refine ⟨11263845161718804973921931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7509230107812536649281287 11263845161718804973921931)
          ·
            refine ⟨16895767742578207460882897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11263845161718804973921931 16895767742578207460882897)
            ·
              refine ⟨12671825806933655595662173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16895767742578207460882897 12671825806933655595662173)
              ·
                refine ⟨4751934677600120848373315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12671825806933655595662173 4751934677600120848373315)
                ·
                  refine ⟨7127902016400181272559973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4751934677600120848373315 7127902016400181272559973)
                  ·
                    refine ⟨1336481628075033988604995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7127902016400181272559973 1336481628075033988604995)
                    ·
                      rfl

theorem cell23_7808366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_7808366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808366 prefixEnd_7808366 := by exact prefixLift 7808366
  have htrace : WordTrace (prefixWord ++ tailWord_7808366) baseStart_7808366 baseEnd_7808366 := by
    simpa [prefixWord, tailWord_7808366, baseEnd_7808366] using wordTrace_append hprefix tailTrace_7808366
  have hstable : (prefixWord ++ tailWord_7808366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808366).length < 2 ^ (prefixWord ++ tailWord_7808366).sum := by decide
  have hdescent : baseEnd_7808366 < baseStart_7808366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808405 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_7808405 : Nat := 118140960795 + 7808405 * 2 ^ 59
def prefixEnd_7808405 : Nat := 4983230072969 + 3 ^ 40 * 7808405 * 2
def baseEnd_7808405 : Nat := 1336488303323542437742435

theorem tailTrace_7808405 : CollatzResearch.WordTrace tailWord_7808405 prefixEnd_7808405 1336488303323542437742435 := by
  unfold tailWord_7808405
  simp only [CollatzResearch.WordTrace]
  refine ⟨284795927276489729248226669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189863951517659819498817779 284795927276489729248226669)
  ·
    refine ⟨106798472728683648468085001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284795927276489729248226669 106798472728683648468085001)
    ·
      refine ⟨80098854546512736351063751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106798472728683648468085001 80098854546512736351063751)
      ·
        refine ⟨120148281819769104526595627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80098854546512736351063751 120148281819769104526595627)
        ·
          refine ⟨180222422729653656789893441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120148281819769104526595627 180222422729653656789893441)
          ·
            refine ⟨135166817047240242592420081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180222422729653656789893441 135166817047240242592420081)
            ·
              refine ⟨101375112785430181944315061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135166817047240242592420081 101375112785430181944315061)
              ·
                refine ⟨9503916823634079557279537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101375112785430181944315061 9503916823634079557279537)
                ·
                  refine ⟨7127937617725559667959653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9503916823634079557279537 7127937617725559667959653)
                  ·
                    refine ⟨1336488303323542437742435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7127937617725559667959653 1336488303323542437742435)
                    ·
                      rfl

theorem cell23_7808405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_7808405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808405 prefixEnd_7808405 := by exact prefixLift 7808405
  have htrace : WordTrace (prefixWord ++ tailWord_7808405) baseStart_7808405 baseEnd_7808405 := by
    simpa [prefixWord, tailWord_7808405, baseEnd_7808405] using wordTrace_append hprefix tailTrace_7808405
  have hstable : (prefixWord ++ tailWord_7808405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808405).length < 2 ^ (prefixWord ++ tailWord_7808405).sum := by decide
  have hdescent : baseEnd_7808405 < baseStart_7808405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808519 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 1, 4, 2]
def baseStart_7808519 : Nat := 118140960795 + 7808519 * 2 ^ 59
def prefixEnd_7808519 : Nat := 4983230072969 + 3 ^ 40 * 7808519 * 2
def baseEnd_7808519 : Nat := 4009523446765239867201781

theorem tailTrace_7808519 : CollatzResearch.WordTrace tailWord_7808519 prefixEnd_7808519 4009523446765239867201781 := by
  unfold tailWord_7808519
  simp only [CollatzResearch.WordTrace]
  refine ⟨284800085198076726717876611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189866723465384484478584407 284800085198076726717876611)
  ·
    refine ⟨427200127797115090076814917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284800085198076726717876611 427200127797115090076814917)
    ·
      refine ⟨80100023961959079389402797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427200127797115090076814917 80100023961959079389402797)
      ·
        refine ⟨30037508985734654771026049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80100023961959079389402797 30037508985734654771026049)
        ·
          refine ⟨22528131739300991078269537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30037508985734654771026049 22528131739300991078269537)
          ·
            refine ⟨16896098804475743308702153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22528131739300991078269537 16896098804475743308702153)
            ·
              refine ⟨12672074103356807481526615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16896098804475743308702153 12672074103356807481526615)
              ·
                refine ⟨19008111155035211222289923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12672074103356807481526615 19008111155035211222289923)
                ·
                  refine ⟨28512166732552816833434885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19008111155035211222289923 28512166732552816833434885)
                  ·
                    refine ⟨5346031262353653156269041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28512166732552816833434885 5346031262353653156269041)
                    ·
                      refine ⟨4009523446765239867201781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5346031262353653156269041 4009523446765239867201781)
                      ·
                        rfl

theorem cell23_7808519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_7808519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808519 prefixEnd_7808519 := by exact prefixLift 7808519
  have htrace : WordTrace (prefixWord ++ tailWord_7808519) baseStart_7808519 baseEnd_7808519 := by
    simpa [prefixWord, tailWord_7808519, baseEnd_7808519] using wordTrace_append hprefix tailTrace_7808519
  have hstable : (prefixWord ++ tailWord_7808519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808519).length < 2 ^ (prefixWord ++ tailWord_7808519).sum := by decide
  have hdescent : baseEnd_7808519 < baseStart_7808519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808575 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_7808575 : Nat := 118140960795 + 7808575 * 2 ^ 59
def prefixEnd_7808575 : Nat := 4983230072969 + 3 ^ 40 * 7808575 * 2
def baseEnd_7808575 : Nat := 4009552201681891648101523

theorem tailTrace_7808575 : CollatzResearch.WordTrace tailWord_7808575 prefixEnd_7808575 4009552201681891648101523 := by
  unfold tailWord_7808575
  simp only [CollatzResearch.WordTrace]
  refine ⟨284802127685873848281915179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189868085123915898854610119 284802127685873848281915179)
  ·
    refine ⟨427203191528810772422872769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284802127685873848281915179 427203191528810772422872769)
    ·
      refine ⟨320402393646608079317154577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427203191528810772422872769 320402393646608079317154577)
      ·
        refine ⟨240301795234956059487865933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320402393646608079317154577 240301795234956059487865933)
        ·
          refine ⟨90113173213108522307949725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240301795234956059487865933 90113173213108522307949725)
          ·
            refine ⟨33792439954915695865481147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90113173213108522307949725 33792439954915695865481147)
            ·
              refine ⟨50688659932373543798221721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33792439954915695865481147 50688659932373543798221721)
              ·
                refine ⟨38016494949280157848666291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50688659932373543798221721 38016494949280157848666291)
                ·
                  refine ⟨57024742423920236772999437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38016494949280157848666291 57024742423920236772999437)
                  ·
                    refine ⟨21384278408970088789874789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57024742423920236772999437 21384278408970088789874789)
                    ·
                      refine ⟨4009552201681891648101523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21384278408970088789874789 4009552201681891648101523)
                      ·
                        rfl

theorem cell23_7808575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_7808575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808575 prefixEnd_7808575 := by exact prefixLift 7808575
  have htrace : WordTrace (prefixWord ++ tailWord_7808575) baseStart_7808575 baseEnd_7808575 := by
    simpa [prefixWord, tailWord_7808575, baseEnd_7808575] using wordTrace_append hprefix tailTrace_7808575
  have hstable : (prefixWord ++ tailWord_7808575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808575).length < 2 ^ (prefixWord ++ tailWord_7808575).sum := by decide
  have hdescent : baseEnd_7808575 < baseStart_7808575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808612 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_7808612 : Nat := 118140960795 + 7808612 * 2 ^ 59
def prefixEnd_7808612 : Nat := 4983230072969 + 3 ^ 40 * 7808612 * 2
def baseEnd_7808612 : Nat := 4009571200466108003338853

theorem tailTrace_7808612 : CollatzResearch.WordTrace tailWord_7808612 prefixEnd_7808612 4009571200466108003338853 := by
  unfold tailWord_7808612
  simp only [CollatzResearch.WordTrace]
  refine ⟨142401738593369901800506045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189868984791159869067341393 142401738593369901800506045)
  ·
    refine ⟨53400651972513713175189767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142401738593369901800506045 53400651972513713175189767)
    ·
      refine ⟨80100977958770569762784651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53400651972513713175189767 80100977958770569762784651)
      ·
        refine ⟨120151466938155854644176977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80100977958770569762784651 120151466938155854644176977)
        ·
          refine ⟨90113600203616890983132733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120151466938155854644176977 90113600203616890983132733)
          ·
            refine ⟨33792600076356334118674775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90113600203616890983132733 33792600076356334118674775)
            ·
              refine ⟨50688900114534501178012163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33792600076356334118674775 50688900114534501178012163)
              ·
                refine ⟨76033350171801751767018245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50688900114534501178012163 76033350171801751767018245)
                ·
                  refine ⟨14256253157212828456315921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76033350171801751767018245 14256253157212828456315921)
                  ·
                    refine ⟨10692189867909621342236941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14256253157212828456315921 10692189867909621342236941)
                    ·
                      refine ⟨4009571200466108003338853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10692189867909621342236941 4009571200466108003338853)
                      ·
                        rfl

theorem cell23_7808612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_7808612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808612 prefixEnd_7808612 := by exact prefixLift 7808612
  have htrace : WordTrace (prefixWord ++ tailWord_7808612) baseStart_7808612 baseEnd_7808612 := by
    simpa [prefixWord, tailWord_7808612, baseEnd_7808612] using wordTrace_append hprefix tailTrace_7808612
  have hstable : (prefixWord ++ tailWord_7808612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808612).length < 2 ^ (prefixWord ++ tailWord_7808612).sum := by decide
  have hdescent : baseEnd_7808612 < baseStart_7808612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808615 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 8]
def baseStart_7808615 : Nat := 118140960795 + 7808615 * 2 ^ 59
def prefixEnd_7808615 : Nat := 4983230072969 + 3 ^ 40 * 7808615 * 2
def baseEnd_7808615 : Nat := 445508082323119054622371

theorem tailTrace_7808615 : CollatzResearch.WordTrace tailWord_7808615 prefixEnd_7808615 445508082323119054622371 := by
  unfold tailWord_7808615
  simp only [CollatzResearch.WordTrace]
  refine ⟨284803586605728935113371299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189869057737152623408914199 284803586605728935113371299)
  ·
    refine ⟨427205379908593402670056949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284803586605728935113371299 427205379908593402670056949)
    ·
      refine ⟨40050504366430631500317839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427205379908593402670056949 40050504366430631500317839)
      ·
        refine ⟨60075756549645947250476759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40050504366430631500317839 60075756549645947250476759)
        ·
          refine ⟨90113634824468920875715139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60075756549645947250476759 90113634824468920875715139)
          ·
            refine ⟨135170452236703381313572709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90113634824468920875715139 135170452236703381313572709)
            ·
              refine ⟨25344459794381883996294883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135170452236703381313572709 25344459794381883996294883)
              ·
                refine ⟨38016689691572825994442325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25344459794381883996294883 38016689691572825994442325)
                ·
                  refine ⟨445508082323119054622371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38016689691572825994442325 445508082323119054622371)
                  ·
                    rfl

theorem cell23_7808615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 8].length) (baseStart_7808615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808615 prefixEnd_7808615 := by exact prefixLift 7808615
  have htrace : WordTrace (prefixWord ++ tailWord_7808615) baseStart_7808615 baseEnd_7808615 := by
    simpa [prefixWord, tailWord_7808615, baseEnd_7808615] using wordTrace_append hprefix tailTrace_7808615
  have hstable : (prefixWord ++ tailWord_7808615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808615).length < 2 ^ (prefixWord ++ tailWord_7808615).sum := by decide
  have hdescent : baseEnd_7808615 < baseStart_7808615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808670 : List Nat := [4, 3, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_7808670 : Nat := 118140960795 + 7808670 * 2 ^ 59
def prefixEnd_7808670 : Nat := 4983230072969 + 3 ^ 40 * 7808670 * 2
def baseEnd_7808670 : Nat := 1336533660781356258804529

theorem tailTrace_7808670 : CollatzResearch.WordTrace tailWord_7808670 prefixEnd_7808670 1336533660781356258804529 := by
  unfold tailWord_7808670
  simp only [CollatzResearch.WordTrace]
  refine ⟨35600699077566209938327933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189870395080353119671082309 35600699077566209938327933)
  ·
    refine ⟨13350262154087328726872975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35600699077566209938327933 13350262154087328726872975)
    ·
      refine ⟨20025393231130993090309463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13350262154087328726872975 20025393231130993090309463)
      ·
        refine ⟨30038089846696489635464195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20025393231130993090309463 30038089846696489635464195)
        ·
          refine ⟨45057134770044734453196293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30038089846696489635464195 45057134770044734453196293)
          ·
            refine ⟨8448212769383387709974305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45057134770044734453196293 8448212769383387709974305)
            ·
              refine ⟨6336159577037540782480729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8448212769383387709974305 6336159577037540782480729)
              ·
                refine ⟨4752119682778155586860547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6336159577037540782480729 4752119682778155586860547)
                ·
                  refine ⟨7128179524167233380290821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752119682778155586860547 7128179524167233380290821)
                  ·
                    refine ⟨1336533660781356258804529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7128179524167233380290821 1336533660781356258804529)
                    ·
                      rfl

theorem cell23_7808670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_7808670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808670 prefixEnd_7808670 := by exact prefixLift 7808670
  have htrace : WordTrace (prefixWord ++ tailWord_7808670) baseStart_7808670 baseEnd_7808670 := by
    simpa [prefixWord, tailWord_7808670, baseEnd_7808670] using wordTrace_append hprefix tailTrace_7808670
  have hstable : (prefixWord ++ tailWord_7808670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808670).length < 2 ^ (prefixWord ++ tailWord_7808670).sum := by decide
  have hdescent : baseEnd_7808670 < baseStart_7808670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808675 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 3, 6]
def baseStart_7808675 : Nat := 118140960795 + 7808675 * 2 ^ 59
def prefixEnd_7808675 : Nat := 4983230072969 + 3 ^ 40 * 7808675 * 2
def baseEnd_7808675 : Nat := 1336534516582447085617021

theorem tailTrace_7808675 : CollatzResearch.WordTrace tailWord_7808675 prefixEnd_7808675 1336534516582447085617021 := by
  unfold tailWord_7808675
  simp only [CollatzResearch.WordTrace]
  refine ⟨284805774985511565360555479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189870516657007710240370319 284805774985511565360555479)
  ·
    refine ⟨427208662478267348040833219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284805774985511565360555479 427208662478267348040833219)
    ·
      refine ⟨640812993717401022061249829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427208662478267348040833219 640812993717401022061249829)
      ·
        refine ⟨120152436322012691636484343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 640812993717401022061249829 120152436322012691636484343)
        ·
          refine ⟨180228654483019037454726515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120152436322012691636484343 180228654483019037454726515)
          ·
            refine ⟨270342981724528556182089773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180228654483019037454726515 270342981724528556182089773)
            ·
              refine ⟨101378618146698208568283665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270342981724528556182089773 101378618146698208568283665)
              ·
                refine ⟨76033963610023656426212749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101378618146698208568283665 76033963610023656426212749)
                ·
                  refine ⟨28512736353758871159829781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76033963610023656426212749 28512736353758871159829781)
                  ·
                    refine ⟨1336534516582447085617021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28512736353758871159829781 1336534516582447085617021)
                    ·
                      rfl

theorem cell23_7808675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 6].length) (baseStart_7808675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808675 prefixEnd_7808675 := by exact prefixLift 7808675
  have htrace : WordTrace (prefixWord ++ tailWord_7808675) baseStart_7808675 baseEnd_7808675 := by
    simpa [prefixWord, tailWord_7808675, baseEnd_7808675] using wordTrace_append hprefix tailTrace_7808675
  have hstable : (prefixWord ++ tailWord_7808675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808675).length < 2 ^ (prefixWord ++ tailWord_7808675).sum := by decide
  have hdescent : baseEnd_7808675 < baseStart_7808675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808712 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_7808712 : Nat := 118140960795 + 7808712 * 2 ^ 59
def prefixEnd_7808712 : Nat := 4983230072969 + 3 ^ 40 * 7808712 * 2
def baseEnd_7808712 : Nat := 4009622548531557612088393

theorem tailTrace_7808712 : CollatzResearch.WordTrace tailWord_7808712 prefixEnd_7808712 4009622548531557612088393 := by
  unfold tailWord_7808712
  simp only [CollatzResearch.WordTrace]
  refine ⟨142403562243188760339826195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189871416324251680453101593 142403562243188760339826195)
  ·
    refine ⟨213605343364783140509739293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142403562243188760339826195 213605343364783140509739293)
    ·
      refine ⟨80102003761793677691152235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213605343364783140509739293 80102003761793677691152235)
      ·
        refine ⟨120153005642690516536728353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80102003761793677691152235 120153005642690516536728353)
        ·
          refine ⟨90114754232017887402546265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120153005642690516536728353 90114754232017887402546265)
          ·
            refine ⟨67586065674013415551909699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90114754232017887402546265 67586065674013415551909699)
            ·
              refine ⟨101379098511020123327864549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67586065674013415551909699 101379098511020123327864549)
              ·
                refine ⟨19008580970816273123974603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101379098511020123327864549 19008580970816273123974603)
                ·
                  refine ⟨28512871456224409685961905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19008580970816273123974603 28512871456224409685961905)
                  ·
                    refine ⟨21384653592168307264471429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28512871456224409685961905 21384653592168307264471429)
                    ·
                      refine ⟨4009622548531557612088393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21384653592168307264471429 4009622548531557612088393)
                      ·
                        rfl

theorem cell23_7808712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_7808712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808712 prefixEnd_7808712 := by exact prefixLift 7808712
  have htrace : WordTrace (prefixWord ++ tailWord_7808712) baseStart_7808712 baseEnd_7808712 := by
    simpa [prefixWord, tailWord_7808712, baseEnd_7808712] using wordTrace_append hprefix tailTrace_7808712
  have hstable : (prefixWord ++ tailWord_7808712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808712).length < 2 ^ (prefixWord ++ tailWord_7808712).sum := by decide
  have hdescent : baseEnd_7808712 < baseStart_7808712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808716 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 1, 1, 4]
def baseStart_7808716 : Nat := 118140960795 + 7808716 * 2 ^ 59
def prefixEnd_7808716 : Nat := 4983230072969 + 3 ^ 40 * 7808716 * 2
def baseEnd_7808716 : Nat := 4009624602454175596438375

theorem tailTrace_7808716 : CollatzResearch.WordTrace tailWord_7808716 prefixEnd_7808716 4009624602454175596438375 := by
  unfold tailWord_7808716
  simp only [CollatzResearch.WordTrace]
  refine ⟨142403635189181514681399001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189871513585575352908532001 142403635189181514681399001)
  ·
    refine ⟨106802726391886136011049251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142403635189181514681399001 106802726391886136011049251)
    ·
      refine ⟨160204089587829204016573877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106802726391886136011049251 160204089587829204016573877)
      ·
        refine ⟨15019133398858987876553801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160204089587829204016573877 15019133398858987876553801)
        ·
          refine ⟨11264350049144240907415351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15019133398858987876553801 11264350049144240907415351)
          ·
            refine ⟨16896525073716361361123027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11264350049144240907415351 16896525073716361361123027)
            ·
              refine ⟨25344787610574542041684541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16896525073716361361123027 25344787610574542041684541)
              ·
                refine ⟨9504295353965453265631703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25344787610574542041684541 9504295353965453265631703)
                ·
                  refine ⟨14256443030948179898447555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9504295353965453265631703 14256443030948179898447555)
                  ·
                    refine ⟨21384664546422269847671333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14256443030948179898447555 21384664546422269847671333)
                    ·
                      refine ⟨4009624602454175596438375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21384664546422269847671333 4009624602454175596438375)
                      ·
                        rfl

theorem cell23_7808716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_7808716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808716 prefixEnd_7808716 := by exact prefixLift 7808716
  have htrace : WordTrace (prefixWord ++ tailWord_7808716) baseStart_7808716 baseEnd_7808716 := by
    simpa [prefixWord, tailWord_7808716, baseEnd_7808716] using wordTrace_append hprefix tailTrace_7808716
  have hstable : (prefixWord ++ tailWord_7808716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808716).length < 2 ^ (prefixWord ++ tailWord_7808716).sum := by decide
  have hdescent : baseEnd_7808716 < baseStart_7808716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808722 : List Nat := [3, 2, 2, 2, 2, 2, 10]
def baseStart_7808722 : Nat := 118140960795 + 7808722 * 2 ^ 59
def prefixEnd_7808722 : Nat := 4983230072969 + 3 ^ 40 * 7808722 * 2
def baseEnd_7808722 : Nat := 49501576337507439172387

theorem tailTrace_7808722 : CollatzResearch.WordTrace tailWord_7808722 prefixEnd_7808722 49501576337507439172387 := by
  unfold tailWord_7808722
  simp only [CollatzResearch.WordTrace]
  refine ⟨71201872304085323096879105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189871659477560861591677613 71201872304085323096879105)
  ·
    refine ⟨53401404228063992322659329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71201872304085323096879105 53401404228063992322659329)
    ·
      refine ⟨40051053171047994241994497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53401404228063992322659329 40051053171047994241994497)
      ·
        refine ⟨30038289878285995681495873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40051053171047994241994497 30038289878285995681495873)
        ·
          refine ⟨22528717408714496761121905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30038289878285995681495873 22528717408714496761121905)
          ·
            refine ⟨16896538056535872570841429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22528717408714496761121905 16896538056535872570841429)
            ·
              refine ⟨49501576337507439172387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16896538056535872570841429 49501576337507439172387)
              ·
                rfl

theorem cell23_7808722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 10].length) (baseStart_7808722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808722 prefixEnd_7808722 := by exact prefixLift 7808722
  have htrace : WordTrace (prefixWord ++ tailWord_7808722) baseStart_7808722 baseEnd_7808722 := by
    simpa [prefixWord, tailWord_7808722, baseEnd_7808722] using wordTrace_append hprefix tailTrace_7808722
  have hstable : (prefixWord ++ tailWord_7808722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808722).length < 2 ^ (prefixWord ++ tailWord_7808722).sum := by decide
  have hdescent : baseEnd_7808722 < baseStart_7808722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808743 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 1, 6]
def baseStart_7808743 : Nat := 118140960795 + 7808743 * 2 ^ 59
def prefixEnd_7808743 : Nat := 4983230072969 + 3 ^ 40 * 7808743 * 2
def baseEnd_7808743 : Nat := 1336546155477282330266917

theorem tailTrace_7808743 : CollatzResearch.WordTrace tailWord_7808743 prefixEnd_7808743 1336546155477282330266917 := by
  unfold tailWord_7808743
  simp only [CollatzResearch.WordTrace]
  refine ⟨284808255149265212974030883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189872170099510141982687255 284808255149265212974030883)
  ·
    refine ⟨427212382723897819461046325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284808255149265212974030883 427212382723897819461046325)
    ·
      refine ⟨40051160880365420574473093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427212382723897819461046325 40051160880365420574473093)
      ·
        refine ⟨7509592665068516357713705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40051160880365420574473093 7509592665068516357713705)
        ·
          refine ⟨5632194498801387268285279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7509592665068516357713705 5632194498801387268285279)
          ·
            refine ⟨8448291748202080902427919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632194498801387268285279 8448291748202080902427919)
            ·
              refine ⟨12672437622303121353641879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8448291748202080902427919 12672437622303121353641879)
              ·
                refine ⟨19008656433454682030462819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12672437622303121353641879 19008656433454682030462819)
                ·
                  refine ⟨28512984650182023045694229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19008656433454682030462819 28512984650182023045694229)
                  ·
                    refine ⟨1336546155477282330266917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28512984650182023045694229 1336546155477282330266917)
                    ·
                      rfl

theorem cell23_7808743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_7808743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808743 prefixEnd_7808743 := by exact prefixLift 7808743
  have htrace : WordTrace (prefixWord ++ tailWord_7808743) baseStart_7808743 baseEnd_7808743 := by
    simpa [prefixWord, tailWord_7808743, baseEnd_7808743] using wordTrace_append hprefix tailTrace_7808743
  have hstable : (prefixWord ++ tailWord_7808743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808743).length < 2 ^ (prefixWord ++ tailWord_7808743).sum := by decide
  have hdescent : baseEnd_7808743 < baseStart_7808743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808756 : List Nat := [2, 6, 1, 1, 1, 2, 1, 9]
def baseStart_7808756 : Nat := 118140960795 + 7808756 * 2 ^ 59
def prefixEnd_7808756 : Nat := 4983230072969 + 3 ^ 40 * 7808756 * 2
def baseEnd_7808756 : Nat := 148505375617790942219933

theorem tailTrace_7808756 : CollatzResearch.WordTrace tailWord_7808756 prefixEnd_7808756 148505375617790942219933 := by
  unfold tailWord_7808756
  simp only [CollatzResearch.WordTrace]
  refine ⟨142404364649109058097127061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189872486198812077462836081 142404364649109058097127061)
  ·
    refine ⟨6675204592926987098302831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142404364649109058097127061 6675204592926987098302831)
    ·
      refine ⟨10012806889390480647454247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6675204592926987098302831 10012806889390480647454247)
      ·
        refine ⟨15019210334085720971181371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10012806889390480647454247 15019210334085720971181371)
        ·
          refine ⟨22528815501128581456772057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15019210334085720971181371 22528815501128581456772057)
          ·
            refine ⟨16896611625846436092579043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22528815501128581456772057 16896611625846436092579043)
            ·
              refine ⟨25344917438769654138868565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16896611625846436092579043 25344917438769654138868565)
              ·
                refine ⟨148505375617790942219933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25344917438769654138868565 148505375617790942219933)
                ·
                  rfl

theorem cell23_7808756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 9].length) (baseStart_7808756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808756 prefixEnd_7808756 := by exact prefixLift 7808756
  have htrace : WordTrace (prefixWord ++ tailWord_7808756) baseStart_7808756 baseEnd_7808756 := by
    simpa [prefixWord, tailWord_7808756, baseEnd_7808756] using wordTrace_append hprefix tailTrace_7808756
  have hstable : (prefixWord ++ tailWord_7808756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808756).length < 2 ^ (prefixWord ++ tailWord_7808756).sum := by decide
  have hdescent : baseEnd_7808756 < baseStart_7808756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808759 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 3, 3, 2]
def baseStart_7808759 : Nat := 118140960795 + 7808759 * 2 ^ 59
def prefixEnd_7808759 : Nat := 4983230072969 + 3 ^ 40 * 7808759 * 2
def baseEnd_7808759 : Nat := 4009646682122318928200677

theorem tailTrace_7808759 : CollatzResearch.WordTrace tailWord_7808759 prefixEnd_7808759 4009646682122318928200677 := by
  unfold tailWord_7808759
  simp only [CollatzResearch.WordTrace]
  refine ⟨284808838717207247706613331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189872559144804831804408887 284808838717207247706613331)
  ·
    refine ⟨427213258075810871559919997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284808838717207247706613331 427213258075810871559919997)
    ·
      refine ⟨160204971778429076834969999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427213258075810871559919997 160204971778429076834969999)
      ·
        refine ⟨240307457667643615252454999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160204971778429076834969999 240307457667643615252454999)
        ·
          refine ⟨360461186501465422878682499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240307457667643615252454999 360461186501465422878682499)
          ·
            refine ⟨540691779752198134318023749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360461186501465422878682499 540691779752198134318023749)
            ·
              refine ⟨101379708703537150184629453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540691779752198134318023749 101379708703537150184629453)
              ·
                refine ⟨38017390763826431319236045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101379708703537150184629453 38017390763826431319236045)
                ·
                  refine ⟨14256521536434911744713517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38017390763826431319236045 14256521536434911744713517)
                  ·
                    refine ⟨5346195576163091904267569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14256521536434911744713517 5346195576163091904267569)
                    ·
                      refine ⟨4009646682122318928200677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5346195576163091904267569 4009646682122318928200677)
                      ·
                        rfl

theorem cell23_7808759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_7808759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808759 prefixEnd_7808759 := by exact prefixLift 7808759
  have htrace : WordTrace (prefixWord ++ tailWord_7808759) baseStart_7808759 baseEnd_7808759 := by
    simpa [prefixWord, tailWord_7808759, baseEnd_7808759] using wordTrace_append hprefix tailTrace_7808759
  have hstable : (prefixWord ++ tailWord_7808759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808759).length < 2 ^ (prefixWord ++ tailWord_7808759).sum := by decide
  have hdescent : baseEnd_7808759 < baseStart_7808759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808776 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 1, 3, 2]
def baseStart_7808776 : Nat := 118140960795 + 7808776 * 2 ^ 59
def prefixEnd_7808776 : Nat := 4983230072969 + 3 ^ 40 * 7808776 * 2
def baseEnd_7808776 : Nat := 4009655411293445361688099

theorem tailTrace_7808776 : CollatzResearch.WordTrace tailWord_7808776 prefixEnd_7808776 4009655411293445361688099 := by
  unfold tailWord_7808776
  simp only [CollatzResearch.WordTrace]
  refine ⟨142404729379072829804991091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189872972505430439739988121 142404729379072829804991091)
  ·
    refine ⟨213607094068609244707486637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142404729379072829804991091 213607094068609244707486637)
    ·
      refine ⟨80102660275728466765307489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213607094068609244707486637 80102660275728466765307489)
      ·
        refine ⟨60076995206796350073980617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80102660275728466765307489 60076995206796350073980617)
        ·
          refine ⟨45057746405097262555485463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60076995206796350073980617 45057746405097262555485463)
          ·
            refine ⟨67586619607645893833228195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45057746405097262555485463 67586619607645893833228195)
            ·
              refine ⟨101379929411468840749842293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67586619607645893833228195 101379929411468840749842293)
              ·
                refine ⟨9504368382325203820297715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101379929411468840749842293 9504368382325203820297715)
                ·
                  refine ⟨14256552573487805730446573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9504368382325203820297715 14256552573487805730446573)
                  ·
                    refine ⟨5346207215057927148917465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14256552573487805730446573 5346207215057927148917465)
                    ·
                      refine ⟨4009655411293445361688099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5346207215057927148917465 4009655411293445361688099)
                      ·
                        rfl

theorem cell23_7808776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_7808776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808776 prefixEnd_7808776 := by exact prefixLift 7808776
  have htrace : WordTrace (prefixWord ++ tailWord_7808776) baseStart_7808776 baseEnd_7808776 := by
    simpa [prefixWord, tailWord_7808776, baseEnd_7808776] using wordTrace_append hprefix tailTrace_7808776
  have hstable : (prefixWord ++ tailWord_7808776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808776).length < 2 ^ (prefixWord ++ tailWord_7808776).sum := by decide
  have hdescent : baseEnd_7808776 < baseStart_7808776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808782 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_7808782 : Nat := 118140960795 + 7808782 * 2 ^ 59
def prefixEnd_7808782 : Nat := 4983230072969 + 3 ^ 40 * 7808782 * 2
def baseEnd_7808782 : Nat := 1336552830725790779404357

theorem tailTrace_7808782 : CollatzResearch.WordTrace tailWord_7808782 prefixEnd_7808782 1336552830725790779404357 := by
  unfold tailWord_7808782
  simp only [CollatzResearch.WordTrace]
  refine ⟨35601209699515490329337575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189873118397415948423133733 35601209699515490329337575)
  ·
    refine ⟨53401814549273235494006363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35601209699515490329337575 53401814549273235494006363)
    ·
      refine ⟨80102721823909853241009545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53401814549273235494006363 80102721823909853241009545)
      ·
        refine ⟨60077041367932389930757159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80102721823909853241009545 60077041367932389930757159)
        ·
          refine ⟨90115562051898584896135739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60077041367932389930757159 90115562051898584896135739)
          ·
            refine ⟨135173343077847877344203609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90115562051898584896135739 135173343077847877344203609)
            ·
              refine ⟨101380007308385908008152707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135173343077847877344203609 101380007308385908008152707)
              ·
                refine ⟨152070010962578862012229061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101380007308385908008152707 152070010962578862012229061)
                ·
                  refine ⟨28513127055483536627292949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152070010962578862012229061 28513127055483536627292949)
                  ·
                    refine ⟨1336552830725790779404357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28513127055483536627292949 1336552830725790779404357)
                    ·
                      rfl

theorem cell23_7808782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_7808782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808782 prefixEnd_7808782 := by exact prefixLift 7808782
  have htrace : WordTrace (prefixWord ++ tailWord_7808782) baseStart_7808782 baseEnd_7808782 := by
    simpa [prefixWord, tailWord_7808782, baseEnd_7808782] using wordTrace_append hprefix tailTrace_7808782
  have hstable : (prefixWord ++ tailWord_7808782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808782).length < 2 ^ (prefixWord ++ tailWord_7808782).sum := by decide
  have hdescent : baseEnd_7808782 < baseStart_7808782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808876 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_7808876 : Nat := 118140960795 + 7808876 * 2 ^ 59
def prefixEnd_7808876 : Nat := 4983230072969 + 3 ^ 40 * 7808876 * 2
def baseEnd_7808876 : Nat := 1336568919786298323479213

theorem tailTrace_7808876 : CollatzResearch.WordTrace tailWord_7808876 prefixEnd_7808876 1336568919786298323479213 := by
  unfold tailWord_7808876
  simp only [CollatzResearch.WordTrace]
  refine ⟨142406553028891688344311241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189875404038522251125748321 142406553028891688344311241)
  ·
    refine ⟨106804914771668766258233431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142406553028891688344311241 106804914771668766258233431)
    ·
      refine ⟨160207372157503149387350147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106804914771668766258233431 160207372157503149387350147)
      ·
        refine ⟨240311058236254724081025221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160207372157503149387350147 240311058236254724081025221)
        ·
          refine ⟨45058323419297760765192229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240311058236254724081025221 45058323419297760765192229)
          ·
            refine ⟨8448435641118330143473543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45058323419297760765192229 8448435641118330143473543)
            ·
              refine ⟨12672653461677495215210315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8448435641118330143473543 12672653461677495215210315)
              ·
                refine ⟨19008980192516242822815473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12672653461677495215210315 19008980192516242822815473)
                ·
                  refine ⟨14256735144387182117111605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19008980192516242822815473 14256735144387182117111605)
                  ·
                    refine ⟨1336568919786298323479213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14256735144387182117111605 1336568919786298323479213)
                    ·
                      rfl

theorem cell23_7808876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_7808876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808876 prefixEnd_7808876 := by exact prefixLift 7808876
  have htrace : WordTrace (prefixWord ++ tailWord_7808876) baseStart_7808876 baseEnd_7808876 := by
    simpa [prefixWord, tailWord_7808876, baseEnd_7808876] using wordTrace_append hprefix tailTrace_7808876
  have hstable : (prefixWord ++ tailWord_7808876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808876).length < 2 ^ (prefixWord ++ tailWord_7808876).sum := by decide
  have hdescent : baseEnd_7808876 < baseStart_7808876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808889 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 5, 4]
def baseStart_7808889 : Nat := 118140960795 + 7808889 * 2 ^ 59
def prefixEnd_7808889 : Nat := 4983230072969 + 3 ^ 40 * 7808889 * 2
def baseEnd_7808889 : Nat := 1336571144869134473191693

theorem tailTrace_7808889 : CollatzResearch.WordTrace tailWord_7808889 prefixEnd_7808889 1336571144869134473191693 := by
  unfold tailWord_7808889
  simp only [CollatzResearch.WordTrace]
  refine ⟨284813580206736279908845721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189875720137824186605897147 284813580206736279908845721)
  ·
    refine ⟨213610185155052209931634291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284813580206736279908845721 213610185155052209931634291)
    ·
      refine ⟨320415277732578314897451437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213610185155052209931634291 320415277732578314897451437)
      ·
        refine ⟨120155729149716868086544289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320415277732578314897451437 120155729149716868086544289)
        ·
          refine ⟨90116796862287651064908217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120155729149716868086544289 90116796862287651064908217)
          ·
            refine ⟨67587597646715738298681163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90116796862287651064908217 67587597646715738298681163)
            ·
              refine ⟨101381396470073607448021745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67587597646715738298681163 101381396470073607448021745)
              ·
                refine ⟨76036047352555205586016309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101381396470073607448021745 76036047352555205586016309)
                ·
                  refine ⟨7128379439302050523689029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76036047352555205586016309 7128379439302050523689029)
                  ·
                    refine ⟨1336571144869134473191693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7128379439302050523689029 1336571144869134473191693)
                    ·
                      rfl

theorem cell23_7808889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 4].length) (baseStart_7808889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808889 prefixEnd_7808889 := by exact prefixLift 7808889
  have htrace : WordTrace (prefixWord ++ tailWord_7808889) baseStart_7808889 baseEnd_7808889 := by
    simpa [prefixWord, tailWord_7808889, baseEnd_7808889] using wordTrace_append hprefix tailTrace_7808889
  have hstable : (prefixWord ++ tailWord_7808889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808889).length < 2 ^ (prefixWord ++ tailWord_7808889).sum := by decide
  have hdescent : baseEnd_7808889 < baseStart_7808889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808916 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_7808916 : Nat := 118140960795 + 7808916 * 2 ^ 59
def prefixEnd_7808916 : Nat := 4983230072969 + 3 ^ 40 * 7808916 * 2
def baseEnd_7808916 : Nat := 4009727298585074813937455

theorem tailTrace_7808916 : CollatzResearch.WordTrace tailWord_7808916 prefixEnd_7808916 4009727298585074813937455 := by
  unfold tailWord_7808916
  simp only [CollatzResearch.WordTrace]
  refine ⟨142407282488819231760039301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189876376651758975680052401 142407282488819231760039301)
  ·
    refine ⟨26701365466653605955007369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142407282488819231760039301 26701365466653605955007369)
    ·
      refine ⟨20026024099990204466255527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26701365466653605955007369 20026024099990204466255527)
      ·
        refine ⟨30039036149985306699383291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20026024099990204466255527 30039036149985306699383291)
        ·
          refine ⟨45058554224977960049074937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30039036149985306699383291 45058554224977960049074937)
          ·
            refine ⟨33793915668733470036806203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45058554224977960049074937 33793915668733470036806203)
            ·
              refine ⟨50690873503100205055209305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33793915668733470036806203 50690873503100205055209305)
              ·
                refine ⟨38018155127325153791406979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50690873503100205055209305 38018155127325153791406979)
                ·
                  refine ⟨57027232690987730687110469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38018155127325153791406979 57027232690987730687110469)
                  ·
                    refine ⟨10692606129560199503833213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57027232690987730687110469 10692606129560199503833213)
                    ·
                      refine ⟨4009727298585074813937455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10692606129560199503833213 4009727298585074813937455)
                      ·
                        rfl

theorem cell23_7808916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_7808916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808916 prefixEnd_7808916 := by exact prefixLift 7808916
  have htrace : WordTrace (prefixWord ++ tailWord_7808916) baseStart_7808916 baseEnd_7808916 := by
    simpa [prefixWord, tailWord_7808916, baseEnd_7808916] using wordTrace_append hprefix tailTrace_7808916
  have hstable : (prefixWord ++ tailWord_7808916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808916).length < 2 ^ (prefixWord ++ tailWord_7808916).sum := by decide
  have hdescent : baseEnd_7808916 < baseStart_7808916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808946 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_7808946 : Nat := 118140960795 + 7808946 * 2 ^ 59
def prefixEnd_7808946 : Nat := 4983230072969 + 3 ^ 40 * 7808946 * 2
def baseEnd_7808946 : Nat := 4009742703004709696562317

theorem tailTrace_7808946 : CollatzResearch.WordTrace tailWord_7808946 prefixEnd_7808946 4009742703004709696562317 := by
  unfold tailWord_7808946
  simp only [CollatzResearch.WordTrace]
  refine ⟨71203914791882444660917673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189877106111686519095780461 71203914791882444660917673)
  ·
    refine ⟨53402936093911833495688255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71203914791882444660917673 53402936093911833495688255)
    ·
      refine ⟨80104404140867750243532383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53402936093911833495688255 80104404140867750243532383)
      ·
        refine ⟨120156606211301625365298575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80104404140867750243532383 120156606211301625365298575)
        ·
          refine ⟨180234909316952438047947863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120156606211301625365298575 180234909316952438047947863)
          ·
            refine ⟨270352363975428657071921795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180234909316952438047947863 270352363975428657071921795)
            ·
              refine ⟨405528545963142985607882693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270352363975428657071921795 405528545963142985607882693)
              ·
                refine ⟨76036602368089309801478005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405528545963142985607882693 76036602368089309801478005)
                ·
                  refine ⟨7128431472008372793888563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76036602368089309801478005 7128431472008372793888563)
                  ·
                    refine ⟨10692647208012559190832845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7128431472008372793888563 10692647208012559190832845)
                    ·
                      refine ⟨4009742703004709696562317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10692647208012559190832845 4009742703004709696562317)
                      ·
                        rfl

theorem cell23_7808946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_7808946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808946 prefixEnd_7808946 := by exact prefixLift 7808946
  have htrace : WordTrace (prefixWord ++ tailWord_7808946) baseStart_7808946 baseEnd_7808946 := by
    simpa [prefixWord, tailWord_7808946, baseEnd_7808946] using wordTrace_append hprefix tailTrace_7808946
  have hstable : (prefixWord ++ tailWord_7808946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808946).length < 2 ^ (prefixWord ++ tailWord_7808946).sum := by decide
  have hdescent : baseEnd_7808946 < baseStart_7808946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7808969 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 4]
def baseStart_7808969 : Nat := 118140960795 + 7808969 * 2 ^ 59
def prefixEnd_7808969 : Nat := 4983230072969 + 3 ^ 40 * 7808969 * 2
def baseEnd_7808969 : Nat := 4009754513059763106574711

theorem tailTrace_7808969 : CollatzResearch.WordTrace tailWord_7808969 prefixEnd_7808969 4009754513059763106574711 := by
  unfold tailWord_7808969
  simp only [CollatzResearch.WordTrace]
  refine ⟨284816498046446453571757961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189877665364297635714505307 284816498046446453571757961)
  ·
    refine ⟨213612373534834840178818471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284816498046446453571757961 213612373534834840178818471)
    ·
      refine ⟨320418560302252260268227707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213612373534834840178818471 320418560302252260268227707)
      ·
        refine ⟨480627840453378390402341561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320418560302252260268227707 480627840453378390402341561)
        ·
          refine ⟨360470880340033792801756171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480627840453378390402341561 360470880340033792801756171)
          ·
            refine ⟨540706320510050689202634257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360470880340033792801756171 540706320510050689202634257)
            ·
              refine ⟨405529740382538016901975693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540706320510050689202634257 405529740382538016901975693)
              ·
                refine ⟨152073652643451756338240885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405529740382538016901975693 152073652643451756338240885)
                ·
                  refine ⟨14256904935323602156710083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152073652643451756338240885 14256904935323602156710083)
                  ·
                    refine ⟨21385357402985403235065125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14256904935323602156710083 21385357402985403235065125)
                    ·
                      refine ⟨4009754513059763106574711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21385357402985403235065125 4009754513059763106574711)
                      ·
                        rfl

theorem cell23_7808969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_7808969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7808969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7808969 prefixEnd_7808969 := by exact prefixLift 7808969
  have htrace : WordTrace (prefixWord ++ tailWord_7808969) baseStart_7808969 baseEnd_7808969 := by
    simpa [prefixWord, tailWord_7808969, baseEnd_7808969] using wordTrace_append hprefix tailTrace_7808969
  have hstable : (prefixWord ++ tailWord_7808969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7808969).length < 2 ^ (prefixWord ++ tailWord_7808969).sum := by decide
  have hdescent : baseEnd_7808969 < baseStart_7808969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7808969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809009 : List Nat := [1, 2, 2, 2, 5, 11]
def baseStart_7809009 : Nat := 118140960795 + 7809009 * 2 ^ 59
def prefixEnd_7809009 : Nat := 4983230072969 + 3 ^ 40 * 7809009 * 2
def baseEnd_7809009 : Nat := 16501131902411287860389

theorem tailTrace_7809009 : CollatzResearch.WordTrace tailWord_7809009 prefixEnd_7809009 16501131902411287860389 := by
  unfold tailWord_7809009
  simp only [CollatzResearch.WordTrace]
  refine ⟨284817956966301540403214081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189878637977534360268809387 284817956966301540403214081)
  ·
    refine ⟨213613467724726155302410561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284817956966301540403214081 213613467724726155302410561)
    ·
      refine ⟨160210100793544616476807921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213613467724726155302410561 160210100793544616476807921)
      ·
        refine ⟨120157575595158462357605941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160210100793544616476807921 120157575595158462357605941)
        ·
          refine ⟨11264772712046105846025557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120157575595158462357605941 11264772712046105846025557)
          ·
            refine ⟨16501131902411287860389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11264772712046105846025557 16501131902411287860389)
            ·
              rfl

theorem cell23_7809009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 11].length) (baseStart_7809009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809009 prefixEnd_7809009 := by exact prefixLift 7809009
  have htrace : WordTrace (prefixWord ++ tailWord_7809009) baseStart_7809009 baseEnd_7809009 := by
    simpa [prefixWord, tailWord_7809009, baseEnd_7809009] using wordTrace_append hprefix tailTrace_7809009
  have hstable : (prefixWord ++ tailWord_7809009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809009).length < 2 ^ (prefixWord ++ tailWord_7809009).sum := by decide
  have hdescent : baseEnd_7809009 < baseStart_7809009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809049 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_7809049 : Nat := 118140960795 + 7809049 * 2 ^ 59
def prefixEnd_7809049 : Nat := 4983230072969 + 3 ^ 40 * 7809049 * 2
def baseEnd_7809049 : Nat := 4009795591512122793574343

theorem tailTrace_7809049 : CollatzResearch.WordTrace tailWord_7809049 prefixEnd_7809049 4009795591512122793574343 := by
  unfold tailWord_7809049
  simp only [CollatzResearch.WordTrace]
  refine ⟨284819415886156627234670201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189879610590771084823113467 284819415886156627234670201)
  ·
    refine ⟨213614561914617470426002651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284819415886156627234670201 213614561914617470426002651)
    ·
      refine ⟨320421842871926205639003977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213614561914617470426002651 320421842871926205639003977)
      ·
        refine ⟨240316382153944654229252983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320421842871926205639003977 240316382153944654229252983)
        ·
          refine ⟨360474573230916981343879475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240316382153944654229252983 360474573230916981343879475)
          ·
            refine ⟨540711859846375472015819213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360474573230916981343879475 540711859846375472015819213)
            ·
              refine ⟨202766947442390802005932205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 540711859846375472015819213 202766947442390802005932205)
              ·
                refine ⟨76037605290896550752224577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202766947442390802005932205 76037605290896550752224577)
                ·
                  refine ⟨57028203968172413064168433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76037605290896550752224577 57028203968172413064168433)
                  ·
                    refine ⟨42771152976129309798126325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57028203968172413064168433 42771152976129309798126325)
                    ·
                      refine ⟨4009795591512122793574343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42771152976129309798126325 4009795591512122793574343)
                      ·
                        rfl

theorem cell23_7809049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_7809049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809049 prefixEnd_7809049 := by exact prefixLift 7809049
  have htrace : WordTrace (prefixWord ++ tailWord_7809049) baseStart_7809049 baseEnd_7809049 := by
    simpa [prefixWord, tailWord_7809049, baseEnd_7809049] using wordTrace_append hprefix tailTrace_7809049
  have hstable : (prefixWord ++ tailWord_7809049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809049).length < 2 ^ (prefixWord ++ tailWord_7809049).sum := by decide
  have hdescent : baseEnd_7809049 < baseStart_7809049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809053 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_7809053 : Nat := 118140960795 + 7809053 * 2 ^ 59
def prefixEnd_7809053 : Nat := 4983230072969 + 3 ^ 40 * 7809053 * 2
def baseEnd_7809053 : Nat := 4009797645434740777924325

theorem tailTrace_7809053 : CollatzResearch.WordTrace tailWord_7809053 prefixEnd_7809053 4009797645434740777924325 := by
  unfold tailWord_7809053
  simp only [CollatzResearch.WordTrace]
  refine ⟨284819561778142135917815813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189879707852094757278543875 284819561778142135917815813)
  ·
    refine ⟨53403667833401650484590465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284819561778142135917815813 53403667833401650484590465)
    ·
      refine ⟨40052750875051237863442849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53403667833401650484590465 40052750875051237863442849)
      ·
        refine ⟨30039563156288428397582137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40052750875051237863442849 30039563156288428397582137)
        ·
          refine ⟨22529672367216321298186603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30039563156288428397582137 22529672367216321298186603)
          ·
            refine ⟨33794508550824481947279905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22529672367216321298186603 33794508550824481947279905)
            ·
              refine ⟨25345881413118361460459929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33794508550824481947279905 25345881413118361460459929)
              ·
                refine ⟨19009411059838771095344947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25345881413118361460459929 19009411059838771095344947)
                ·
                  refine ⟨28514116589758156643017421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19009411059838771095344947 28514116589758156643017421)
                  ·
                    refine ⟨10692793721159308741131533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28514116589758156643017421 10692793721159308741131533)
                    ·
                      refine ⟨4009797645434740777924325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10692793721159308741131533 4009797645434740777924325)
                      ·
                        rfl

theorem cell23_7809053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_7809053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809053 prefixEnd_7809053 := by exact prefixLift 7809053
  have htrace : WordTrace (prefixWord ++ tailWord_7809053) baseStart_7809053 baseEnd_7809053 := by
    simpa [prefixWord, tailWord_7809053, baseEnd_7809053] using wordTrace_append hprefix tailTrace_7809053
  have hstable : (prefixWord ++ tailWord_7809053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809053).length < 2 ^ (prefixWord ++ tailWord_7809053).sum := by decide
  have hdescent : baseEnd_7809053 < baseStart_7809053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809057 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 1, 2, 3]
def baseStart_7809057 : Nat := 118140960795 + 7809057 * 2 ^ 59
def prefixEnd_7809057 : Nat := 4983230072969 + 3 ^ 40 * 7809057 * 2
def baseEnd_7809057 : Nat := 4009799699357358762274307

theorem tailTrace_7809057 : CollatzResearch.WordTrace tailWord_7809057 prefixEnd_7809057 4009799699357358762274307 := by
  unfold tailWord_7809057
  simp only [CollatzResearch.WordTrace]
  refine ⟨284819707670127644600961425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189879805113418429733974283 284819707670127644600961425)
  ·
    refine ⟨213614780752595733450721069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284819707670127644600961425 213614780752595733450721069)
    ·
      refine ⟨80105542782223400044020401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213614780752595733450721069 80105542782223400044020401)
      ·
        refine ⟨60079157086667550033015301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80105542782223400044020401 60079157086667550033015301)
        ·
          refine ⟨11264841953750165631190369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60079157086667550033015301 11264841953750165631190369)
          ·
            refine ⟨8448631465312624223392777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11264841953750165631190369 8448631465312624223392777)
            ·
              refine ⟨6336473598984468167544583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8448631465312624223392777 6336473598984468167544583)
              ·
                refine ⟨9504710398476702251316875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6336473598984468167544583 9504710398476702251316875)
                ·
                  refine ⟨14257065597715053376975313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9504710398476702251316875 14257065597715053376975313)
                  ·
                    refine ⟨10692799198286290032731485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14257065597715053376975313 10692799198286290032731485)
                    ·
                      refine ⟨4009799699357358762274307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10692799198286290032731485 4009799699357358762274307)
                      ·
                        rfl

theorem cell23_7809057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_7809057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809057 prefixEnd_7809057 := by exact prefixLift 7809057
  have htrace : WordTrace (prefixWord ++ tailWord_7809057) baseStart_7809057 baseEnd_7809057 := by
    simpa [prefixWord, tailWord_7809057, baseEnd_7809057] using wordTrace_append hprefix tailTrace_7809057
  have hstable : (prefixWord ++ tailWord_7809057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809057).length < 2 ^ (prefixWord ++ tailWord_7809057).sum := by decide
  have hdescent : baseEnd_7809057 < baseStart_7809057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809064 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 2, 4]
def baseStart_7809064 : Nat := 118140960795 + 7809064 * 2 ^ 59
def prefixEnd_7809064 : Nat := 4983230072969 + 3 ^ 40 * 7809064 * 2
def baseEnd_7809064 : Nat := 1336601097907313411628925

theorem tailTrace_7809064 : CollatzResearch.WordTrace tailWord_7809064 prefixEnd_7809064 1336601097907313411628925 := by
  unfold tailWord_7809064
  simp only [CollatzResearch.WordTrace]
  refine ⟨142409981490551142398233123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189879975320734856530977497 142409981490551142398233123)
  ·
    refine ⟨213614972235826713597349685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142409981490551142398233123 213614972235826713597349685)
    ·
      refine ⟨20026403647108754399751533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213614972235826713597349685 20026403647108754399751533)
      ·
        refine ⟨7509901367665782899906825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20026403647108754399751533 7509901367665782899906825)
        ·
          refine ⟨5632426025749337174930119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7509901367665782899906825 5632426025749337174930119)
          ·
            refine ⟨8448639038624005762395179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632426025749337174930119 8448639038624005762395179)
            ·
              refine ⟨12672958557936008643592769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8448639038624005762395179 12672958557936008643592769)
              ·
                refine ⟨9504718918452006482694577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12672958557936008643592769 9504718918452006482694577)
                ·
                  refine ⟨7128539188839004862020933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9504718918452006482694577 7128539188839004862020933)
                  ·
                    refine ⟨1336601097907313411628925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7128539188839004862020933 1336601097907313411628925)
                    ·
                      rfl

theorem cell23_7809064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_7809064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809064 prefixEnd_7809064 := by exact prefixLift 7809064
  have htrace : WordTrace (prefixWord ++ tailWord_7809064) baseStart_7809064 baseEnd_7809064 := by
    simpa [prefixWord, tailWord_7809064, baseEnd_7809064] using wordTrace_append hprefix tailTrace_7809064
  have hstable : (prefixWord ++ tailWord_7809064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809064).length < 2 ^ (prefixWord ++ tailWord_7809064).sum := by decide
  have hdescent : baseEnd_7809064 < baseStart_7809064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809070 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_7809070 : Nat := 118140960795 + 7809070 * 2 ^ 59
def prefixEnd_7809070 : Nat := 4983230072969 + 3 ^ 40 * 7809070 * 2
def baseEnd_7809070 : Nat := 4009806374605867211411747

theorem tailTrace_7809070 : CollatzResearch.WordTrace tailWord_7809070 prefixEnd_7809070 4009806374605867211411747 := by
  unfold tailWord_7809070
  simp only [CollatzResearch.WordTrace]
  refine ⟨35602522727385068477648083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189880121212720365214123109 35602522727385068477648083)
  ·
    refine ⟨53403784091077602716472125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35602522727385068477648083 53403784091077602716472125)
    ·
      refine ⟨20026419034154101018677047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53403784091077602716472125 20026419034154101018677047)
      ·
        refine ⟨30039628551231151528015571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20026419034154101018677047 30039628551231151528015571)
        ·
          refine ⟨45059442826846727292023357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30039628551231151528015571 45059442826846727292023357)
          ·
            refine ⟨16897291060067522734508759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45059442826846727292023357 16897291060067522734508759)
            ·
              refine ⟨25345936590101284101763139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16897291060067522734508759 25345936590101284101763139)
              ·
                refine ⟨38018904885151926152644709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25345936590101284101763139 38018904885151926152644709)
                ·
                  refine ⟨7128544665965986153620883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38018904885151926152644709 7128544665965986153620883)
                  ·
                    refine ⟨10692816998948979230431325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7128544665965986153620883 10692816998948979230431325)
                    ·
                      refine ⟨4009806374605867211411747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10692816998948979230431325 4009806374605867211411747)
                      ·
                        rfl

theorem cell23_7809070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_7809070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809070 prefixEnd_7809070 := by exact prefixLift 7809070
  have htrace : WordTrace (prefixWord ++ tailWord_7809070) baseStart_7809070 baseEnd_7809070 := by
    simpa [prefixWord, tailWord_7809070, baseEnd_7809070] using wordTrace_append hprefix tailTrace_7809070
  have hstable : (prefixWord ++ tailWord_7809070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809070).length < 2 ^ (prefixWord ++ tailWord_7809070).sum := by decide
  have hdescent : baseEnd_7809070 < baseStart_7809070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809156 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7809156 : Nat := 118140960795 + 7809156 * 2 ^ 59
def prefixEnd_7809156 : Nat := 4983230072969 + 3 ^ 40 * 7809156 * 2
def baseEnd_7809156 : Nat := 4009850533942153874936351

theorem tailTrace_7809156 : CollatzResearch.WordTrace tailWord_7809156 prefixEnd_7809156 4009850533942153874936351 := by
  unfold tailWord_7809156
  simp only [CollatzResearch.WordTrace]
  refine ⟨142411659248384492254407661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189882212331179323005876881 142411659248384492254407661)
  ·
    refine ⟨53404372218144184595402873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142411659248384492254407661 53404372218144184595402873)
    ·
      refine ⟨40053279163608138446552155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53404372218144184595402873 40053279163608138446552155)
      ·
        refine ⟨60079918745412207669828233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40053279163608138446552155 60079918745412207669828233)
        ·
          refine ⟨45059939059059155752371175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60079918745412207669828233 45059939059059155752371175)
          ·
            refine ⟨67589908588588733628556763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45059939059059155752371175 67589908588588733628556763)
            ·
              refine ⟨101384862882883100442835145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67589908588588733628556763 101384862882883100442835145)
              ·
                refine ⟨76038647162162325332126359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101384862882883100442835145 76038647162162325332126359)
                ·
                  refine ⟨114057970743243487998189539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76038647162162325332126359 114057970743243487998189539)
                  ·
                    refine ⟨171086956114865231997284309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114057970743243487998189539 171086956114865231997284309)
                    ·
                      refine ⟨4009850533942153874936351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171086956114865231997284309 4009850533942153874936351)
                      ·
                        rfl

theorem cell23_7809156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7809156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809156 prefixEnd_7809156 := by exact prefixLift 7809156
  have htrace : WordTrace (prefixWord ++ tailWord_7809156) baseStart_7809156 baseEnd_7809156 := by
    simpa [prefixWord, tailWord_7809156, baseEnd_7809156] using wordTrace_append hprefix tailTrace_7809156
  have hstable : (prefixWord ++ tailWord_7809156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809156).length < 2 ^ (prefixWord ++ tailWord_7809156).sum := by decide
  have hdescent : baseEnd_7809156 < baseStart_7809156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809220 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_7809220 : Nat := 118140960795 + 7809220 * 2 ^ 59
def prefixEnd_7809220 : Nat := 4983230072969 + 3 ^ 40 * 7809220 * 2
def baseEnd_7809220 : Nat := 4009883396704041624536057

theorem tailTrace_7809220 : CollatzResearch.WordTrace tailWord_7809220 prefixEnd_7809220 4009883396704041624536057 := by
  unfold tailWord_7809220
  simp only [CollatzResearch.WordTrace]
  refine ⟨142412826384268561719572557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189883768512358082292763409 142412826384268561719572557)
  ·
    refine ⟨53404809894100710644839709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142412826384268561719572557 53404809894100710644839709)
    ·
      refine ⟨20026803710287766491814891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53404809894100710644839709 20026803710287766491814891)
      ·
        refine ⟨30040205565431649737722337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20026803710287766491814891 30040205565431649737722337)
        ·
          refine ⟨22530154174073737303291753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30040205565431649737722337 22530154174073737303291753)
          ·
            refine ⟨16897615630555302977468815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22530154174073737303291753 16897615630555302977468815)
            ·
              refine ⟨25346423445832954466203223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16897615630555302977468815 25346423445832954466203223)
              ·
                refine ⟨38019635168749431699304835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25346423445832954466203223 38019635168749431699304835)
                ·
                  refine ⟨57029452753124147548957253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38019635168749431699304835 57029452753124147548957253)
                  ·
                    refine ⟨10693022391210777665429485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57029452753124147548957253 10693022391210777665429485)
                    ·
                      refine ⟨4009883396704041624536057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10693022391210777665429485 4009883396704041624536057)
                      ·
                        rfl

theorem cell23_7809220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_7809220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809220 prefixEnd_7809220 := by exact prefixLift 7809220
  have htrace : WordTrace (prefixWord ++ tailWord_7809220) baseStart_7809220 baseEnd_7809220 := by
    simpa [prefixWord, tailWord_7809220, baseEnd_7809220] using wordTrace_append hprefix tailTrace_7809220
  have hstable : (prefixWord ++ tailWord_7809220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809220).length < 2 ^ (prefixWord ++ tailWord_7809220).sum := by decide
  have hdescent : baseEnd_7809220 < baseStart_7809220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809240 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 6]
def baseStart_7809240 : Nat := 118140960795 + 7809240 * 2 ^ 59
def prefixEnd_7809240 : Nat := 4983230072969 + 3 ^ 40 * 7809240 * 2
def baseEnd_7809240 : Nat := 445543740701903505142885

theorem tailTrace_7809240 : CollatzResearch.WordTrace tailWord_7809240 prefixEnd_7809240 445543740701903505142885 := by
  unfold tailWord_7809240
  simp only [CollatzResearch.WordTrace]
  refine ⟨142413191114232333427436587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189884254818976444569915449 142413191114232333427436587)
  ·
    refine ⟨213619786671348500141154881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142413191114232333427436587 213619786671348500141154881)
    ·
      refine ⟨160214840003511375105866161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213619786671348500141154881 160214840003511375105866161)
      ·
        refine ⟨120161130002633531329399621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160214840003511375105866161 120161130002633531329399621)
        ·
          refine ⟨22530211875493787124262429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120161130002633531329399621 22530211875493787124262429)
          ·
            refine ⟨8448829453310170171598411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22530211875493787124262429 8448829453310170171598411)
            ·
              refine ⟨12673244179965255257397617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8448829453310170171598411 12673244179965255257397617)
              ·
                refine ⟨9504933134973941443048213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12673244179965255257397617 9504933134973941443048213)
                ·
                  refine ⟨445543740701903505142885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9504933134973941443048213 445543740701903505142885)
                  ·
                    rfl

theorem cell23_7809240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 6].length) (baseStart_7809240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809240 prefixEnd_7809240 := by exact prefixLift 7809240
  have htrace : WordTrace (prefixWord ++ tailWord_7809240) baseStart_7809240 baseEnd_7809240 := by
    simpa [prefixWord, tailWord_7809240, baseEnd_7809240] using wordTrace_append hprefix tailTrace_7809240
  have hstable : (prefixWord ++ tailWord_7809240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809240).length < 2 ^ (prefixWord ++ tailWord_7809240).sum := by decide
  have hdescent : baseEnd_7809240 < baseStart_7809240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809243 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 3, 5, 2]
def baseStart_7809243 : Nat := 118140960795 + 7809243 * 2 ^ 59
def prefixEnd_7809243 : Nat := 4983230072969 + 3 ^ 40 * 7809243 * 2
def baseEnd_7809243 : Nat := 4009895206759095034548451

theorem tailTrace_7809243 : CollatzResearch.WordTrace tailWord_7809243 prefixEnd_7809243 4009895206759095034548451 := by
  unfold tailWord_7809243
  simp only [CollatzResearch.WordTrace]
  refine ⟨284826491647453798367232383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189884327764969198911488255 284826491647453798367232383)
  ·
    refine ⟨427239737471180697550848575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284826491647453798367232383 427239737471180697550848575)
    ·
      refine ⟨640859606206771046326272863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427239737471180697550848575 640859606206771046326272863)
      ·
        refine ⟨961289409310156569489409295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640859606206771046326272863 961289409310156569489409295)
        ·
          refine ⟨1441934113965234854234113943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961289409310156569489409295 1441934113965234854234113943)
          ·
            refine ⟨2162901170947852281351170915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441934113965234854234113943 2162901170947852281351170915)
            ·
              refine ⟨3244351756421778422026756373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162901170947852281351170915 3244351756421778422026756373)
              ·
                refine ⟨152078988582270863532504205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3244351756421778422026756373 152078988582270863532504205)
                ·
                  refine ⟨57029620718351573824689077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152078988582270863532504205 57029620718351573824689077)
                  ·
                    refine ⟨5346526942345460046064601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57029620718351573824689077 5346526942345460046064601)
                    ·
                      refine ⟨4009895206759095034548451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5346526942345460046064601 4009895206759095034548451)
                      ·
                        rfl

theorem cell23_7809243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 5, 2].length) (baseStart_7809243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809243 prefixEnd_7809243 := by exact prefixLift 7809243
  have htrace : WordTrace (prefixWord ++ tailWord_7809243) baseStart_7809243 baseEnd_7809243 := by
    simpa [prefixWord, tailWord_7809243, baseEnd_7809243] using wordTrace_append hprefix tailTrace_7809243
  have hstable : (prefixWord ++ tailWord_7809243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809243).length < 2 ^ (prefixWord ++ tailWord_7809243).sum := by decide
  have hdescent : baseEnd_7809243 < baseStart_7809243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809244 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_7809244 : Nat := 118140960795 + 7809244 * 2 ^ 59
def prefixEnd_7809244 : Nat := 4983230072969 + 3 ^ 40 * 7809244 * 2
def baseEnd_7809244 : Nat := 1336631906746583176878649

theorem tailTrace_7809244 : CollatzResearch.WordTrace tailWord_7809244 prefixEnd_7809244 1336631906746583176878649 := by
  unfold tailWord_7809244
  simp only [CollatzResearch.WordTrace]
  refine ⟨142413264060225087769009393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189884352080300117025345857 142413264060225087769009393)
  ·
    refine ⟨106809948045168815826757045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142413264060225087769009393 106809948045168815826757045)
    ·
      refine ⟨10013432629234576483758473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106809948045168815826757045 10013432629234576483758473)
      ·
        refine ⟨7510074471925932362818855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10013432629234576483758473 7510074471925932362818855)
        ·
          refine ⟨11265111707888898544228283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7510074471925932362818855 11265111707888898544228283)
          ·
            refine ⟨16897667561833347816342425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11265111707888898544228283 16897667561833347816342425)
            ·
              refine ⟨12673250671375010862256819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16897667561833347816342425 12673250671375010862256819)
              ·
                refine ⟨19009876007062516293385229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12673250671375010862256819 19009876007062516293385229)
                ·
                  refine ⟨7128703502648443610019461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19009876007062516293385229 7128703502648443610019461)
                  ·
                    refine ⟨1336631906746583176878649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7128703502648443610019461 1336631906746583176878649)
                    ·
                      rfl

theorem cell23_7809244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_7809244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809244 prefixEnd_7809244 := by exact prefixLift 7809244
  have htrace : WordTrace (prefixWord ++ tailWord_7809244) baseStart_7809244 baseEnd_7809244 := by
    simpa [prefixWord, tailWord_7809244, baseEnd_7809244] using wordTrace_append hprefix tailTrace_7809244
  have hstable : (prefixWord ++ tailWord_7809244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809244).length < 2 ^ (prefixWord ++ tailWord_7809244).sum := by decide
  have hdescent : baseEnd_7809244 < baseStart_7809244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809270 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_7809270 : Nat := 118140960795 + 7809270 * 2 ^ 59
def prefixEnd_7809270 : Nat := 4983230072969 + 3 ^ 40 * 7809270 * 2
def baseEnd_7809270 : Nat := 1336636356912255476303609

theorem tailTrace_7809270 : CollatzResearch.WordTrace tailWord_7809270 prefixEnd_7809270 1336636356912255476303609 := by
  unfold tailWord_7809270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17801717276147248873654079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189884984278903987985643509 17801717276147248873654079)
  ·
    refine ⟨26702575914220873310481119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17801717276147248873654079 26702575914220873310481119)
    ·
      refine ⟨40053863871331309965721679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26702575914220873310481119 40053863871331309965721679)
      ·
        refine ⟨60080795806996964948582519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40053863871331309965721679 60080795806996964948582519)
        ·
          refine ⟨90121193710495447422873779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60080795806996964948582519 90121193710495447422873779)
          ·
            refine ⟨135181790565743171134310669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90121193710495447422873779 135181790565743171134310669)
            ·
              refine ⟨50693171462153689175366501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135181790565743171134310669 50693171462153689175366501)
              ·
                refine ⟨9504969649153816720381219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50693171462153689175366501 9504969649153816720381219)
                ·
                  refine ⟨14257454473730725080571829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9504969649153816720381219 14257454473730725080571829)
                  ·
                    refine ⟨1336636356912255476303609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14257454473730725080571829 1336636356912255476303609)
                    ·
                      rfl

theorem cell23_7809270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_7809270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809270 prefixEnd_7809270 := by exact prefixLift 7809270
  have htrace : WordTrace (prefixWord ++ tailWord_7809270) baseStart_7809270 baseEnd_7809270 := by
    simpa [prefixWord, tailWord_7809270, baseEnd_7809270] using wordTrace_append hprefix tailTrace_7809270
  have hstable : (prefixWord ++ tailWord_7809270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809270).length < 2 ^ (prefixWord ++ tailWord_7809270).sum := by decide
  have hdescent : baseEnd_7809270 < baseStart_7809270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809283 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 6, 4]
def baseStart_7809283 : Nat := 118140960795 + 7809283 * 2 ^ 59
def prefixEnd_7809283 : Nat := 4983230072969 + 3 ^ 40 * 7809283 * 2
def baseEnd_7809283 : Nat := 1336638581995091626016089

theorem tailTrace_7809283 : CollatzResearch.WordTrace tailWord_7809283 prefixEnd_7809283 1336638581995091626016089 := by
  unfold tailWord_7809283
  simp only [CollatzResearch.WordTrace]
  refine ⟨284827950567308885198688503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189885300378205923465792335 284827950567308885198688503)
  ·
    refine ⟨427241925850963327798032755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284827950567308885198688503 427241925850963327798032755)
    ·
      refine ⟨640862888776444991697049133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427241925850963327798032755 640862888776444991697049133)
      ·
        refine ⟨240323583291166871886393425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640862888776444991697049133 240323583291166871886393425)
        ·
          refine ⟨180242687468375153914795069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240323583291166871886393425 180242687468375153914795069)
          ·
            refine ⟨67591007800640682718048151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180242687468375153914795069 67591007800640682718048151)
            ·
              refine ⟨101386511700961024077072227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67591007800640682718048151 101386511700961024077072227)
              ·
                refine ⟨152079767551441536115608341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101386511700961024077072227 152079767551441536115608341)
                ·
                  refine ⟨7128739103973822005419141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152079767551441536115608341 7128739103973822005419141)
                  ·
                    refine ⟨1336638581995091626016089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7128739103973822005419141 1336638581995091626016089)
                    ·
                      rfl

theorem cell23_7809283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 4].length) (baseStart_7809283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809283 prefixEnd_7809283 := by exact prefixLift 7809283
  have htrace : WordTrace (prefixWord ++ tailWord_7809283) baseStart_7809283 baseEnd_7809283 := by
    simpa [prefixWord, tailWord_7809283, baseEnd_7809283] using wordTrace_append hprefix tailTrace_7809283
  have hstable : (prefixWord ++ tailWord_7809283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809283).length < 2 ^ (prefixWord ++ tailWord_7809283).sum := by decide
  have hdescent : baseEnd_7809283 < baseStart_7809283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809290 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_7809290 : Nat := 118140960795 + 7809290 * 2 ^ 59
def prefixEnd_7809290 : Nat := 4983230072969 + 3 ^ 40 * 7809290 * 2
def baseEnd_7809290 : Nat := 4009919340349856350660735

theorem tailTrace_7809290 : CollatzResearch.WordTrace tailWord_7809290 prefixEnd_7809290 4009919340349856350660735 := by
  unfold tailWord_7809290
  simp only [CollatzResearch.WordTrace]
  refine ⟨71207051469570881348548331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189885470585522350262795549 71207051469570881348548331)
  ·
    refine ⟨106810577204356322022822497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71207051469570881348548331 106810577204356322022822497)
    ·
      refine ⟨80107932903267241517116873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106810577204356322022822497 80107932903267241517116873)
      ·
        refine ⟨60080949677450431137837655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80107932903267241517116873 60080949677450431137837655)
        ·
          refine ⟨90121424516175646706756483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60080949677450431137837655 90121424516175646706756483)
          ·
            refine ⟨135182136774263470060134725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90121424516175646706756483 135182136774263470060134725)
            ·
              refine ⟨25346650645174400636275261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135182136774263470060134725 25346650645174400636275261)
              ·
                refine ⟨9504993991940400238603223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25346650645174400636275261 9504993991940400238603223)
                ·
                  refine ⟨14257490987910600357904835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9504993991940400238603223 14257490987910600357904835)
                  ·
                    refine ⟨21386236481865900536857253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14257490987910600357904835 21386236481865900536857253)
                    ·
                      refine ⟨4009919340349856350660735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21386236481865900536857253 4009919340349856350660735)
                      ·
                        rfl

theorem cell23_7809290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_7809290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809290 prefixEnd_7809290 := by exact prefixLift 7809290
  have htrace : WordTrace (prefixWord ++ tailWord_7809290) baseStart_7809290 baseEnd_7809290 := by
    simpa [prefixWord, tailWord_7809290, baseEnd_7809290] using wordTrace_append hprefix tailTrace_7809290
  have hstable : (prefixWord ++ tailWord_7809290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809290).length < 2 ^ (prefixWord ++ tailWord_7809290).sum := by decide
  have hdescent : baseEnd_7809290 < baseStart_7809290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809303 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_7809303 : Nat := 118140960795 + 7809303 * 2 ^ 59
def prefixEnd_7809303 : Nat := 4983230072969 + 3 ^ 40 * 7809303 * 2
def baseEnd_7809303 : Nat := 4009926015598364799798175

theorem tailTrace_7809303 : CollatzResearch.WordTrace tailWord_7809303 prefixEnd_7809303 4009926015598364799798175 := by
  unfold tailWord_7809303
  simp only [CollatzResearch.WordTrace]
  refine ⟨284828680027236428614416563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189885786684824285742944375 284828680027236428614416563)
  ·
    refine ⟨427243020040854642921624845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284828680027236428614416563 427243020040854642921624845)
    ·
      refine ⟨160216132515320491095609317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427243020040854642921624845 160216132515320491095609317)
      ·
        refine ⟨30040524846622592080426747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160216132515320491095609317 30040524846622592080426747)
        ·
          refine ⟨45060787269933888120640121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30040524846622592080426747 45060787269933888120640121)
          ·
            refine ⟨33795590452450416090480091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45060787269933888120640121 33795590452450416090480091)
            ·
              refine ⟨50693385678675624135720137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33795590452450416090480091 50693385678675624135720137)
              ·
                refine ⟨38020039259006718101790103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50693385678675624135720137 38020039259006718101790103)
                ·
                  refine ⟨57030058888510077152685155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38020039259006718101790103 57030058888510077152685155)
                  ·
                    refine ⟨85545088332765115729027733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57030058888510077152685155 85545088332765115729027733)
                    ·
                      refine ⟨4009926015598364799798175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85545088332765115729027733 4009926015598364799798175)
                      ·
                        rfl

theorem cell23_7809303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_7809303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809303 prefixEnd_7809303 := by exact prefixLift 7809303
  have htrace : WordTrace (prefixWord ++ tailWord_7809303) baseStart_7809303 baseEnd_7809303 := by
    simpa [prefixWord, tailWord_7809303, baseEnd_7809303] using wordTrace_append hprefix tailTrace_7809303
  have hstable : (prefixWord ++ tailWord_7809303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809303).length < 2 ^ (prefixWord ++ tailWord_7809303).sum := by decide
  have hdescent : baseEnd_7809303 < baseStart_7809303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809307 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 3, 2, 2]
def baseStart_7809307 : Nat := 118140960795 + 7809307 * 2 ^ 59
def prefixEnd_7809307 : Nat := 4983230072969 + 3 ^ 40 * 7809307 * 2
def baseEnd_7809307 : Nat := 4009928069520982784148157

theorem tailTrace_7809307 : CollatzResearch.WordTrace tailWord_7809307 prefixEnd_7809307 4009928069520982784148157 := by
  unfold tailWord_7809307
  simp only [CollatzResearch.WordTrace]
  refine ⟨284828825919221937297562175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189885883946147958198374783 284828825919221937297562175)
  ·
    refine ⟨427243238878832905946343263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284828825919221937297562175 427243238878832905946343263)
    ·
      refine ⟨640864858318249358919514895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427243238878832905946343263 640864858318249358919514895)
      ·
        refine ⟨961297287477374038379272343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640864858318249358919514895 961297287477374038379272343)
        ·
          refine ⟨1441945931216061057568908515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961297287477374038379272343 1441945931216061057568908515)
          ·
            refine ⟨2162918896824091586353362773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441945931216061057568908515 2162918896824091586353362773)
            ·
              refine ⟨12673352911078661638789235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2162918896824091586353362773 12673352911078661638789235)
              ·
                refine ⟨19010029366617992458183853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12673352911078661638789235 19010029366617992458183853)
                ·
                  refine ⟨7128761012481747171818945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19010029366617992458183853 7128761012481747171818945)
                  ·
                    refine ⟨5346570759361310378864209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7128761012481747171818945 5346570759361310378864209)
                    ·
                      refine ⟨4009928069520982784148157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5346570759361310378864209 4009928069520982784148157)
                      ·
                        rfl

theorem cell23_7809307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 2, 2].length) (baseStart_7809307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809307 prefixEnd_7809307 := by exact prefixLift 7809307
  have htrace : WordTrace (prefixWord ++ tailWord_7809307) baseStart_7809307 baseEnd_7809307 := by
    simpa [prefixWord, tailWord_7809307, baseEnd_7809307] using wordTrace_append hprefix tailTrace_7809307
  have hstable : (prefixWord ++ tailWord_7809307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809307).length < 2 ^ (prefixWord ++ tailWord_7809307).sum := by decide
  have hdescent : baseEnd_7809307 < baseStart_7809307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809317 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_7809317 : Nat := 118140960795 + 7809317 * 2 ^ 59
def prefixEnd_7809317 : Nat := 4983230072969 + 3 ^ 40 * 7809317 * 2
def baseEnd_7809317 : Nat := 1336644401442509248341037

theorem tailTrace_7809317 : CollatzResearch.WordTrace tailWord_7809317 prefixEnd_7809317 1336644401442509248341037 := by
  unfold tailWord_7809317
  simp only [CollatzResearch.WordTrace]
  refine ⟨284829190649185709005426205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189886127099457139336950803 284829190649185709005426205)
  ·
    refine ⟨106810946493444640877034827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284829190649185709005426205 106810946493444640877034827)
    ·
      refine ⟨160216419740166961315552241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106810946493444640877034827 160216419740166961315552241)
      ·
        refine ⟨120162314805125220986664181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160216419740166961315552241 120162314805125220986664181)
        ·
          refine ⟨11265217012980489467499767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120162314805125220986664181 11265217012980489467499767)
          ·
            refine ⟨16897825519470734201249651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11265217012980489467499767 16897825519470734201249651)
            ·
              refine ⟨25346738279206101301874477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16897825519470734201249651 25346738279206101301874477)
              ·
                refine ⟨9505026854702287988202929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25346738279206101301874477 9505026854702287988202929)
                ·
                  refine ⟨7128770141026715991152197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9505026854702287988202929 7128770141026715991152197)
                  ·
                    refine ⟨1336644401442509248341037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7128770141026715991152197 1336644401442509248341037)
                    ·
                      rfl

theorem cell23_7809317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_7809317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809317 prefixEnd_7809317 := by exact prefixLift 7809317
  have htrace : WordTrace (prefixWord ++ tailWord_7809317) baseStart_7809317 baseEnd_7809317 := by
    simpa [prefixWord, tailWord_7809317, baseEnd_7809317] using wordTrace_append hprefix tailTrace_7809317
  have hstable : (prefixWord ++ tailWord_7809317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809317).length < 2 ^ (prefixWord ++ tailWord_7809317).sum := by decide
  have hdescent : baseEnd_7809317 < baseStart_7809317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809340 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_7809340 : Nat := 118140960795 + 7809340 * 2 ^ 59
def prefixEnd_7809340 : Nat := 4983230072969 + 3 ^ 40 * 7809340 * 2
def baseEnd_7809340 : Nat := 4009945014382581155035505

theorem tailTrace_7809340 : CollatzResearch.WordTrace tailWord_7809340 prefixEnd_7809340 4009945014382581155035505 := by
  unfold tailWord_7809340
  simp only [CollatzResearch.WordTrace]
  refine ⟨142415014764051191966756737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189886686352068255955675649 142415014764051191966756737)
  ·
    refine ⟨106811261073038393975067553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142415014764051191966756737 106811261073038393975067553)
    ·
      refine ⟨80108445804778795481300665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106811261073038393975067553 80108445804778795481300665)
      ·
        refine ⟨60081334353584096610975499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80108445804778795481300665 60081334353584096610975499)
        ·
          refine ⟨90122001530376144916463249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60081334353584096610975499 90122001530376144916463249)
          ·
            refine ⟨67591501147782108687347437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90122001530376144916463249 67591501147782108687347437)
            ·
              refine ⟨25346812930418290757755289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67591501147782108687347437 25346812930418290757755289)
              ·
                refine ⟨19010109697813718068316467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25346812930418290757755289 19010109697813718068316467)
                ·
                  refine ⟨28515164546720577102474701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19010109697813718068316467 28515164546720577102474701)
                  ·
                    refine ⟨10693186705020216413428013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28515164546720577102474701 10693186705020216413428013)
                    ·
                      refine ⟨4009945014382581155035505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10693186705020216413428013 4009945014382581155035505)
                      ·
                        rfl

theorem cell23_7809340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_7809340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809340 prefixEnd_7809340 := by exact prefixLift 7809340
  have htrace : WordTrace (prefixWord ++ tailWord_7809340) baseStart_7809340 baseEnd_7809340 := by
    simpa [prefixWord, tailWord_7809340, baseEnd_7809340] using wordTrace_append hprefix tailTrace_7809340
  have hstable : (prefixWord ++ tailWord_7809340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809340).length < 2 ^ (prefixWord ++ tailWord_7809340).sum := by decide
  have hdescent : baseEnd_7809340 < baseStart_7809340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809393 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_7809393 : Nat := 118140960795 + 7809393 * 2 ^ 59
def prefixEnd_7809393 : Nat := 4983230072969 + 3 ^ 40 * 7809393 * 2
def baseEnd_7809393 : Nat := 4009972228857269447672761

theorem tailTrace_7809393 : CollatzResearch.WordTrace tailWord_7809393 prefixEnd_7809393 4009972228857269447672761 := by
  unfold tailWord_7809393
  simp only [CollatzResearch.WordTrace]
  refine ⟨284831962596910373985192833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189887975064606915990128555 284831962596910373985192833)
  ·
    refine ⟨213623971947682780488894625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284831962596910373985192833 213623971947682780488894625)
    ·
      refine ⟨160217978960762085366670969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213623971947682780488894625 160217978960762085366670969)
      ·
        refine ⟨120163484220571564025003227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160217978960762085366670969 120163484220571564025003227)
        ·
          refine ⟨180245226330857346037504841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120163484220571564025003227 180245226330857346037504841)
          ·
            refine ⟨135183919748143009528128631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180245226330857346037504841 135183919748143009528128631)
            ·
              refine ⟨202775879622214514292192947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135183919748143009528128631 202775879622214514292192947)
              ·
                refine ⟨304163819433321771438289421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202775879622214514292192947 304163819433321771438289421)
                ·
                  refine ⟨114061432287495664289358533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304163819433321771438289421 114061432287495664289358533)
                  ·
                    refine ⟨21386518553905437054254725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114061432287495664289358533 21386518553905437054254725)
                    ·
                      refine ⟨4009972228857269447672761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21386518553905437054254725 4009972228857269447672761)
                      ·
                        rfl

theorem cell23_7809393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_7809393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809393 prefixEnd_7809393 := by exact prefixLift 7809393
  have htrace : WordTrace (prefixWord ++ tailWord_7809393) baseStart_7809393 baseEnd_7809393 := by
    simpa [prefixWord, tailWord_7809393, baseEnd_7809393] using wordTrace_append hprefix tailTrace_7809393
  have hstable : (prefixWord ++ tailWord_7809393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809393).length < 2 ^ (prefixWord ++ tailWord_7809393).sum := by decide
  have hdescent : baseEnd_7809393 < baseStart_7809393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809420 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 7]
def baseStart_7809420 : Nat := 118140960795 + 7809420 * 2 ^ 59
def prefixEnd_7809420 : Nat := 4983230072969 + 3 ^ 40 * 7809420 * 2
def baseEnd_7809420 : Nat := 445554010314993426892793

theorem tailTrace_7809420 : CollatzResearch.WordTrace tailWord_7809420 prefixEnd_7809420 445554010314993426892793 := by
  unfold tailWord_7809420
  simp only [CollatzResearch.WordTrace]
  refine ⟨142416473683906278798212857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189888631578541705064283809 142416473683906278798212857)
  ·
    refine ⟨106812355262929709098659643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142416473683906278798212857 106812355262929709098659643)
    ·
      refine ⟨160218532894394563647989465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106812355262929709098659643 160218532894394563647989465)
      ·
        refine ⟨120163899670795922735992099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160218532894394563647989465 120163899670795922735992099)
        ·
          refine ⟨180245849506193884103988149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120163899670795922735992099 180245849506193884103988149)
          ·
            refine ⟨16898048391205676634748889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180245849506193884103988149 16898048391205676634748889)
            ·
              refine ⟨12673536293404257476061667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16898048391205676634748889 12673536293404257476061667)
              ·
                refine ⟨19010304440106386214092501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12673536293404257476061667 19010304440106386214092501)
                ·
                  refine ⟨445554010314993426892793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19010304440106386214092501 445554010314993426892793)
                  ·
                    rfl

theorem cell23_7809420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_7809420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809420 prefixEnd_7809420 := by exact prefixLift 7809420
  have htrace : WordTrace (prefixWord ++ tailWord_7809420) baseStart_7809420 baseEnd_7809420 := by
    simpa [prefixWord, tailWord_7809420, baseEnd_7809420] using wordTrace_append hprefix tailTrace_7809420
  have hstable : (prefixWord ++ tailWord_7809420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809420).length < 2 ^ (prefixWord ++ tailWord_7809420).sum := by decide
  have hdescent : baseEnd_7809420 < baseStart_7809420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809433 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 3, 7]
def baseStart_7809433 : Nat := 118140960795 + 7809433 * 2 ^ 59
def prefixEnd_7809433 : Nat := 4983230072969 + 3 ^ 40 * 7809433 * 2
def baseEnd_7809433 : Nat := 1336664256027816430390859

theorem tailTrace_7809433 : CollatzResearch.WordTrace tailWord_7809433 prefixEnd_7809433 1336664256027816430390859 := by
  unfold tailWord_7809433
  simp only [CollatzResearch.WordTrace]
  refine ⟨284833421516765460816648953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189888947677843640544432635 284833421516765460816648953)
  ·
    refine ⟨213625066137574095612486715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284833421516765460816648953 213625066137574095612486715)
    ·
      refine ⟨320437599206361143418730073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213625066137574095612486715 320437599206361143418730073)
      ·
        refine ⟨240328199404770857564047555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320437599206361143418730073 240328199404770857564047555)
        ·
          refine ⟨360492299107156286346071333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240328199404770857564047555 360492299107156286346071333)
          ·
            refine ⟨67592306082591803689888375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360492299107156286346071333 67592306082591803689888375)
            ·
              refine ⟨101388459123887705534832563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67592306082591803689888375 101388459123887705534832563)
              ·
                refine ⟨152082688685831558302248845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101388459123887705534832563 152082688685831558302248845)
                ·
                  refine ⟨57031008257186834363343317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152082688685831558302248845 57031008257186834363343317)
                  ·
                    refine ⟨1336664256027816430390859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57031008257186834363343317 1336664256027816430390859)
                    ·
                      rfl

theorem cell23_7809433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_7809433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809433 prefixEnd_7809433 := by exact prefixLift 7809433
  have htrace : WordTrace (prefixWord ++ tailWord_7809433) baseStart_7809433 baseEnd_7809433 := by
    simpa [prefixWord, tailWord_7809433, baseEnd_7809433] using wordTrace_append hprefix tailTrace_7809433
  have hstable : (prefixWord ++ tailWord_7809433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809433).length < 2 ^ (prefixWord ++ tailWord_7809433).sum := by decide
  have hdescent : baseEnd_7809433 < baseStart_7809433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809557 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_7809557 : Nat := 118140960795 + 7809557 * 2 ^ 59
def prefixEnd_7809557 : Nat := 4983230072969 + 3 ^ 40 * 7809557 * 2
def baseEnd_7809557 : Nat := 1336685479894868935340669

theorem tailTrace_7809557 : CollatzResearch.WordTrace tailWord_7809557 prefixEnd_7809557 1336685479894868935340669 := by
  unfold tailWord_7809557
  simp only [CollatzResearch.WordTrace]
  refine ⟨284837944168316229994162925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189891962778877486662775283 284837944168316229994162925)
  ·
    refine ⟨106814229063118586247811097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284837944168316229994162925 106814229063118586247811097)
    ·
      refine ⟨80110671797338939685858323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106814229063118586247811097 80110671797338939685858323)
      ·
        refine ⟨120166007696008409528787485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80110671797338939685858323 120166007696008409528787485)
        ·
          refine ⟨45062252886003153573295307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120166007696008409528787485 45062252886003153573295307)
          ·
            refine ⟨67593379329004730359942961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45062252886003153573295307 67593379329004730359942961)
            ·
              refine ⟨50695034496753547769957221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67593379329004730359942961 50695034496753547769957221)
              ·
                refine ⟨9505318968141290206866979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50695034496753547769957221 9505318968141290206866979)
                ·
                  refine ⟨14257978452211935310300469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9505318968141290206866979 14257978452211935310300469)
                  ·
                    refine ⟨1336685479894868935340669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14257978452211935310300469 1336685479894868935340669)
                    ·
                      rfl

theorem cell23_7809557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_7809557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809557 prefixEnd_7809557 := by exact prefixLift 7809557
  have htrace : WordTrace (prefixWord ++ tailWord_7809557) baseStart_7809557 baseEnd_7809557 := by
    simpa [prefixWord, tailWord_7809557, baseEnd_7809557] using wordTrace_append hprefix tailTrace_7809557
  have hstable : (prefixWord ++ tailWord_7809557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809557).length < 2 ^ (prefixWord ++ tailWord_7809557).sum := by decide
  have hdescent : baseEnd_7809557 < baseStart_7809557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809564 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_7809564 : Nat := 118140960795 + 7809564 * 2 ^ 59
def prefixEnd_7809564 : Nat := 4983230072969 + 3 ^ 40 * 7809564 * 2
def baseEnd_7809564 : Nat := 4010060034049188278634475

theorem tailTrace_7809564 : CollatzResearch.WordTrace tailWord_7809564 prefixEnd_7809564 4010060034049188278634475 := by
  unfold tailWord_7809564
  simp only [CollatzResearch.WordTrace]
  refine ⟨142419099739645435094833873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189892132986193913459778497 142419099739645435094833873)
  ·
    refine ⟨106814324804734076321125405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142419099739645435094833873 106814324804734076321125405)
    ·
      refine ⟨40055371801775278620422027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106814324804734076321125405 40055371801775278620422027)
      ·
        refine ⟨60083057702662917930633041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40055371801775278620422027 60083057702662917930633041)
        ·
          refine ⟨45062293276997188447974781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60083057702662917930633041 45062293276997188447974781)
          ·
            refine ⟨16898359978873945667990543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45062293276997188447974781 16898359978873945667990543)
            ·
              refine ⟨25347539968310918501985815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16898359978873945667990543 25347539968310918501985815)
              ·
                refine ⟨38021309952466377752978723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25347539968310918501985815 38021309952466377752978723)
                ·
                  refine ⟨57031964928699566629468085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38021309952466377752978723 57031964928699566629468085)
                  ·
                    refine ⟨5346746712065584371512633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57031964928699566629468085 5346746712065584371512633)
                    ·
                      refine ⟨4010060034049188278634475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5346746712065584371512633 4010060034049188278634475)
                      ·
                        rfl

theorem cell23_7809564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_7809564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809564 prefixEnd_7809564 := by exact prefixLift 7809564
  have htrace : WordTrace (prefixWord ++ tailWord_7809564) baseStart_7809564 baseEnd_7809564 := by
    simpa [prefixWord, tailWord_7809564, baseEnd_7809564] using wordTrace_append hprefix tailTrace_7809564
  have hstable : (prefixWord ++ tailWord_7809564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809564).length < 2 ^ (prefixWord ++ tailWord_7809564).sum := by decide
  have hdescent : baseEnd_7809564 < baseStart_7809564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809571 : List Nat := [1, 1, 1, 4, 4, 1, 1, 5, 1, 1, 3]
def baseStart_7809571 : Nat := 118140960795 + 7809571 * 2 ^ 59
def prefixEnd_7809571 : Nat := 4983230072969 + 3 ^ 40 * 7809571 * 2
def baseEnd_7809571 : Nat := 4010063628413769751246943

theorem tailTrace_7809571 : CollatzResearch.WordTrace tailWord_7809571 prefixEnd_7809571 4010063628413769751246943 := by
  unfold tailWord_7809571
  simp only [CollatzResearch.WordTrace]
  refine ⟨284838454790265510385172567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189892303193510340256781711 284838454790265510385172567)
  ·
    refine ⟨427257682185398265577758851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284838454790265510385172567 427257682185398265577758851)
    ·
      refine ⟨640886523278097398366638277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427257682185398265577758851 640886523278097398366638277)
      ·
        refine ⟨120166223114643262193744677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 640886523278097398366638277 120166223114643262193744677)
        ·
          refine ⟨22531166833995611661327127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120166223114643262193744677 22531166833995611661327127)
          ·
            refine ⟨33796750250993417491990691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22531166833995611661327127 33796750250993417491990691)
            ·
              refine ⟨50695125376490126237986037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33796750250993417491990691 50695125376490126237986037)
              ·
                refine ⟨4752668004045949334811191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50695125376490126237986037 4752668004045949334811191)
                ·
                  refine ⟨7129002006068924002216787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752668004045949334811191 7129002006068924002216787)
                  ·
                    refine ⟨10693503009103386003325181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7129002006068924002216787 10693503009103386003325181)
                    ·
                      refine ⟨4010063628413769751246943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10693503009103386003325181 4010063628413769751246943)
                      ·
                        rfl

theorem cell23_7809571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_7809571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809571 prefixEnd_7809571 := by exact prefixLift 7809571
  have htrace : WordTrace (prefixWord ++ tailWord_7809571) baseStart_7809571 baseEnd_7809571 := by
    simpa [prefixWord, tailWord_7809571, baseEnd_7809571] using wordTrace_append hprefix tailTrace_7809571
  have hstable : (prefixWord ++ tailWord_7809571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809571).length < 2 ^ (prefixWord ++ tailWord_7809571).sum := by decide
  have hdescent : baseEnd_7809571 < baseStart_7809571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809580 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_7809580 : Nat := 118140960795 + 7809580 * 2 ^ 59
def prefixEnd_7809580 : Nat := 4983230072969 + 3 ^ 40 * 7809580 * 2
def baseEnd_7809580 : Nat := 4010068249739660216034401

theorem tailTrace_7809580 : CollatzResearch.WordTrace tailWord_7809580 prefixEnd_7809580 4010068249739660216034401 := by
  unfold tailWord_7809580
  simp only [CollatzResearch.WordTrace]
  refine ⟨142419391523616452461125097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189892522031488603281500129 142419391523616452461125097)
  ·
    refine ⟨106814543642712339345843823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142419391523616452461125097 106814543642712339345843823)
    ·
      refine ⟨160221815464068509018765735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106814543642712339345843823 160221815464068509018765735)
      ·
        refine ⟨240332723196102763528148603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160221815464068509018765735 240332723196102763528148603)
        ·
          refine ⟨360499084794154145292222905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240332723196102763528148603 360499084794154145292222905)
          ·
            refine ⟨270374313595615608969167179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360499084794154145292222905 270374313595615608969167179)
            ·
              refine ⟨405561470393423413453750769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270374313595615608969167179 405561470393423413453750769)
              ·
                refine ⟨304171102795067560090313077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405561470393423413453750769 304171102795067560090313077)
                ·
                  refine ⟨28516040887037583758466851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304171102795067560090313077 28516040887037583758466851)
                  ·
                    refine ⟨42774061330556375637700277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28516040887037583758466851 42774061330556375637700277)
                    ·
                      refine ⟨4010068249739660216034401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42774061330556375637700277 4010068249739660216034401)
                      ·
                        rfl

theorem cell23_7809580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_7809580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809580 prefixEnd_7809580 := by exact prefixLift 7809580
  have htrace : WordTrace (prefixWord ++ tailWord_7809580) baseStart_7809580 baseEnd_7809580 := by
    simpa [prefixWord, tailWord_7809580, baseEnd_7809580] using wordTrace_append hprefix tailTrace_7809580
  have hstable : (prefixWord ++ tailWord_7809580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809580).length < 2 ^ (prefixWord ++ tailWord_7809580).sum := by decide
  have hdescent : baseEnd_7809580 < baseStart_7809580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809587 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 4, 4]
def baseStart_7809587 : Nat := 118140960795 + 7809587 * 2 ^ 59
def prefixEnd_7809587 : Nat := 4983230072969 + 3 ^ 40 * 7809587 * 2
def baseEnd_7809587 : Nat := 1336690614701413896215623

theorem tailTrace_7809587 : CollatzResearch.WordTrace tailWord_7809587 prefixEnd_7809587 1336690614701413896215623 := by
  unfold tailWord_7809587
  simp only [CollatzResearch.WordTrace]
  refine ⟨284839038358207545117755015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189892692238805030078503343 284839038358207545117755015)
  ·
    refine ⟨427258557537311317676632523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284839038358207545117755015 427258557537311317676632523)
    ·
      refine ⟨640887836305966976514948785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427258557537311317676632523 640887836305966976514948785)
      ·
        refine ⟨480665877229475232386211589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640887836305966976514948785 480665877229475232386211589)
        ·
          refine ⟨90124851980526606072414673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 480665877229475232386211589 90124851980526606072414673)
          ·
            refine ⟨67593638985394954554311005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90124851980526606072414673 67593638985394954554311005)
            ·
              refine ⟨25347614619523107957866627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67593638985394954554311005 25347614619523107957866627)
              ·
                refine ⟨38021421929284661936799941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25347614619523107957866627 38021421929284661936799941)
                ·
                  refine ⟨7129016611740874113149989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38021421929284661936799941 7129016611740874113149989)
                  ·
                    refine ⟨1336690614701413896215623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7129016611740874113149989 1336690614701413896215623)
                    ·
                      rfl

theorem cell23_7809587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 4].length) (baseStart_7809587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809587 prefixEnd_7809587 := by exact prefixLift 7809587
  have htrace : WordTrace (prefixWord ++ tailWord_7809587) baseStart_7809587 baseEnd_7809587 := by
    simpa [prefixWord, tailWord_7809587, baseEnd_7809587] using wordTrace_append hprefix tailTrace_7809587
  have hstable : (prefixWord ++ tailWord_7809587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809587).length < 2 ^ (prefixWord ++ tailWord_7809587).sum := by decide
  have hdescent : baseEnd_7809587 < baseStart_7809587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809597 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7809597 : Nat := 118140960795 + 7809597 * 2 ^ 59
def prefixEnd_7809597 : Nat := 4983230072969 + 3 ^ 40 * 7809597 * 2
def baseEnd_7809597 : Nat := 4010076978910786649521823

theorem tailTrace_7809597 : CollatzResearch.WordTrace tailWord_7809597 prefixEnd_7809597 4010076978910786649521823 := by
  unfold tailWord_7809597
  simp only [CollatzResearch.WordTrace]
  refine ⟨284839403088171316825619045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189892935392114211217079363 284839403088171316825619045)
  ·
    refine ⟨53407388079032121904803571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284839403088171316825619045 53407388079032121904803571)
    ·
      refine ⟨80111082118548182857205357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53407388079032121904803571 80111082118548182857205357)
      ·
        refine ⟨30041655794455568571452009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80111082118548182857205357 30041655794455568571452009)
        ·
          refine ⟨22531241845841676428589007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30041655794455568571452009 22531241845841676428589007)
          ·
            refine ⟨33796862768762514642883511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22531241845841676428589007 33796862768762514642883511)
            ·
              refine ⟨50695294153143771964325267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33796862768762514642883511 50695294153143771964325267)
              ·
                refine ⟨76042941229715657946487901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50695294153143771964325267 76042941229715657946487901)
                ·
                  refine ⟨28516102961143371729932963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76042941229715657946487901 28516102961143371729932963)
                  ·
                    refine ⟨42774154441715057594899445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28516102961143371729932963 42774154441715057594899445)
                    ·
                      refine ⟨4010076978910786649521823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42774154441715057594899445 4010076978910786649521823)
                      ·
                        rfl

theorem cell23_7809597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7809597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809597 prefixEnd_7809597 := by exact prefixLift 7809597
  have htrace : WordTrace (prefixWord ++ tailWord_7809597) baseStart_7809597 baseEnd_7809597 := by
    simpa [prefixWord, tailWord_7809597, baseEnd_7809597] using wordTrace_append hprefix tailTrace_7809597
  have hstable : (prefixWord ++ tailWord_7809597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809597).length < 2 ^ (prefixWord ++ tailWord_7809597).sum := by decide
  have hdescent : baseEnd_7809597 < baseStart_7809597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809607 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_7809607 : Nat := 118140960795 + 7809607 * 2 ^ 59
def prefixEnd_7809607 : Nat := 4983230072969 + 3 ^ 40 * 7809607 * 2
def baseEnd_7809607 : Nat := 4010082113717331610396777

theorem tailTrace_7809607 : CollatzResearch.WordTrace tailWord_7809607 prefixEnd_7809607 4010082113717331610396777 := by
  unfold tailWord_7809607
  simp only [CollatzResearch.WordTrace]
  refine ⟨284839767818135088533483075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189893178545423392355655383 284839767818135088533483075)
  ·
    refine ⟨427259651727202632800224613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284839767818135088533483075 427259651727202632800224613)
    ·
      refine ⟨80111184698850493650042115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427259651727202632800224613 80111184698850493650042115)
      ·
        refine ⟨120166777048275740475063173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80111184698850493650042115 120166777048275740475063173)
        ·
          refine ⟨22531270696551701339074345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120166777048275740475063173 22531270696551701339074345)
          ·
            refine ⟨16898453022413776004305759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22531270696551701339074345 16898453022413776004305759)
            ·
              refine ⟨25347679533620664006458639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16898453022413776004305759 25347679533620664006458639)
              ·
                refine ⟨38021519300430996009687959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25347679533620664006458639 38021519300430996009687959)
                ·
                  refine ⟨57032278950646494014531939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38021519300430996009687959 57032278950646494014531939)
                  ·
                    refine ⟨85548418425969741021797909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57032278950646494014531939 85548418425969741021797909)
                    ·
                      refine ⟨4010082113717331610396777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85548418425969741021797909 4010082113717331610396777)
                      ·
                        rfl

theorem cell23_7809607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_7809607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809607 prefixEnd_7809607 := by exact prefixLift 7809607
  have htrace : WordTrace (prefixWord ++ tailWord_7809607) baseStart_7809607 baseEnd_7809607 := by
    simpa [prefixWord, tailWord_7809607, baseEnd_7809607] using wordTrace_append hprefix tailTrace_7809607
  have hstable : (prefixWord ++ tailWord_7809607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809607).length < 2 ^ (prefixWord ++ tailWord_7809607).sum := by decide
  have hdescent : baseEnd_7809607 < baseStart_7809607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809614 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_7809614 : Nat := 118140960795 + 7809614 * 2 ^ 59
def prefixEnd_7809614 : Nat := 4983230072969 + 3 ^ 40 * 7809614 * 2
def baseEnd_7809614 : Nat := 4010085708081913083009245

theorem tailTrace_7809614 : CollatzResearch.WordTrace tailWord_7809614 prefixEnd_7809614 4010085708081913083009245 := by
  unfold tailWord_7809614
  simp only [CollatzResearch.WordTrace]
  refine ⟨35605002891138716091123487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189893348752739819152658597 35605002891138716091123487)
  ·
    refine ⟨53407504336708074136685231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35605002891138716091123487 53407504336708074136685231)
    ·
      refine ⟨80111256505062111205027847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53407504336708074136685231 80111256505062111205027847)
      ·
        refine ⟨120166884757593166807541771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80111256505062111205027847 120166884757593166807541771)
        ·
          refine ⟨180250327136389750211312657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120166884757593166807541771 180250327136389750211312657)
          ·
            refine ⟨135187745352292312658484493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180250327136389750211312657 135187745352292312658484493)
            ·
              refine ⟨50695404507109617246931685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135187745352292312658484493 50695404507109617246931685)
              ·
                refine ⟨9505388345083053233799691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50695404507109617246931685 9505388345083053233799691)
                ·
                  refine ⟨14258082517624579850699537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9505388345083053233799691 14258082517624579850699537)
                  ·
                    refine ⟨10693561888218434888024653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14258082517624579850699537 10693561888218434888024653)
                    ·
                      refine ⟨4010085708081913083009245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10693561888218434888024653 4010085708081913083009245)
                      ·
                        rfl

theorem cell23_7809614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_7809614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809614 prefixEnd_7809614 := by exact prefixLift 7809614
  have htrace : WordTrace (prefixWord ++ tailWord_7809614) baseStart_7809614 baseEnd_7809614 := by
    simpa [prefixWord, tailWord_7809614, baseEnd_7809614] using wordTrace_append hprefix tailTrace_7809614
  have hstable : (prefixWord ++ tailWord_7809614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809614).length < 2 ^ (prefixWord ++ tailWord_7809614).sum := by decide
  have hdescent : baseEnd_7809614 < baseStart_7809614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809617 : List Nat := [1, 2, 2, 1, 3, 3, 4, 7]
def baseStart_7809617 : Nat := 118140960795 + 7809617 * 2 ^ 59
def prefixEnd_7809617 : Nat := 4983230072969 + 3 ^ 40 * 7809617 * 2
def baseEnd_7809617 : Nat := 148521749945328761898953

theorem tailTrace_7809617 : CollatzResearch.WordTrace tailWord_7809617 prefixEnd_7809617 148521749945328761898953 := by
  unfold tailWord_7809617
  simp only [CollatzResearch.WordTrace]
  refine ⟨284840132548098860241347105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189893421698732573494231403 284840132548098860241347105)
  ·
    refine ⟨213630099411074145181010329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284840132548098860241347105 213630099411074145181010329)
    ·
      refine ⟨160222574558305608885757747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213630099411074145181010329 160222574558305608885757747)
      ·
        refine ⟨240333861837458413328636621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160222574558305608885757747 240333861837458413328636621)
        ·
          refine ⟨90125198189046904998238733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240333861837458413328636621 90125198189046904998238733)
          ·
            refine ⟨33796949320892589374339525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90125198189046904998238733 33796949320892589374339525)
            ·
              refine ⟨6336927997667360507688661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33796949320892589374339525 6336927997667360507688661)
              ·
                refine ⟨148521749945328761898953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6336927997667360507688661 148521749945328761898953)
                ·
                  rfl

theorem cell23_7809617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 7].length) (baseStart_7809617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809617 prefixEnd_7809617 := by exact prefixLift 7809617
  have htrace : WordTrace (prefixWord ++ tailWord_7809617) baseStart_7809617 baseEnd_7809617 := by
    simpa [prefixWord, tailWord_7809617, baseEnd_7809617] using wordTrace_append hprefix tailTrace_7809617
  have hstable : (prefixWord ++ tailWord_7809617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809617).length < 2 ^ (prefixWord ++ tailWord_7809617).sum := by decide
  have hdescent : baseEnd_7809617 < baseStart_7809617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809644 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 3]
def baseStart_7809644 : Nat := 118140960795 + 7809644 * 2 ^ 59
def prefixEnd_7809644 : Nat := 4983230072969 + 3 ^ 40 * 7809644 * 2
def baseEnd_7809644 : Nat := 4010101112501547965634107

theorem tailTrace_7809644 : CollatzResearch.WordTrace tailWord_7809644 prefixEnd_7809644 4010101112501547965634107 := by
  unfold tailWord_7809644
  simp only [CollatzResearch.WordTrace]
  refine ⟨142420558659500521926289993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189894078212667362568386657 142420558659500521926289993)
  ·
    refine ⟨106815418994625391444717495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142420558659500521926289993 106815418994625391444717495)
    ·
      refine ⟨160223128491938087167076243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106815418994625391444717495 160223128491938087167076243)
      ·
        refine ⟨240334692737907130750614365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160223128491938087167076243 240334692737907130750614365)
        ·
          refine ⟨90125509776715174031480387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240334692737907130750614365 90125509776715174031480387)
          ·
            refine ⟨135188264665072761047220581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90125509776715174031480387 135188264665072761047220581)
            ·
              refine ⟨25347799624701142696353859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135188264665072761047220581 25347799624701142696353859)
              ·
                refine ⟨38021699437051714044530789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25347799624701142696353859 38021699437051714044530789)
                ·
                  refine ⟨7129068644447196383349523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38021699437051714044530789 7129068644447196383349523)
                  ·
                    refine ⟨10693602966670794575024285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7129068644447196383349523 10693602966670794575024285)
                    ·
                      refine ⟨4010101112501547965634107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10693602966670794575024285 4010101112501547965634107)
                      ·
                        rfl

theorem cell23_7809644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_7809644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809644 prefixEnd_7809644 := by exact prefixLift 7809644
  have htrace : WordTrace (prefixWord ++ tailWord_7809644) baseStart_7809644 baseEnd_7809644 := by
    simpa [prefixWord, tailWord_7809644, baseEnd_7809644] using wordTrace_append hprefix tailTrace_7809644
  have hstable : (prefixWord ++ tailWord_7809644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809644).length < 2 ^ (prefixWord ++ tailWord_7809644).sum := by decide
  have hdescent : baseEnd_7809644 < baseStart_7809644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809687 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_7809687 : Nat := 118140960795 + 7809687 * 2 ^ 59
def prefixEnd_7809687 : Nat := 4983230072969 + 3 ^ 40 * 7809687 * 2
def baseEnd_7809687 : Nat := 4010123192169691297396409

theorem tailTrace_7809687 : CollatzResearch.WordTrace tailWord_7809687 prefixEnd_7809687 4010123192169691297396409 := by
  unfold tailWord_7809687
  simp only [CollatzResearch.WordTrace]
  refine ⟨284842685657845262196395315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189895123771896841464263543 284842685657845262196395315)
  ·
    refine ⟨427264028486767893294592973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284842685657845262196395315 427264028486767893294592973)
    ·
      refine ⟨160224010682537959985472365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427264028486767893294592973 160224010682537959985472365)
      ·
        refine ⟨60084004005951734994552137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160224010682537959985472365 60084004005951734994552137)
        ·
          refine ⟨45063003004463801245914103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60084004005951734994552137 45063003004463801245914103)
          ·
            refine ⟨67594504506695701868871155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45063003004463801245914103 67594504506695701868871155)
            ·
              refine ⟨101391756760043552803306733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67594504506695701868871155 101391756760043552803306733)
              ·
                refine ⟨38021908785016332301240025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101391756760043552803306733 38021908785016332301240025)
                ·
                  refine ⟨28516431588762249225930019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38021908785016332301240025 28516431588762249225930019)
                  ·
                    refine ⟨42774647383143373838895029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28516431588762249225930019 42774647383143373838895029)
                    ·
                      refine ⟨4010123192169691297396409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42774647383143373838895029 4010123192169691297396409)
                      ·
                        rfl

theorem cell23_7809687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_7809687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809687 prefixEnd_7809687 := by exact prefixLift 7809687
  have htrace : WordTrace (prefixWord ++ tailWord_7809687) baseStart_7809687 baseEnd_7809687 := by
    simpa [prefixWord, tailWord_7809687, baseEnd_7809687] using wordTrace_append hprefix tailTrace_7809687
  have hstable : (prefixWord ++ tailWord_7809687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809687).length < 2 ^ (prefixWord ++ tailWord_7809687).sum := by decide
  have hdescent : baseEnd_7809687 < baseStart_7809687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809688 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 1, 3, 2]
def baseStart_7809688 : Nat := 118140960795 + 7809688 * 2 ^ 59
def prefixEnd_7809688 : Nat := 4983230072969 + 3 ^ 40 * 7809688 * 2
def baseEnd_7809688 : Nat := 4010123705650345793483905

theorem tailTrace_7809688 : CollatzResearch.WordTrace tailWord_7809688 prefixEnd_7809688 4010123705650345793483905 := by
  unfold tailWord_7809688
  simp only [CollatzResearch.WordTrace]
  refine ⟨142421361065420819683590859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189895148087227759578121145 142421361065420819683590859)
  ·
    refine ⟨213632041598131229525386289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142421361065420819683590859 213632041598131229525386289)
    ·
      refine ⟨160224031198598422144039717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213632041598131229525386289 160224031198598422144039717)
      ·
        refine ⟨30042005849737204152007447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160224031198598422144039717 30042005849737204152007447)
        ·
          refine ⟨45063008774605806228011171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30042005849737204152007447 45063008774605806228011171)
          ·
            refine ⟨67594513161908709342016757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45063008774605806228011171 67594513161908709342016757)
            ·
              refine ⟨6336985608928941500814071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67594513161908709342016757 6336985608928941500814071)
              ·
                refine ⟨9505478413393412251221107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6336985608928941500814071 9505478413393412251221107)
                ·
                  refine ⟨14258217620090118376831661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9505478413393412251221107 14258217620090118376831661)
                  ·
                    refine ⟨5346831607533794391311873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14258217620090118376831661 5346831607533794391311873)
                    ·
                      refine ⟨4010123705650345793483905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5346831607533794391311873 4010123705650345793483905)
                      ·
                        rfl

theorem cell23_7809688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_7809688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809688 prefixEnd_7809688 := by exact prefixLift 7809688
  have htrace : WordTrace (prefixWord ++ tailWord_7809688) baseStart_7809688 baseEnd_7809688 := by
    simpa [prefixWord, tailWord_7809688, baseEnd_7809688] using wordTrace_append hprefix tailTrace_7809688
  have hstable : (prefixWord ++ tailWord_7809688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809688).length < 2 ^ (prefixWord ++ tailWord_7809688).sum := by decide
  have hdescent : baseEnd_7809688 < baseStart_7809688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809694 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7809694 : Nat := 118140960795 + 7809694 * 2 ^ 59
def prefixEnd_7809694 : Nat := 4983230072969 + 3 ^ 40 * 7809694 * 2
def baseEnd_7809694 : Nat := 1336708928844757590002959

theorem tailTrace_7809694 : CollatzResearch.WordTrace tailWord_7809694 prefixEnd_7809694 1336708928844757590002959 := by
  unfold tailWord_7809694
  simp only [CollatzResearch.WordTrace]
  refine ⟨35605367621102487798987517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189895293979213268261266757 35605367621102487798987517)
  ·
    refine ⟨13352012857913432924620319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35605367621102487798987517 13352012857913432924620319)
    ·
      refine ⟨20028019286870149386930479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13352012857913432924620319 20028019286870149386930479)
      ·
        refine ⟨30042028930305224080395719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20028019286870149386930479 30042028930305224080395719)
        ·
          refine ⟨45063043395457836120593579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30042028930305224080395719 45063043395457836120593579)
          ·
            refine ⟨67594565093186754180890369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45063043395457836120593579 67594565093186754180890369)
            ·
              refine ⟨50695923819890065635667777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67594565093186754180890369 50695923819890065635667777)
              ·
                refine ⟨38021942864917549226750833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50695923819890065635667777 38021942864917549226750833)
                ·
                  refine ⟨28516457148688161920063125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38021942864917549226750833 28516457148688161920063125)
                  ·
                    refine ⟨1336708928844757590002959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28516457148688161920063125 1336708928844757590002959)
                    ·
                      rfl

theorem cell23_7809694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7809694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809694 prefixEnd_7809694 := by exact prefixLift 7809694
  have htrace : WordTrace (prefixWord ++ tailWord_7809694) baseStart_7809694 baseEnd_7809694 := by
    simpa [prefixWord, tailWord_7809694, baseEnd_7809694] using wordTrace_append hprefix tailTrace_7809694
  have hstable : (prefixWord ++ tailWord_7809694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809694).length < 2 ^ (prefixWord ++ tailWord_7809694).sum := by decide
  have hdescent : baseEnd_7809694 < baseStart_7809694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809774 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_7809774 : Nat := 118140960795 + 7809774 * 2 ^ 59
def prefixEnd_7809774 : Nat := 4983230072969 + 3 ^ 40 * 7809774 * 2
def baseEnd_7809774 : Nat := 4010167864986632457008509

theorem tailTrace_7809774 : CollatzResearch.WordTrace tailWord_7809774 prefixEnd_7809774 4010167864986632457008509 := by
  unfold tailWord_7809774
  simp only [CollatzResearch.WordTrace]
  refine ⟨35605732351066259506851547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189897239205686717369874917 35605732351066259506851547)
  ·
    refine ⟨53408598526599389260277321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35605732351066259506851547 53408598526599389260277321)
    ·
      refine ⟨40056448894949541945207991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53408598526599389260277321 40056448894949541945207991)
      ·
        refine ⟨60084673342424312917811987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40056448894949541945207991 60084673342424312917811987)
        ·
          refine ⟨90127010013636469376717981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60084673342424312917811987 90127010013636469376717981)
          ·
            refine ⟨33797628755113676016269243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90127010013636469376717981 33797628755113676016269243)
            ·
              refine ⟨50696443132670514024403865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33797628755113676016269243 50696443132670514024403865)
              ·
                refine ⟨38022332349502885518302899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50696443132670514024403865 38022332349502885518302899)
                ·
                  refine ⟨57033498524254328277454349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38022332349502885518302899 57033498524254328277454349)
                  ·
                    refine ⟨21387561946595373104045381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57033498524254328277454349 21387561946595373104045381)
                    ·
                      refine ⟨4010167864986632457008509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21387561946595373104045381 4010167864986632457008509)
                      ·
                        rfl

theorem cell23_7809774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_7809774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809774 prefixEnd_7809774 := by exact prefixLift 7809774
  have htrace : WordTrace (prefixWord ++ tailWord_7809774) baseStart_7809774 baseEnd_7809774 := by
    simpa [prefixWord, tailWord_7809774, baseEnd_7809774] using wordTrace_append hprefix tailTrace_7809774
  have hstable : (prefixWord ++ tailWord_7809774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809774).length < 2 ^ (prefixWord ++ tailWord_7809774).sum := by decide
  have hdescent : baseEnd_7809774 < baseStart_7809774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809784 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 3, 4]
def baseStart_7809784 : Nat := 118140960795 + 7809784 * 2 ^ 59
def prefixEnd_7809784 : Nat := 4983230072969 + 3 ^ 40 * 7809784 * 2
def baseEnd_7809784 : Nat := 1336724333264392472627821

theorem tailTrace_7809784 : CollatzResearch.WordTrace tailWord_7809784 prefixEnd_7809784 1336724333264392472627821 := by
  unfold tailWord_7809784
  simp only [CollatzResearch.WordTrace]
  refine ⟨142423111769246923881338203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189897482358995898508450937 142423111769246923881338203)
  ·
    refine ⟨213634667653870385822007305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142423111769246923881338203 213634667653870385822007305)
    ·
      refine ⟨160226000740402789366505479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213634667653870385822007305 160226000740402789366505479)
      ·
        refine ⟨240339001110604184049758219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160226000740402789366505479 240339001110604184049758219)
        ·
          refine ⟨360508501665906276074637329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240339001110604184049758219 360508501665906276074637329)
          ·
            refine ⟨270381376249429707055977997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360508501665906276074637329 270381376249429707055977997)
            ·
              refine ⟨101393016093536140145991749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270381376249429707055977997 101393016093536140145991749)
              ·
                refine ⟨19011190517538026277373453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101393016093536140145991749 19011190517538026277373453)
                ·
                  refine ⟨7129196444076759854015045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19011190517538026277373453 7129196444076759854015045)
                  ·
                    refine ⟨1336724333264392472627821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7129196444076759854015045 1336724333264392472627821)
                    ·
                      rfl

theorem cell23_7809784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_7809784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809784 prefixEnd_7809784 := by exact prefixLift 7809784
  have htrace : WordTrace (prefixWord ++ tailWord_7809784) baseStart_7809784 baseEnd_7809784 := by
    simpa [prefixWord, tailWord_7809784, baseEnd_7809784] using wordTrace_append hprefix tailTrace_7809784
  have hstable : (prefixWord ++ tailWord_7809784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809784).length < 2 ^ (prefixWord ++ tailWord_7809784).sum := by decide
  have hdescent : baseEnd_7809784 < baseStart_7809784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809817 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_7809817 : Nat := 118140960795 + 7809817 * 2 ^ 59
def prefixEnd_7809817 : Nat := 4983230072969 + 3 ^ 40 * 7809817 * 2
def baseEnd_7809817 : Nat := 4010189944654775788770811

theorem tailTrace_7809817 : CollatzResearch.WordTrace tailWord_7809817 prefixEnd_7809817 4010189944654775788770811 := by
  unfold tailWord_7809817
  simp only [CollatzResearch.WordTrace]
  refine ⟨284847427147374294398627705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189898284764916196265751803 284847427147374294398627705)
  ·
    refine ⟨213635570360530720798970779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284847427147374294398627705 213635570360530720798970779)
    ·
      refine ⟨320453355540796081198456169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213635570360530720798970779 320453355540796081198456169)
      ·
        refine ⟨240340016655597060898842127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320453355540796081198456169 240340016655597060898842127)
        ·
          refine ⟨360510024983395591348263191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240340016655597060898842127 360510024983395591348263191)
          ·
            refine ⟨540765037475093387022394787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360510024983395591348263191 540765037475093387022394787)
            ·
              refine ⟨811147556212640080533592181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540765037475093387022394787 811147556212640080533592181)
              ·
                refine ⟨76045083394935007550024267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 811147556212640080533592181 76045083394935007550024267)
                ·
                  refine ⟨114067625092402511325036401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76045083394935007550024267 114067625092402511325036401)
                  ·
                    refine ⟨85550718819301883493777301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114067625092402511325036401 85550718819301883493777301)
                    ·
                      refine ⟨4010189944654775788770811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85550718819301883493777301 4010189944654775788770811)
                      ·
                        rfl

theorem cell23_7809817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_7809817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809817 prefixEnd_7809817 := by exact prefixLift 7809817
  have htrace : WordTrace (prefixWord ++ tailWord_7809817) baseStart_7809817 baseEnd_7809817 := by
    simpa [prefixWord, tailWord_7809817, baseEnd_7809817] using wordTrace_append hprefix tailTrace_7809817
  have hstable : (prefixWord ++ tailWord_7809817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809817).length < 2 ^ (prefixWord ++ tailWord_7809817).sum := by decide
  have hdescent : baseEnd_7809817 < baseStart_7809817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809827 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 2, 9]
def baseStart_7809827 : Nat := 118140960795 + 7809827 * 2 ^ 59
def prefixEnd_7809827 : Nat := 4983230072969 + 3 ^ 40 * 7809827 * 2
def baseEnd_7809827 : Nat := 1336731693153773583215255

theorem tailTrace_7809827 : CollatzResearch.WordTrace tailWord_7809827 prefixEnd_7809827 1336731693153773583215255 := by
  unfold tailWord_7809827
  simp only [CollatzResearch.WordTrace]
  refine ⟨284847791877338066106491735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189898527918225377404327823 284847791877338066106491735)
  ·
    refine ⟨427271687816007099159737603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284847791877338066106491735 427271687816007099159737603)
    ·
      refine ⟨640907531724010648739606405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427271687816007099159737603 640907531724010648739606405)
      ·
        refine ⟨120170162198251996638676201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 640907531724010648739606405 120170162198251996638676201)
        ·
          refine ⟨90127621648688997479007151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120170162198251996638676201 90127621648688997479007151)
          ·
            refine ⟨135191432473033496218510727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90127621648688997479007151 135191432473033496218510727)
            ·
              refine ⟨202787148709550244327766091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135191432473033496218510727 202787148709550244327766091)
              ·
                refine ⟨304180723064325366491649137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202787148709550244327766091 304180723064325366491649137)
                ·
                  refine ⟨228135542298244024868736853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304180723064325366491649137 228135542298244024868736853)
                  ·
                    refine ⟨1336731693153773583215255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 228135542298244024868736853 1336731693153773583215255)
                    ·
                      rfl

theorem cell23_7809827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 9].length) (baseStart_7809827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809827 prefixEnd_7809827 := by exact prefixLift 7809827
  have htrace : WordTrace (prefixWord ++ tailWord_7809827) baseStart_7809827 baseEnd_7809827 := by
    simpa [prefixWord, tailWord_7809827, baseEnd_7809827] using wordTrace_append hprefix tailTrace_7809827
  have hstable : (prefixWord ++ tailWord_7809827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809827).length < 2 ^ (prefixWord ++ tailWord_7809827).sum := by decide
  have hdescent : baseEnd_7809827 < baseStart_7809827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809841 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 5, 1, 3]
def baseStart_7809841 : Nat := 118140960795 + 7809841 * 2 ^ 59
def prefixEnd_7809841 : Nat := 4983230072969 + 3 ^ 40 * 7809841 * 2
def baseEnd_7809841 : Nat := 4010202268190483694870701

theorem tailTrace_7809841 : CollatzResearch.WordTrace tailWord_7809841 prefixEnd_7809841 4010202268190483694870701 := by
  unfold tailWord_7809841
  simp only [CollatzResearch.WordTrace]
  refine ⟨284848302499287346497501377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189898868332858230998334251 284848302499287346497501377)
  ·
    refine ⟨213636226874465509873126033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284848302499287346497501377 213636226874465509873126033)
    ·
      refine ⟨160227170155849132404844525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213636226874465509873126033 160227170155849132404844525)
      ·
        refine ⟨60085188808443424651816697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160227170155849132404844525 60085188808443424651816697)
        ·
          refine ⟨45063891606332568488862523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60085188808443424651816697 45063891606332568488862523)
          ·
            refine ⟨67595837409498852733293785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45063891606332568488862523 67595837409498852733293785)
            ·
              refine ⟨50696878057124139549970339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67595837409498852733293785 50696878057124139549970339)
              ·
                refine ⟨76045317085686209324955509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50696878057124139549970339 76045317085686209324955509)
                ·
                  refine ⟨7129248476783082124214579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76045317085686209324955509 7129248476783082124214579)
                  ·
                    refine ⟨10693872715174623186321869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7129248476783082124214579 10693872715174623186321869)
                    ·
                      refine ⟨4010202268190483694870701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10693872715174623186321869 4010202268190483694870701)
                      ·
                        rfl

theorem cell23_7809841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_7809841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809841 prefixEnd_7809841 := by exact prefixLift 7809841
  have htrace : WordTrace (prefixWord ++ tailWord_7809841) baseStart_7809841 baseEnd_7809841 := by
    simpa [prefixWord, tailWord_7809841, baseEnd_7809841] using wordTrace_append hprefix tailTrace_7809841
  have hstable : (prefixWord ++ tailWord_7809841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809841).length < 2 ^ (prefixWord ++ tailWord_7809841).sum := by decide
  have hdescent : baseEnd_7809841 < baseStart_7809841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809868 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 2, 3, 2]
def baseStart_7809868 : Nat := 118140960795 + 7809868 * 2 ^ 59
def prefixEnd_7809868 : Nat := 4983230072969 + 3 ^ 40 * 7809868 * 2
def baseEnd_7809868 : Nat := 4010216132168155089233077

theorem tailTrace_7809868 : CollatzResearch.WordTrace tailWord_7809868 prefixEnd_7809868 4010216132168155089233077 := by
  unfold tailWord_7809868
  simp only [CollatzResearch.WordTrace]
  refine ⟨142424643635094765054367129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189899524846793020072489505 142424643635094765054367129)
  ·
    refine ⟨106818482726321073790775347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142424643635094765054367129 106818482726321073790775347)
    ·
      refine ⟨160227724089481610686163021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106818482726321073790775347 160227724089481610686163021)
      ·
        refine ⟨60085396533555604007311133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160227724089481610686163021 60085396533555604007311133)
        ·
          refine ⟨22532023700083351502741675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60085396533555604007311133 22532023700083351502741675)
          ·
            refine ⟨33798035550125027254112513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22532023700083351502741675 33798035550125027254112513)
            ·
              refine ⟨25348526662593770440584385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33798035550125027254112513 25348526662593770440584385)
              ·
                refine ⟨19011394996945327830438289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25348526662593770440584385 19011394996945327830438289)
                ·
                  refine ⟨14258546247708995872828717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19011394996945327830438289 14258546247708995872828717)
                  ·
                    refine ⟨5346954842890873452310769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14258546247708995872828717 5346954842890873452310769)
                    ·
                      refine ⟨4010216132168155089233077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5346954842890873452310769 4010216132168155089233077)
                      ·
                        rfl

theorem cell23_7809868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_7809868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809868 prefixEnd_7809868 := by exact prefixLift 7809868
  have htrace : WordTrace (prefixWord ++ tailWord_7809868) baseStart_7809868 baseEnd_7809868 := by
    simpa [prefixWord, tailWord_7809868, baseEnd_7809868] using wordTrace_append hprefix tailTrace_7809868
  have hstable : (prefixWord ++ tailWord_7809868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809868).length < 2 ^ (prefixWord ++ tailWord_7809868).sum := by decide
  have hdescent : baseEnd_7809868 < baseStart_7809868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809869 : List Nat := [1, 6, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_7809869 : Nat := 118140960795 + 7809869 * 2 ^ 59
def prefixEnd_7809869 : Nat := 4983230072969 + 3 ^ 40 * 7809869 * 2
def baseEnd_7809869 : Nat := 1336738881882936528440191

theorem tailTrace_7809869 : CollatzResearch.WordTrace tailWord_7809869 prefixEnd_7809869 1336738881882936528440191 := by
  unfold tailWord_7809869
  simp only [CollatzResearch.WordTrace]
  refine ⟨284849323743185907279520661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189899549162123938186347107 284849323743185907279520661)
  ·
    refine ⟨13352312050461839403727531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 284849323743185907279520661 13352312050461839403727531)
    ·
      refine ⟨20028468075692759105591297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13352312050461839403727531 20028468075692759105591297)
      ·
        refine ⟨15021351056769569329193473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20028468075692759105591297 15021351056769569329193473)
        ·
          refine ⟨11266013292577176996895105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15021351056769569329193473 11266013292577176996895105)
          ·
            refine ⟨8449509969432882747671329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11266013292577176996895105 8449509969432882747671329)
            ·
              refine ⟨6337132477074662060753497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8449509969432882747671329 6337132477074662060753497)
              ·
                refine ⟨4752849357805996545565123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6337132477074662060753497 4752849357805996545565123)
                ·
                  refine ⟨7129274036708994818347685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752849357805996545565123 7129274036708994818347685)
                  ·
                    refine ⟨1336738881882936528440191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7129274036708994818347685 1336738881882936528440191)
                    ·
                      rfl

theorem cell23_7809869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_7809869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809869 prefixEnd_7809869 := by exact prefixLift 7809869
  have htrace : WordTrace (prefixWord ++ tailWord_7809869) baseStart_7809869 baseEnd_7809869 := by
    simpa [prefixWord, tailWord_7809869, baseEnd_7809869] using wordTrace_append hprefix tailTrace_7809869
  have hstable : (prefixWord ++ tailWord_7809869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809869).length < 2 ^ (prefixWord ++ tailWord_7809869).sum := by decide
  have hdescent : baseEnd_7809869 < baseStart_7809869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809874 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_7809874 : Nat := 118140960795 + 7809874 * 2 ^ 59
def prefixEnd_7809874 : Nat := 4983230072969 + 3 ^ 40 * 7809874 * 2
def baseEnd_7809874 : Nat := 1336739737684027355252683

theorem tailTrace_7809874 : CollatzResearch.WordTrace tailWord_7809874 prefixEnd_7809874 1336739737684027355252683 := by
  unfold tailWord_7809874
  simp only [CollatzResearch.WordTrace]
  refine ⟨71212376527041948283363169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189899670738778528755635117 71212376527041948283363169)
  ·
    refine ⟨53409282395281461212522377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71212376527041948283363169 53409282395281461212522377)
    ·
      refine ⟨40056961796461095909391783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53409282395281461212522377 40056961796461095909391783)
      ·
        refine ⟨60085442694691643864087675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40056961796461095909391783 60085442694691643864087675)
        ·
          refine ⟨90128164042037465796131513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60085442694691643864087675 90128164042037465796131513)
          ·
            refine ⟨67596123031528099347098635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90128164042037465796131513 67596123031528099347098635)
            ·
              refine ⟨101394184547292149020647953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67596123031528099347098635 101394184547292149020647953)
              ·
                refine ⟨76045638410469111765485965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101394184547292149020647953 76045638410469111765485965)
                ·
                  refine ⟨28517114403925916912057237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76045638410469111765485965 28517114403925916912057237)
                  ·
                    refine ⟨1336739737684027355252683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28517114403925916912057237 1336739737684027355252683)
                    ·
                      rfl

theorem cell23_7809874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_7809874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809874 prefixEnd_7809874 := by exact prefixLift 7809874
  have htrace : WordTrace (prefixWord ++ tailWord_7809874) baseStart_7809874 baseEnd_7809874 := by
    simpa [prefixWord, tailWord_7809874, baseEnd_7809874] using wordTrace_append hprefix tailTrace_7809874
  have hstable : (prefixWord ++ tailWord_7809874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809874).length < 2 ^ (prefixWord ++ tailWord_7809874).sum := by decide
  have hdescent : baseEnd_7809874 < baseStart_7809874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809891 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 1, 6]
def baseStart_7809891 : Nat := 118140960795 + 7809891 * 2 ^ 59
def prefixEnd_7809891 : Nat := 4983230072969 + 3 ^ 40 * 7809891 * 2
def baseEnd_7809891 : Nat := 1336742647407736166415157

theorem tailTrace_7809891 : CollatzResearch.WordTrace tailWord_7809891 prefixEnd_7809891 1336742647407736166415157 := by
  unfold tailWord_7809891
  simp only [CollatzResearch.WordTrace]
  refine ⟨284850126149106205036821527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189900084099404136691214351 284850126149106205036821527)
  ·
    refine ⟨427275189223659307555232291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284850126149106205036821527 427275189223659307555232291)
    ·
      refine ⟨640912783835488961332848437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427275189223659307555232291 640912783835488961332848437)
      ·
        refine ⟨60085573484577090124954541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 640912783835488961332848437 60085573484577090124954541)
        ·
          refine ⟨22532090056716408796857953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60085573484577090124954541 22532090056716408796857953)
          ·
            refine ⟨16899067542537306597643465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22532090056716408796857953 16899067542537306597643465)
            ·
              refine ⟨12674300656902979948232599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16899067542537306597643465 12674300656902979948232599)
              ·
                refine ⟨19011450985354469922348899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12674300656902979948232599 19011450985354469922348899)
                ·
                  refine ⟨28517176478031704883523349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19011450985354469922348899 28517176478031704883523349)
                  ·
                    refine ⟨1336742647407736166415157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28517176478031704883523349 1336742647407736166415157)
                    ·
                      rfl

theorem cell23_7809891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 6].length) (baseStart_7809891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809891 prefixEnd_7809891 := by exact prefixLift 7809891
  have htrace : WordTrace (prefixWord ++ tailWord_7809891) baseStart_7809891 baseEnd_7809891 := by
    simpa [prefixWord, tailWord_7809891, baseEnd_7809891] using wordTrace_append hprefix tailTrace_7809891
  have hstable : (prefixWord ++ tailWord_7809891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809891).length < 2 ^ (prefixWord ++ tailWord_7809891).sum := by decide
  have hdescent : baseEnd_7809891 < baseStart_7809891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809902 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_7809902 : Nat := 118140960795 + 7809902 * 2 ^ 59
def prefixEnd_7809902 : Nat := 4983230072969 + 3 ^ 40 * 7809902 * 2
def baseEnd_7809902 : Nat := 4010233590510407956207921

theorem tailTrace_7809902 : CollatzResearch.WordTrace tailWord_7809902 prefixEnd_7809902 4010233590510407956207921 := by
  unfold tailWord_7809902
  simp only [CollatzResearch.WordTrace]
  refine ⟨35606315919008294239433995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189900351568044235943647973 35606315919008294239433995)
  ·
    refine ⟨53409473878512441359150993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35606315919008294239433995 53409473878512441359150993)
    ·
      refine ⟨40057105408884331019363245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53409473878512441359150993 40057105408884331019363245)
      ·
        refine ⟨15021414528331624132261217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40057105408884331019363245 15021414528331624132261217)
        ·
          refine ⟨11266060896248718099195913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15021414528331624132261217 11266060896248718099195913)
          ·
            refine ⟨8449545672186538574396935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11266060896248718099195913 8449545672186538574396935)
            ·
              refine ⟨12674318508279807861595403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8449545672186538574396935 12674318508279807861595403)
              ·
                refine ⟨19011477762419711792393105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12674318508279807861595403 19011477762419711792393105)
                ·
                  refine ⟨14258608321814783844294829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19011477762419711792393105 14258608321814783844294829)
                  ·
                    refine ⟨5346978120680543941610561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14258608321814783844294829 5346978120680543941610561)
                    ·
                      refine ⟨4010233590510407956207921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5346978120680543941610561 4010233590510407956207921)
                      ·
                        rfl

theorem cell23_7809902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_7809902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809902 prefixEnd_7809902 := by exact prefixLift 7809902
  have htrace : WordTrace (prefixWord ++ tailWord_7809902) baseStart_7809902 baseEnd_7809902 := by
    simpa [prefixWord, tailWord_7809902, baseEnd_7809902] using wordTrace_append hprefix tailTrace_7809902
  have hstable : (prefixWord ++ tailWord_7809902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809902).length < 2 ^ (prefixWord ++ tailWord_7809902).sum := by decide
  have hdescent : baseEnd_7809902 < baseStart_7809902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809915 : List Nat := [1, 1, 1, 1, 1, 5, 3, 5, 1, 2, 2]
def baseStart_7809915 : Nat := 118140960795 + 7809915 * 2 ^ 59
def prefixEnd_7809915 : Nat := 4983230072969 + 3 ^ 40 * 7809915 * 2
def baseEnd_7809915 : Nat := 4010240265758916405345361

theorem tailTrace_7809915 : CollatzResearch.WordTrace tailWord_7809915 prefixEnd_7809915 4010240265758916405345361 := by
  unfold tailWord_7809915
  simp only [CollatzResearch.WordTrace]
  refine ⟨284851001501019257135695199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189900667667346171423796799 284851001501019257135695199)
  ·
    refine ⟨427276502251528885703542799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284851001501019257135695199 427276502251528885703542799)
    ·
      refine ⟨640914753377293328555314199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427276502251528885703542799 640914753377293328555314199)
      ·
        refine ⟨961372130065939992832971299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640914753377293328555314199 961372130065939992832971299)
        ·
          refine ⟨1442058195098909989249456949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961372130065939992832971299 1442058195098909989249456949)
          ·
            refine ⟨135192955790522811492136589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1442058195098909989249456949 135192955790522811492136589)
            ·
              refine ⟨50697358421446054309551221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135192955790522811492136589 50697358421446054309551221)
              ·
                refine ⟨4752877352010567591520427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50697358421446054309551221 4752877352010567591520427)
                ·
                  refine ⟨7129316028015851387280641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752877352010567591520427 7129316028015851387280641)
                  ·
                    refine ⟨5346987021011888540460481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7129316028015851387280641 5346987021011888540460481)
                    ·
                      refine ⟨4010240265758916405345361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5346987021011888540460481 4010240265758916405345361)
                      ·
                        rfl

theorem cell23_7809915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 1, 2, 2].length) (baseStart_7809915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809915 prefixEnd_7809915 := by exact prefixLift 7809915
  have htrace : WordTrace (prefixWord ++ tailWord_7809915) baseStart_7809915 baseEnd_7809915 := by
    simpa [prefixWord, tailWord_7809915, baseEnd_7809915] using wordTrace_append hprefix tailTrace_7809915
  have hstable : (prefixWord ++ tailWord_7809915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809915).length < 2 ^ (prefixWord ++ tailWord_7809915).sum := by decide
  have hdescent : baseEnd_7809915 < baseStart_7809915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809924 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7809924 : Nat := 118140960795 + 7809924 * 2 ^ 59
def prefixEnd_7809924 : Nat := 4983230072969 + 3 ^ 40 * 7809924 * 2
def baseEnd_7809924 : Nat := 4010244887084806870132819

theorem tailTrace_7809924 : CollatzResearch.WordTrace tailWord_7809924 prefixEnd_7809924 4010244887084806870132819 := by
  unfold tailWord_7809924
  simp only [CollatzResearch.WordTrace]
  refine ⟨142425664878993325836386413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189900886505324434448515217 142425664878993325836386413)
  ·
    refine ⟨53409624329622497188644905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142425664878993325836386413 53409624329622497188644905)
    ·
      refine ⟨40057218247216872891483679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53409624329622497188644905 40057218247216872891483679)
      ·
        refine ⟨60085827370825309337225519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40057218247216872891483679 60085827370825309337225519)
        ·
          refine ⟨90128741056237964005838279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60085827370825309337225519 90128741056237964005838279)
          ·
            refine ⟨135193111584356946008757419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90128741056237964005838279 135193111584356946008757419)
            ·
              refine ⟨202789667376535419013136129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135193111584356946008757419 202789667376535419013136129)
              ·
                refine ⟨152092250532401564259852097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202789667376535419013136129 152092250532401564259852097)
                ·
                  refine ⟨114069187899301173194889073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152092250532401564259852097 114069187899301173194889073)
                  ·
                    refine ⟨85551890924475879896166805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114069187899301173194889073 85551890924475879896166805)
                    ·
                      refine ⟨4010244887084806870132819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85551890924475879896166805 4010244887084806870132819)
                      ·
                        rfl

theorem cell23_7809924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7809924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809924 prefixEnd_7809924 := by exact prefixLift 7809924
  have htrace : WordTrace (prefixWord ++ tailWord_7809924) baseStart_7809924 baseEnd_7809924 := by
    simpa [prefixWord, tailWord_7809924, baseEnd_7809924] using wordTrace_append hprefix tailTrace_7809924
  have hstable : (prefixWord ++ tailWord_7809924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809924).length < 2 ^ (prefixWord ++ tailWord_7809924).sum := by decide
  have hdescent : baseEnd_7809924 < baseStart_7809924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7809942 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_7809942 : Nat := 118140960795 + 7809942 * 2 ^ 59
def prefixEnd_7809942 : Nat := 4983230072969 + 3 ^ 40 * 7809942 * 2
def baseEnd_7809942 : Nat := 1336751376578862599902579

theorem tailTrace_7809942 : CollatzResearch.WordTrace tailWord_7809942 prefixEnd_7809942 1336751376578862599902579 := by
  unfold tailWord_7809942
  simp only [CollatzResearch.WordTrace]
  refine ⟨17803249141995090046683005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189901324181280960497952053 17803249141995090046683005)
  ·
    refine ⟨6676218428248158767506127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17803249141995090046683005 6676218428248158767506127)
    ·
      refine ⟨10014327642372238151259191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6676218428248158767506127 10014327642372238151259191)
      ·
        refine ⟨15021491463558357226888787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10014327642372238151259191 15021491463558357226888787)
        ·
          refine ⟨22532237195337535840333181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15021491463558357226888787 22532237195337535840333181)
          ·
            refine ⟨8449588948251575940124943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22532237195337535840333181 8449588948251575940124943)
            ·
              refine ⟨12674383422377363910187415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8449588948251575940124943 12674383422377363910187415)
              ·
                refine ⟨19011575133566045865281123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12674383422377363910187415 19011575133566045865281123)
                ·
                  refine ⟨28517362700349068797921685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19011575133566045865281123 28517362700349068797921685)
                  ·
                    refine ⟨1336751376578862599902579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28517362700349068797921685 1336751376578862599902579)
                    ·
                      rfl

theorem cell23_7809942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_7809942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7809942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7809942 prefixEnd_7809942 := by exact prefixLift 7809942
  have htrace : WordTrace (prefixWord ++ tailWord_7809942) baseStart_7809942 baseEnd_7809942 := by
    simpa [prefixWord, tailWord_7809942, baseEnd_7809942] using wordTrace_append hprefix tailTrace_7809942
  have hstable : (prefixWord ++ tailWord_7809942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7809942).length < 2 ^ (prefixWord ++ tailWord_7809942).sum := by decide
  have hdescent : baseEnd_7809942 < baseStart_7809942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7809942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810041 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 2, 5]
def baseStart_7810041 : Nat := 118140960795 + 7810041 * 2 ^ 59
def prefixEnd_7810041 : Nat := 4983230072969 + 3 ^ 40 * 7810041 * 2
def baseEnd_7810041 : Nat := 1336768321440460970789927

theorem tailTrace_7810041 : CollatzResearch.WordTrace tailWord_7810041 prefixEnd_7810041 1336768321440460970789927 := by
  unfold tailWord_7810041
  simp only [CollatzResearch.WordTrace]
  refine ⟨284855597098562780654781977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189903731399041853769854651 284855597098562780654781977)
  ·
    refine ⟨213641697823922085491086483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284855597098562780654781977 213641697823922085491086483)
    ·
      refine ⟨320462546735883128236629725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213641697823922085491086483 320462546735883128236629725)
      ·
        refine ⟨120173455025956173088736147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320462546735883128236629725 120173455025956173088736147)
        ·
          refine ⟨180260182538934259633104221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120173455025956173088736147 180260182538934259633104221)
          ·
            refine ⟨67597568452100347362414083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180260182538934259633104221 67597568452100347362414083)
            ·
              refine ⟨101396352678150521043621125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67597568452100347362414083 101396352678150521043621125)
              ·
                refine ⟨19011816127153222695678961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101396352678150521043621125 19011816127153222695678961)
                ·
                  refine ⟨14258862095364917021759221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19011816127153222695678961 14258862095364917021759221)
                  ·
                    refine ⟨1336768321440460970789927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14258862095364917021759221 1336768321440460970789927)
                    ·
                      rfl

theorem cell23_7810041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_7810041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810041 prefixEnd_7810041 := by exact prefixLift 7810041
  have htrace : WordTrace (prefixWord ++ tailWord_7810041) baseStart_7810041 baseEnd_7810041 := by
    simpa [prefixWord, tailWord_7810041, baseEnd_7810041] using wordTrace_append hprefix tailTrace_7810041
  have hstable : (prefixWord ++ tailWord_7810041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810041).length < 2 ^ (prefixWord ++ tailWord_7810041).sum := by decide
  have hdescent : baseEnd_7810041 < baseStart_7810041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810098 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_7810098 : Nat := 118140960795 + 7810098 * 2 ^ 59
def prefixEnd_7810098 : Nat := 4983230072969 + 3 ^ 40 * 7810098 * 2
def baseEnd_7810098 : Nat := 4010334232718689189357019

theorem tailTrace_7810098 : CollatzResearch.WordTrace tailWord_7810098 prefixEnd_7810098 4010334232718689189357019 := by
  unfold tailWord_7810098
  simp only [CollatzResearch.WordTrace]
  refine ⟨71214419014839069847401737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189905117372904186259737965 71214419014839069847401737)
  ·
    refine ⟨53410814261129302385551303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71214419014839069847401737 53410814261129302385551303)
    ·
      refine ⟨80116221391693953578326955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53410814261129302385551303 80116221391693953578326955)
      ·
        refine ⟨120174332087540930367490433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80116221391693953578326955 120174332087540930367490433)
        ·
          refine ⟨90130749065655697775617825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120174332087540930367490433 90130749065655697775617825)
          ·
            refine ⟨67598061799241773331713369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90130749065655697775617825 67598061799241773331713369)
            ·
              refine ⟨50698546349431329998785027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67598061799241773331713369 50698546349431329998785027)
              ·
                refine ⟨76047819524146994998177541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50698546349431329998785027 76047819524146994998177541)
                ·
                  refine ⟨14258966160777561562158289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76047819524146994998177541 14258966160777561562158289)
                  ·
                    refine ⟨10694224620583171171618717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14258966160777561562158289 10694224620583171171618717)
                    ·
                      refine ⟨4010334232718689189357019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10694224620583171171618717 4010334232718689189357019)
                      ·
                        rfl

theorem cell23_7810098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_7810098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810098 prefixEnd_7810098 := by exact prefixLift 7810098
  have htrace : WordTrace (prefixWord ++ tailWord_7810098) baseStart_7810098 baseEnd_7810098 := by
    simpa [prefixWord, tailWord_7810098, baseEnd_7810098] using wordTrace_append hprefix tailTrace_7810098
  have hstable : (prefixWord ++ tailWord_7810098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810098).length < 2 ^ (prefixWord ++ tailWord_7810098).sum := by decide
  have hdescent : baseEnd_7810098 < baseStart_7810098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810105 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 3, 4]
def baseStart_7810105 : Nat := 118140960795 + 7810105 * 2 ^ 59
def prefixEnd_7810105 : Nat := 4983230072969 + 3 ^ 40 * 7810105 * 2
def baseEnd_7810105 : Nat := 1336779275694423553989829

theorem tailTrace_7810105 : CollatzResearch.WordTrace tailWord_7810105 prefixEnd_7810105 1336779275694423553989829 := by
  unfold tailWord_7810105
  simp only [CollatzResearch.WordTrace]
  refine ⟨284857931370330919585111769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189905287580220613056741179 284857931370330919585111769)
  ·
    refine ⟨213643448527748189688833827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284857931370330919585111769 213643448527748189688833827)
    ·
      refine ⟨320465172791622284533250741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213643448527748189688833827 320465172791622284533250741)
      ·
        refine ⟨30043609949214589174992257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320465172791622284533250741 30043609949214589174992257)
        ·
          refine ⟨22532707461910941881244193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30043609949214589174992257 22532707461910941881244193)
          ·
            refine ⟨16899530596433206410933145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22532707461910941881244193 16899530596433206410933145)
            ·
              refine ⟨12674647947324904808199859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16899530596433206410933145 12674647947324904808199859)
              ·
                refine ⟨19011971920987357212299789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12674647947324904808199859 19011971920987357212299789)
                ·
                  refine ⟨7129489470370258954612421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19011971920987357212299789 7129489470370258954612421)
                  ·
                    refine ⟨1336779275694423553989829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7129489470370258954612421 1336779275694423553989829)
                    ·
                      rfl

theorem cell23_7810105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 4].length) (baseStart_7810105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810105 prefixEnd_7810105 := by exact prefixLift 7810105
  have htrace : WordTrace (prefixWord ++ tailWord_7810105) baseStart_7810105 baseEnd_7810105 := by
    simpa [prefixWord, tailWord_7810105, baseEnd_7810105] using wordTrace_append hprefix tailTrace_7810105
  have hstable : (prefixWord ++ tailWord_7810105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810105).length < 2 ^ (prefixWord ++ tailWord_7810105).sum := by decide
  have hdescent : baseEnd_7810105 < baseStart_7810105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810161 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 5, 6]
def baseStart_7810161 : Nat := 118140960795 + 7810161 * 2 ^ 59
def prefixEnd_7810161 : Nat := 4983230072969 + 3 ^ 40 * 7810161 * 2
def baseEnd_7810161 : Nat := 1336788860666640814289743

theorem tailTrace_7810161 : CollatzResearch.WordTrace tailWord_7810161 prefixEnd_7810161 1336788860666640814289743 := by
  unfold tailWord_7810161
  simp only [CollatzResearch.WordTrace]
  refine ⟨284859973858128041149150337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189906649238752027432766891 284859973858128041149150337)
  ·
    refine ⟨213644980393596030861862753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284859973858128041149150337 213644980393596030861862753)
    ·
      refine ⟨160233735295197023146397065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213644980393596030861862753 160233735295197023146397065)
      ·
        refine ⟨120175301471397767359797799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160233735295197023146397065 120175301471397767359797799)
        ·
          refine ⟨180262952207096651039696699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120175301471397767359797799 180262952207096651039696699)
          ·
            refine ⟨270394428310644976559545049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180262952207096651039696699 270394428310644976559545049)
            ·
              refine ⟨202795821232983732419658787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270394428310644976559545049 202795821232983732419658787)
              ·
                refine ⟨304193731849475598629488181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202795821232983732419658787 304193731849475598629488181)
                ·
                  refine ⟨28518162360888337371514517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304193731849475598629488181 28518162360888337371514517)
                  ·
                    refine ⟨1336788860666640814289743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28518162360888337371514517 1336788860666640814289743)
                    ·
                      rfl

theorem cell23_7810161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_7810161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810161 prefixEnd_7810161 := by exact prefixLift 7810161
  have htrace : WordTrace (prefixWord ++ tailWord_7810161) baseStart_7810161 baseEnd_7810161 := by
    simpa [prefixWord, tailWord_7810161, baseEnd_7810161] using wordTrace_append hprefix tailTrace_7810161
  have hstable : (prefixWord ++ tailWord_7810161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810161).length < 2 ^ (prefixWord ++ tailWord_7810161).sum := by decide
  have hdescent : baseEnd_7810161 < baseStart_7810161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810185 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 4]
def baseStart_7810185 : Nat := 118140960795 + 7810185 * 2 ^ 59
def prefixEnd_7810185 : Nat := 4983230072969 + 3 ^ 40 * 7810185 * 2
def baseEnd_7810185 : Nat := 4010378905535630348969119

theorem tailTrace_7810185 : CollatzResearch.WordTrace tailWord_7810185 prefixEnd_7810185 4010378905535630348969119 := by
  unfold tailWord_7810185
  simp only [CollatzResearch.WordTrace]
  refine ⟨284860849210041093248024009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189907232806694062165349339 284860849210041093248024009)
  ·
    refine ⟨213645636907530819936018007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284860849210041093248024009 213645636907530819936018007)
    ·
      refine ⟨320468455361296229904027011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213645636907530819936018007 320468455361296229904027011)
      ·
        refine ⟨480702683041944344856040517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320468455361296229904027011 480702683041944344856040517)
        ·
          refine ⟨90131753070364564660507597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 480702683041944344856040517 90131753070364564660507597)
          ·
            refine ⟨33799407401386711747690349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90131753070364564660507597 33799407401386711747690349)
            ·
              refine ⟨12674777775520016905383881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33799407401386711747690349 12674777775520016905383881)
              ·
                refine ⟨9506083331640012679037911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12674777775520016905383881 9506083331640012679037911)
                ·
                  refine ⟨14259124997460019018556867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506083331640012679037911 14259124997460019018556867)
                  ·
                    refine ⟨21388687496190028527835301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14259124997460019018556867 21388687496190028527835301)
                    ·
                      refine ⟨4010378905535630348969119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21388687496190028527835301 4010378905535630348969119)
                      ·
                        rfl

theorem cell23_7810185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 4].length) (baseStart_7810185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810185 prefixEnd_7810185 := by exact prefixLift 7810185
  have htrace : WordTrace (prefixWord ++ tailWord_7810185) baseStart_7810185 baseEnd_7810185 := by
    simpa [prefixWord, tailWord_7810185, baseEnd_7810185] using wordTrace_append hprefix tailTrace_7810185
  have hstable : (prefixWord ++ tailWord_7810185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810185).length < 2 ^ (prefixWord ++ tailWord_7810185).sum := by decide
  have hdescent : baseEnd_7810185 < baseStart_7810185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810212 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_7810212 : Nat := 118140960795 + 7810212 * 2 ^ 59
def prefixEnd_7810212 : Nat := 4983230072969 + 3 ^ 40 * 7810212 * 2
def baseEnd_7810212 : Nat := 1336797589837767247777165

theorem tailTrace_7810212 : CollatzResearch.WordTrace tailWord_7810212 prefixEnd_7810212 1336797589837767247777165 := by
  unfold tailWord_7810212
  simp only [CollatzResearch.WordTrace]
  refine ⟨142430916990471638429628445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189907889320628851239504593 142430916990471638429628445)
  ·
    refine ⟨53411593871426864411110667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142430916990471638429628445 53411593871426864411110667)
    ·
      refine ⟨80117390807140296616666001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53411593871426864411110667 80117390807140296616666001)
      ·
        refine ⟨60088043105355222462499501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80117390807140296616666001 60088043105355222462499501)
        ·
          refine ⟨22533016164508208423437313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60088043105355222462499501 22533016164508208423437313)
          ·
            refine ⟨16899762123381156317577985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22533016164508208423437313 16899762123381156317577985)
            ·
              refine ⟨12674821592535867238183489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16899762123381156317577985 12674821592535867238183489)
              ·
                refine ⟨9506116194401900428637617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12674821592535867238183489 9506116194401900428637617)
                ·
                  refine ⟨7129587145801425321478213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9506116194401900428637617 7129587145801425321478213)
                  ·
                    refine ⟨1336797589837767247777165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7129587145801425321478213 1336797589837767247777165)
                    ·
                      rfl

theorem cell23_7810212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_7810212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810212 prefixEnd_7810212 := by exact prefixLift 7810212
  have htrace : WordTrace (prefixWord ++ tailWord_7810212) baseStart_7810212 baseEnd_7810212 := by
    simpa [prefixWord, tailWord_7810212, baseEnd_7810212] using wordTrace_append hprefix tailTrace_7810212
  have hstable : (prefixWord ++ tailWord_7810212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810212).length < 2 ^ (prefixWord ++ tailWord_7810212).sum := by decide
  have hdescent : baseEnd_7810212 < baseStart_7810212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810225 : List Nat := [1, 2, 2, 5, 1, 3, 1, 8]
def baseStart_7810225 : Nat := 118140960795 + 7810225 * 2 ^ 59
def prefixEnd_7810225 : Nat := 4983230072969 + 3 ^ 40 * 7810225 * 2
def baseEnd_7810225 : Nat := 148533312768955933054405

theorem tailTrace_7810225 : CollatzResearch.WordTrace tailWord_7810225 prefixEnd_7810225 148533312768955933054405 := by
  unfold tailWord_7810225
  simp only [CollatzResearch.WordTrace]
  refine ⟨284862308129896180079480129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189908205419930786719653419 284862308129896180079480129)
  ·
    refine ⟨213646731097422135059610097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284862308129896180079480129 213646731097422135059610097)
    ·
      refine ⟨160235048323066601294707573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213646731097422135059610097 160235048323066601294707573)
      ·
        refine ⟨15022035780287493871378835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160235048323066601294707573 15022035780287493871378835)
        ·
          refine ⟨22533053670431240807068253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15022035780287493871378835 22533053670431240807068253)
          ·
            refine ⟨8449895126411715302650595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22533053670431240807068253 8449895126411715302650595)
            ·
              refine ⟨12674842689617572953975893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8449895126411715302650595 12674842689617572953975893)
              ·
                refine ⟨148533312768955933054405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12674842689617572953975893 148533312768955933054405)
                ·
                  rfl

theorem cell23_7810225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 8].length) (baseStart_7810225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810225 prefixEnd_7810225 := by exact prefixLift 7810225
  have htrace : WordTrace (prefixWord ++ tailWord_7810225) baseStart_7810225 baseEnd_7810225 := by
    simpa [prefixWord, tailWord_7810225, baseEnd_7810225] using wordTrace_append hprefix tailTrace_7810225
  have hstable : (prefixWord ++ tailWord_7810225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810225).length < 2 ^ (prefixWord ++ tailWord_7810225).sum := by decide
  have hdescent : baseEnd_7810225 < baseStart_7810225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810253 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7810253 : Nat := 118140960795 + 7810253 * 2 ^ 59
def prefixEnd_7810253 : Nat := 4983230072969 + 3 ^ 40 * 7810253 * 2
def baseEnd_7810253 : Nat := 4010413822220136082918807

theorem tailTrace_7810253 : CollatzResearch.WordTrace tailWord_7810253 prefixEnd_7810253 4010413822220136082918807 := by
  unfold tailWord_7810253
  simp only [CollatzResearch.WordTrace]
  refine ⟨284863329373794740861499413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189908886249196493907666275 284863329373794740861499413)
  ·
    refine ⟨13352968564396628477882785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 284863329373794740861499413 13352968564396628477882785)
    ·
      refine ⟨10014726423297471358412089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13352968564396628477882785 10014726423297471358412089)
      ·
        refine ⟨7511044817473103518809067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10014726423297471358412089 7511044817473103518809067)
        ·
          refine ⟨11266567226209655278213601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7511044817473103518809067 11266567226209655278213601)
          ·
            refine ⟨8449925419657241458660201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11266567226209655278213601 8449925419657241458660201)
            ·
              refine ⟨6337444064742931093995151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8449925419657241458660201 6337444064742931093995151)
              ·
                refine ⟨9506166097114396640992727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337444064742931093995151 9506166097114396640992727)
                ·
                  refine ⟨14259249145671594961489091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506166097114396640992727 14259249145671594961489091)
                  ·
                    refine ⟨21388873718507392442233637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14259249145671594961489091 21388873718507392442233637)
                    ·
                      refine ⟨4010413822220136082918807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21388873718507392442233637 4010413822220136082918807)
                      ·
                        rfl

theorem cell23_7810253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7810253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810253 prefixEnd_7810253 := by exact prefixLift 7810253
  have htrace : WordTrace (prefixWord ++ tailWord_7810253) baseStart_7810253 baseEnd_7810253 := by
    simpa [prefixWord, tailWord_7810253, baseEnd_7810253] using wordTrace_append hprefix tailTrace_7810253
  have hstable : (prefixWord ++ tailWord_7810253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810253).length < 2 ^ (prefixWord ++ tailWord_7810253).sum := by decide
  have hdescent : baseEnd_7810253 < baseStart_7810253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810269 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7810269 : Nat := 118140960795 + 7810269 * 2 ^ 59
def prefixEnd_7810269 : Nat := 4983230072969 + 3 ^ 40 * 7810269 * 2
def baseEnd_7810269 : Nat := 4010422037910608020318733

theorem tailTrace_7810269 : CollatzResearch.WordTrace tailWord_7810269 prefixEnd_7810269 4010422037910608020318733 := by
  unfold tailWord_7810269
  simp only [CollatzResearch.WordTrace]
  refine ⟨284863912941736775594081861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189909275294491183729387907 284863912941736775594081861)
  ·
    refine ⟨53411983676575645423890349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284863912941736775594081861 53411983676575645423890349)
    ·
      refine ⟨20029493878715867033958881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53411983676575645423890349 20029493878715867033958881)
      ·
        refine ⟨15022120409036900275469161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20029493878715867033958881 15022120409036900275469161)
        ·
          refine ⟨11266590306777675206601871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15022120409036900275469161 11266590306777675206601871)
          ·
            refine ⟨16899885460166512809902807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11266590306777675206601871 16899885460166512809902807)
            ·
              refine ⟨25349828190249769214854211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16899885460166512809902807 25349828190249769214854211)
              ·
                refine ⟨38024742285374653822281317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25349828190249769214854211 38024742285374653822281317)
                ·
                  refine ⟨7129639178507747591677747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38024742285374653822281317 7129639178507747591677747)
                  ·
                    refine ⟨10694458767761621387516621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7129639178507747591677747 10694458767761621387516621)
                    ·
                      refine ⟨4010422037910608020318733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10694458767761621387516621 4010422037910608020318733)
                      ·
                        rfl

theorem cell23_7810269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7810269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810269 prefixEnd_7810269 := by exact prefixLift 7810269
  have htrace : WordTrace (prefixWord ++ tailWord_7810269) baseStart_7810269 baseEnd_7810269 := by
    simpa [prefixWord, tailWord_7810269, baseEnd_7810269] using wordTrace_append hprefix tailTrace_7810269
  have hstable : (prefixWord ++ tailWord_7810269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810269).length < 2 ^ (prefixWord ++ tailWord_7810269).sum := by decide
  have hdescent : baseEnd_7810269 < baseStart_7810269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810285 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_7810285 : Nat := 118140960795 + 7810285 * 2 ^ 59
def prefixEnd_7810285 : Nat := 4983230072969 + 3 ^ 40 * 7810285 * 2
def baseEnd_7810285 : Nat := 1336810084533693319239553

theorem tailTrace_7810285 : CollatzResearch.WordTrace tailWord_7810285 prefixEnd_7810285 1336810084533693319239553 := by
  unfold tailWord_7810285
  simp only [CollatzResearch.WordTrace]
  refine ⟨284864496509678810326664309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189909664339785873551109539 284864496509678810326664309)
  ·
    refine ⟨26706046547782388468124779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284864496509678810326664309 26706046547782388468124779)
    ·
      refine ⟨40059069821673582702187169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26706046547782388468124779 40059069821673582702187169)
      ·
        refine ⟨30044302366255187026640377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40059069821673582702187169 30044302366255187026640377)
        ·
          refine ⟨22533226774691390269980283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30044302366255187026640377 22533226774691390269980283)
          ·
            refine ⟨33799840162037085404970425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22533226774691390269980283 33799840162037085404970425)
            ·
              refine ⟨25349880121527814053727819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33799840162037085404970425 25349880121527814053727819)
              ·
                refine ⟨38024820182291721080591729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25349880121527814053727819 38024820182291721080591729)
                ·
                  refine ⟨28518615136718790810443797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38024820182291721080591729 28518615136718790810443797)
                  ·
                    refine ⟨1336810084533693319239553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28518615136718790810443797 1336810084533693319239553)
                    ·
                      rfl

theorem cell23_7810285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_7810285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810285 prefixEnd_7810285 := by exact prefixLift 7810285
  have htrace : WordTrace (prefixWord ++ tailWord_7810285) baseStart_7810285 baseEnd_7810285 := by
    simpa [prefixWord, tailWord_7810285, baseEnd_7810285] using wordTrace_append hprefix tailTrace_7810285
  have hstable : (prefixWord ++ tailWord_7810285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810285).length < 2 ^ (prefixWord ++ tailWord_7810285).sum := by decide
  have hdescent : baseEnd_7810285 < baseStart_7810285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810298 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 7]
def baseStart_7810298 : Nat := 118140960795 + 7810298 * 2 ^ 59
def prefixEnd_7810298 : Nat := 4983230072969 + 3 ^ 40 * 7810298 * 2
def baseEnd_7810298 : Nat := 445604103205509822984011

theorem tailTrace_7810298 : CollatzResearch.WordTrace tailWord_7810298 prefixEnd_7810298 445604103205509822984011 := by
  unfold tailWord_7810298
  simp only [CollatzResearch.WordTrace]
  refine ⟨71216242664657928386721887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189909980439087809031258365 71216242664657928386721887)
  ·
    refine ⟨106824363996986892580082831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71216242664657928386721887 106824363996986892580082831)
    ·
      refine ⟨160236545995480338870124247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106824363996986892580082831 160236545995480338870124247)
      ·
        refine ⟨240354818993220508305186371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160236545995480338870124247 240354818993220508305186371)
        ·
          refine ⟨360532228489830762457779557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240354818993220508305186371 360532228489830762457779557)
          ·
            refine ⟨67599792841843267960833667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360532228489830762457779557 67599792841843267960833667)
            ·
              refine ⟨101399689262764901941250501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67599792841843267960833667 101399689262764901941250501)
              ·
                refine ⟨19012441736768419113984469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101399689262764901941250501 19012441736768419113984469)
                ·
                  refine ⟨445604103205509822984011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19012441736768419113984469 445604103205509822984011)
                  ·
                    rfl

theorem cell23_7810298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_7810298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810298 prefixEnd_7810298 := by exact prefixLift 7810298
  have htrace : WordTrace (prefixWord ++ tailWord_7810298) baseStart_7810298 baseEnd_7810298 := by
    simpa [prefixWord, tailWord_7810298, baseEnd_7810298] using wordTrace_append hprefix tailTrace_7810298
  have hstable : (prefixWord ++ tailWord_7810298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810298).length < 2 ^ (prefixWord ++ tailWord_7810298).sum := by decide
  have hdescent : baseEnd_7810298 < baseStart_7810298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810372 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7810372 : Nat := 118140960795 + 7810372 * 2 ^ 59
def prefixEnd_7810372 : Nat := 4983230072969 + 3 ^ 40 * 7810372 * 2
def baseEnd_7810372 : Nat := 4010474926418021117330759

theorem tailTrace_7810372 : CollatzResearch.WordTrace tailWord_7810372 prefixEnd_7810372 4010474926418021117330759 := by
  unfold tailWord_7810372
  simp only [CollatzResearch.WordTrace]
  refine ⟨142433834830181812092540685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189911779773575749456720913 142433834830181812092540685)
  ·
    refine ⟨53412688061318179534702757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142433834830181812092540685 53412688061318179534702757)
    ·
      refine ⟨10014879011497158662756767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53412688061318179534702757 10014879011497158662756767)
      ·
        refine ⟨15022318517245737994135151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10014879011497158662756767 15022318517245737994135151)
        ·
          refine ⟨22533477775868606991202727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15022318517245737994135151 22533477775868606991202727)
          ·
            refine ⟨33800216663802910486804091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22533477775868606991202727 33800216663802910486804091)
            ·
              refine ⟨50700324995704365730206137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33800216663802910486804091 50700324995704365730206137)
              ·
                refine ⟨38025243746778274297654603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50700324995704365730206137 38025243746778274297654603)
                ·
                  refine ⟨57037865620167411446481905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38025243746778274297654603 57037865620167411446481905)
                  ·
                    refine ⟨42778399215125558584861429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57037865620167411446481905 42778399215125558584861429)
                    ·
                      refine ⟨4010474926418021117330759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42778399215125558584861429 4010474926418021117330759)
                      ·
                        rfl

theorem cell23_7810372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7810372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810372 prefixEnd_7810372 := by exact prefixLift 7810372
  have htrace : WordTrace (prefixWord ++ tailWord_7810372) baseStart_7810372 baseEnd_7810372 := by
    simpa [prefixWord, tailWord_7810372, baseEnd_7810372] using wordTrace_append hprefix tailTrace_7810372
  have hstable : (prefixWord ++ tailWord_7810372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810372).length < 2 ^ (prefixWord ++ tailWord_7810372).sum := by decide
  have hdescent : baseEnd_7810372 < baseStart_7810372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810382 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2]
def baseStart_7810382 : Nat := 118140960795 + 7810382 * 2 ^ 59
def prefixEnd_7810382 : Nat := 4983230072969 + 3 ^ 40 * 7810382 * 2
def baseEnd_7810382 : Nat := 4010480061224566078205713

theorem tailTrace_7810382 : CollatzResearch.WordTrace tailWord_7810382 prefixEnd_7810382 4010480061224566078205713 := by
  unfold tailWord_7810382
  simp only [CollatzResearch.WordTrace]
  refine ⟨35608504298790924486618175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189912022926884930595296933 35608504298790924486618175)
  ·
    refine ⟨53412756448186386729927263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35608504298790924486618175 53412756448186386729927263)
    ·
      refine ⟨80119134672279580094890895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53412756448186386729927263 80119134672279580094890895)
      ·
        refine ⟨120178702008419370142336343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80119134672279580094890895 120178702008419370142336343)
        ·
          refine ⟨180268053012629055213504515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120178702008419370142336343 180268053012629055213504515)
          ·
            refine ⟨270402079518943582820256773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180268053012629055213504515 270402079518943582820256773)
            ·
              refine ⟨50700389909801921778798145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270402079518943582820256773 50700389909801921778798145)
              ·
                refine ⟨38025292432351441334098609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50700389909801921778798145 38025292432351441334098609)
                ·
                  refine ⟨28518969324263581000573957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38025292432351441334098609 28518969324263581000573957)
                  ·
                    refine ⟨5347306748299421437607617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28518969324263581000573957 5347306748299421437607617)
                    ·
                      refine ⟨4010480061224566078205713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5347306748299421437607617 4010480061224566078205713)
                      ·
                        rfl

theorem cell23_7810382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_7810382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810382 prefixEnd_7810382 := by exact prefixLift 7810382
  have htrace : WordTrace (prefixWord ++ tailWord_7810382) baseStart_7810382 baseEnd_7810382 := by
    simpa [prefixWord, tailWord_7810382, baseEnd_7810382] using wordTrace_append hprefix tailTrace_7810382
  have hstable : (prefixWord ++ tailWord_7810382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810382).length < 2 ^ (prefixWord ++ tailWord_7810382).sum := by decide
  have hdescent : baseEnd_7810382 < baseStart_7810382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810402 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_7810402 : Nat := 118140960795 + 7810402 * 2 ^ 59
def prefixEnd_7810402 : Nat := 4983230072969 + 3 ^ 40 * 7810402 * 2
def baseEnd_7810402 : Nat := 4010490330837655999955621

theorem tailTrace_7810402 : CollatzResearch.WordTrace tailWord_7810402 prefixEnd_7810402 4010490330837655999955621 := by
  unfold tailWord_7810402
  simp only [CollatzResearch.WordTrace]
  refine ⟨71217190962563734827168365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189912509233503292872448973 71217190962563734827168365)
  ·
    refine ⟨26706446610961400560188137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71217190962563734827168365 26706446610961400560188137)
    ·
      refine ⟨20029834958221050420141103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26706446610961400560188137 20029834958221050420141103)
      ·
        refine ⟨30044752437331575630211655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20029834958221050420141103 30044752437331575630211655)
        ·
          refine ⟨45067128655997363445317483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30044752437331575630211655 45067128655997363445317483)
          ·
            refine ⟨67600692983996045167976225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45067128655997363445317483 67600692983996045167976225)
            ·
              refine ⟨50700519737997033875982169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67600692983996045167976225 50700519737997033875982169)
              ·
                refine ⟨38025389803497775406986627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50700519737997033875982169 38025389803497775406986627)
                ·
                  refine ⟨57038084705246663110479941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38025389803497775406986627 57038084705246663110479941)
                  ·
                    refine ⟨10694640882233749333214989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57038084705246663110479941 10694640882233749333214989)
                    ·
                      refine ⟨4010490330837655999955621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10694640882233749333214989 4010490330837655999955621)
                      ·
                        rfl

theorem cell23_7810402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_7810402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810402 prefixEnd_7810402 := by exact prefixLift 7810402
  have htrace : WordTrace (prefixWord ++ tailWord_7810402) baseStart_7810402 baseEnd_7810402 := by
    simpa [prefixWord, tailWord_7810402, baseEnd_7810402] using wordTrace_append hprefix tailTrace_7810402
  have hstable : (prefixWord ++ tailWord_7810402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810402).length < 2 ^ (prefixWord ++ tailWord_7810402).sum := by decide
  have hdescent : baseEnd_7810402 < baseStart_7810402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810405 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 6]
def baseStart_7810405 : Nat := 118140960795 + 7810405 * 2 ^ 59
def prefixEnd_7810405 : Nat := 4983230072969 + 3 ^ 40 * 7810405 * 2
def baseEnd_7810405 : Nat := 445610207919957720913123

theorem tailTrace_7810405 : CollatzResearch.WordTrace tailWord_7810405 prefixEnd_7810405 445610207919957720913123 := by
  unfold tailWord_7810405
  simp only [CollatzResearch.WordTrace]
  refine ⟨284868873269244070821032669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189912582179496047214021779 284868873269244070821032669)
  ·
    refine ⟨106825827475966526557887251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284868873269244070821032669 106825827475966526557887251)
    ·
      refine ⟨160238741213949789836830877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106825827475966526557887251 160238741213949789836830877)
      ·
        refine ⟨60089527955231171188811579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160238741213949789836830877 60089527955231171188811579)
        ·
          refine ⟨90134291932846756783217369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60089527955231171188811579 90134291932846756783217369)
          ·
            refine ⟨67600718949635067587413027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90134291932846756783217369 67600718949635067587413027)
            ·
              refine ⟨101401078424452601381119541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67600718949635067587413027 101401078424452601381119541)
              ·
                refine ⟨9506351102292431379479957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101401078424452601381119541 9506351102292431379479957)
                ·
                  refine ⟨445610207919957720913123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9506351102292431379479957 445610207919957720913123)
                  ·
                    rfl

theorem cell23_7810405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_7810405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810405 prefixEnd_7810405 := by exact prefixLift 7810405
  have htrace : WordTrace (prefixWord ++ tailWord_7810405) baseStart_7810405 baseEnd_7810405 := by
    simpa [prefixWord, tailWord_7810405, baseEnd_7810405] using wordTrace_append hprefix tailTrace_7810405
  have hstable : (prefixWord ++ tailWord_7810405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810405).length < 2 ^ (prefixWord ++ tailWord_7810405).sum := by decide
  have hdescent : baseEnd_7810405 < baseStart_7810405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810500 : List Nat := [2, 3, 3, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_7810500 : Nat := 118140960795 + 7810500 * 2 ^ 59
def prefixEnd_7810500 : Nat := 4983230072969 + 3 ^ 40 * 7810500 * 2
def baseEnd_7810500 : Nat := 4010540651941796616530171

theorem tailTrace_7810500 : CollatzResearch.WordTrace tailWord_7810500 prefixEnd_7810500 4010540651941796616530171 := by
  unfold tailWord_7810500
  simp only [CollatzResearch.WordTrace]
  refine ⟨142436169101949951022870477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189914892135933268030493969 142436169101949951022870477)
  ·
    refine ⟨53413563413231231633576429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142436169101949951022870477 53413563413231231633576429)
    ·
      refine ⟨20030086279961711862591161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53413563413231231633576429 20030086279961711862591161)
      ·
        refine ⟨15022564709971283896943371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20030086279961711862591161 15022564709971283896943371)
        ·
          refine ⟨22533847064956925845415057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15022564709971283896943371 22533847064956925845415057)
          ·
            refine ⟨16900385298717694384061293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22533847064956925845415057 16900385298717694384061293)
            ·
              refine ⟨6337644487019135394022985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16900385298717694384061293 6337644487019135394022985)
              ·
                refine ⟨4753233365264351545517239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6337644487019135394022985 4753233365264351545517239)
                ·
                  refine ⟨7129850047896527318275859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753233365264351545517239 7129850047896527318275859)
                  ·
                    refine ⟨10694775071844790977413789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7129850047896527318275859 10694775071844790977413789)
                    ·
                      refine ⟨4010540651941796616530171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10694775071844790977413789 4010540651941796616530171)
                      ·
                        rfl

theorem cell23_7810500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_7810500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810500 prefixEnd_7810500 := by exact prefixLift 7810500
  have htrace : WordTrace (prefixWord ++ tailWord_7810500) baseStart_7810500 baseEnd_7810500 := by
    simpa [prefixWord, tailWord_7810500, baseEnd_7810500] using wordTrace_append hprefix tailTrace_7810500
  have hstable : (prefixWord ++ tailWord_7810500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810500).length < 2 ^ (prefixWord ++ tailWord_7810500).sum := by decide
  have hdescent : baseEnd_7810500 < baseStart_7810500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810506 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2]
def baseStart_7810506 : Nat := 118140960795 + 7810506 * 2 ^ 59
def prefixEnd_7810506 : Nat := 4983230072969 + 3 ^ 40 * 7810506 * 2
def baseEnd_7810506 : Nat := 4010543732825723593055143

theorem tailTrace_7810506 : CollatzResearch.WordTrace tailWord_7810506 prefixEnd_7810506 4010543732825723593055143 := by
  unfold tailWord_7810506
  simp only [CollatzResearch.WordTrace]
  refine ⟨71218139260469541267614843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189915038027918776713639581 71218139260469541267614843)
  ·
    refine ⟨106827208890704311901422265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71218139260469541267614843 106827208890704311901422265)
    ·
      refine ⟨80120406668028233926066699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106827208890704311901422265 80120406668028233926066699)
      ·
        refine ⟨120180610002042350889100049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80120406668028233926066699 120180610002042350889100049)
        ·
          refine ⟨90135457501531763166825037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120180610002042350889100049 90135457501531763166825037)
          ·
            refine ⟨33800796563074411187559389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90135457501531763166825037 33800796563074411187559389)
            ·
              refine ⟨12675298711152904195334771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33800796563074411187559389 12675298711152904195334771)
              ·
                refine ⟨19012948066729356293002157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12675298711152904195334771 19012948066729356293002157)
                ·
                  refine ⟨7129855525023508609875809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19012948066729356293002157 7129855525023508609875809)
                  ·
                    refine ⟨5347391643767631457406857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7129855525023508609875809 5347391643767631457406857)
                    ·
                      refine ⟨4010543732825723593055143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5347391643767631457406857 4010543732825723593055143)
                      ·
                        rfl

theorem cell23_7810506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_7810506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810506 prefixEnd_7810506 := by exact prefixLift 7810506
  have htrace : WordTrace (prefixWord ++ tailWord_7810506) baseStart_7810506 baseEnd_7810506 := by
    simpa [prefixWord, tailWord_7810506, baseEnd_7810506] using wordTrace_append hprefix tailTrace_7810506
  have hstable : (prefixWord ++ tailWord_7810506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810506).length < 2 ^ (prefixWord ++ tailWord_7810506).sum := by decide
  have hdescent : baseEnd_7810506 < baseStart_7810506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810516 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_7810516 : Nat := 118140960795 + 7810516 * 2 ^ 59
def prefixEnd_7810516 : Nat := 4983230072969 + 3 ^ 40 * 7810516 * 2
def baseEnd_7810516 : Nat := 1336849622544089517976699

theorem tailTrace_7810516 : CollatzResearch.WordTrace tailWord_7810516 prefixEnd_7810516 1336849622544089517976699 := by
  unfold tailWord_7810516
  simp only [CollatzResearch.WordTrace]
  refine ⟨142436460885920968389161701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189915281181227957852215601 142436460885920968389161701)
  ·
    refine ⟨26706836416110181572967819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142436460885920968389161701 26706836416110181572967819)
    ·
      refine ⟨40060254624165272359451729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26706836416110181572967819 40060254624165272359451729)
      ·
        refine ⟨30045190968123954269588797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40060254624165272359451729 30045190968123954269588797)
        ·
          refine ⟨11266946613046482851095799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30045190968123954269588797 11266946613046482851095799)
          ·
            refine ⟨16900419919569724276643699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11266946613046482851095799 16900419919569724276643699)
            ·
              refine ⟨25350629879354586414965549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16900419919569724276643699 25350629879354586414965549)
              ·
                refine ⟨9506486204757969905612081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25350629879354586414965549 9506486204757969905612081)
                ·
                  refine ⟨7129864653568477429209061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9506486204757969905612081 7129864653568477429209061)
                  ·
                    refine ⟨1336849622544089517976699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7129864653568477429209061 1336849622544089517976699)
                    ·
                      rfl

theorem cell23_7810516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_7810516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810516 prefixEnd_7810516 := by exact prefixLift 7810516
  have htrace : WordTrace (prefixWord ++ tailWord_7810516) baseStart_7810516 baseEnd_7810516 := by
    simpa [prefixWord, tailWord_7810516, baseEnd_7810516] using wordTrace_append hprefix tailTrace_7810516
  have hstable : (prefixWord ++ tailWord_7810516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810516).length < 2 ^ (prefixWord ++ tailWord_7810516).sum := by decide
  have hdescent : baseEnd_7810516 < baseStart_7810516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810555 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 4, 6]
def baseStart_7810555 : Nat := 118140960795 + 7810555 * 2 ^ 59
def prefixEnd_7810555 : Nat := 4983230072969 + 3 ^ 40 * 7810555 * 2
def baseEnd_7810555 : Nat := 1336856297792597967114139

theorem tailTrace_7810555 : CollatzResearch.WordTrace tailWord_7810555 prefixEnd_7810555 1336856297792597967114139 := by
  unfold tailWord_7810555
  simp only [CollatzResearch.WordTrace]
  refine ⟨284874344218700646438993119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189916229479133764292662079 284874344218700646438993119)
  ·
    refine ⟨427311516328050969658489679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284874344218700646438993119 427311516328050969658489679)
    ·
      refine ⟨640967274492076454487734519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427311516328050969658489679 640967274492076454487734519)
      ·
        refine ⟨961450911738114681731601779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640967274492076454487734519 961450911738114681731601779)
        ·
          refine ⟨1442176367607172022597402669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961450911738114681731601779 1442176367607172022597402669)
          ·
            refine ⟨540816137852689508474026001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1442176367607172022597402669 540816137852689508474026001)
            ·
              refine ⟨405612103389517131355519501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540816137852689508474026001 405612103389517131355519501)
              ·
                refine ⟨152104538771068924258319813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405612103389517131355519501 152104538771068924258319813)
                ·
                  refine ⟨28519601019575423298434965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152104538771068924258319813 28519601019575423298434965)
                  ·
                    refine ⟨1336856297792597967114139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28519601019575423298434965 1336856297792597967114139)
                    ·
                      rfl

theorem cell23_7810555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 6].length) (baseStart_7810555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810555 prefixEnd_7810555 := by exact prefixLift 7810555
  have htrace : WordTrace (prefixWord ++ tailWord_7810555) baseStart_7810555 baseEnd_7810555 := by
    simpa [prefixWord, tailWord_7810555, baseEnd_7810555] using wordTrace_append hprefix tailTrace_7810555
  have hstable : (prefixWord ++ tailWord_7810555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810555).length < 2 ^ (prefixWord ++ tailWord_7810555).sum := by decide
  have hdescent : baseEnd_7810555 < baseStart_7810555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810579 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 1, 4, 2]
def baseStart_7810579 : Nat := 118140960795 + 7810579 * 2 ^ 59
def prefixEnd_7810579 : Nat := 4983230072969 + 3 ^ 40 * 7810579 * 2
def baseEnd_7810579 : Nat := 4010581216913501807442307

theorem tailTrace_7810579 : CollatzResearch.WordTrace tailWord_7810579 prefixEnd_7810579 4010581216913501807442307 := by
  unfold tailWord_7810579
  simp only [CollatzResearch.WordTrace]
  refine ⟨284875219570613698537866791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189916813047075799025244527 284875219570613698537866791)
  ·
    refine ⟨427312829355920547806800187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284875219570613698537866791 427312829355920547806800187)
    ·
      refine ⟨640969244033880821710200281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427312829355920547806800187 640969244033880821710200281)
      ·
        refine ⟨480726933025410616282650211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640969244033880821710200281 480726933025410616282650211)
        ·
          refine ⟨721090399538115924423975317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480726933025410616282650211 721090399538115924423975317)
          ·
            refine ⟨33801112478349183957373843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 721090399538115924423975317 33801112478349183957373843)
            ·
              refine ⟨50701668717523775936060765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33801112478349183957373843 50701668717523775936060765)
              ·
                refine ⟨19013125769071415976022787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50701668717523775936060765 19013125769071415976022787)
                ·
                  refine ⟨28519688653607123964034181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19013125769071415976022787 28519688653607123964034181)
                  ·
                    refine ⟨5347441622551335743256409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28519688653607123964034181 5347441622551335743256409)
                    ·
                      refine ⟨4010581216913501807442307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5347441622551335743256409 4010581216913501807442307)
                      ·
                        rfl

theorem cell23_7810579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 4, 2].length) (baseStart_7810579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810579 prefixEnd_7810579 := by exact prefixLift 7810579
  have htrace : WordTrace (prefixWord ++ tailWord_7810579) baseStart_7810579 baseEnd_7810579 := by
    simpa [prefixWord, tailWord_7810579, baseEnd_7810579] using wordTrace_append hprefix tailTrace_7810579
  have hstable : (prefixWord ++ tailWord_7810579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810579).length < 2 ^ (prefixWord ++ tailWord_7810579).sum := by decide
  have hdescent : baseEnd_7810579 < baseStart_7810579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810602 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 9]
def baseStart_7810602 : Nat := 118140960795 + 7810602 * 2 ^ 59
def prefixEnd_7810602 : Nat := 4983230072969 + 3 ^ 40 * 7810602 * 2
def baseEnd_7810602 : Nat := 445621447440950579717189

theorem tailTrace_7810602 : CollatzResearch.WordTrace tailWord_7810602 prefixEnd_7810602 445621447440950579717189 := by
  unfold tailWord_7810602
  simp only [CollatzResearch.WordTrace]
  refine ⟨71219014612382593366488515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189917372299686915643969373 71219014612382593366488515)
  ·
    refine ⟨106828521918573890049732773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71219014612382593366488515 106828521918573890049732773)
    ·
      refine ⟨20030347859732604384324895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106828521918573890049732773 20030347859732604384324895)
      ·
        refine ⟨30045521789598906576487343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20030347859732604384324895 30045521789598906576487343)
        ·
          refine ⟨45068282684398359864731015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30045521789598906576487343 45068282684398359864731015)
          ·
            refine ⟨67602424026597539797096523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45068282684398359864731015 67602424026597539797096523)
            ·
              refine ⟨101403636039896309695644785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67602424026597539797096523 101403636039896309695644785)
              ·
                refine ⟨76052727029922232271733589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101403636039896309695644785 76052727029922232271733589)
                ·
                  refine ⟨445621447440950579717189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76052727029922232271733589 445621447440950579717189)
                  ·
                    rfl

theorem cell23_7810602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_7810602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810602 prefixEnd_7810602 := by exact prefixLift 7810602
  have htrace : WordTrace (prefixWord ++ tailWord_7810602) baseStart_7810602 baseEnd_7810602 := by
    simpa [prefixWord, tailWord_7810602, baseEnd_7810602] using wordTrace_append hprefix tailTrace_7810602
  have hstable : (prefixWord ++ tailWord_7810602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810602).length < 2 ^ (prefixWord ++ tailWord_7810602).sum := by decide
  have hdescent : baseEnd_7810602 < baseStart_7810602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810613 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_7810613 : Nat := 118140960795 + 7810613 * 2 ^ 59
def prefixEnd_7810613 : Nat := 4983230072969 + 3 ^ 40 * 7810613 * 2
def baseEnd_7810613 : Nat := 4010598675255754674417151

theorem tailTrace_7810613 : CollatzResearch.WordTrace tailWord_7810613 prefixEnd_7810613 4010598675255754674417151 := by
  unfold tailWord_7810613
  simp only [CollatzResearch.WordTrace]
  refine ⟨284876459652490522344604493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189917639768327014896402995 284876459652490522344604493)
  ·
    refine ⟨106828672369683945879226685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284876459652490522344604493 106828672369683945879226685)
    ·
      refine ⟨40060752138631479704710007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106828672369683945879226685 40060752138631479704710007)
      ·
        refine ⟨60091128207947219557065011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40060752138631479704710007 60091128207947219557065011)
        ·
          refine ⟨90136692311920829335597517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60091128207947219557065011 90136692311920829335597517)
          ·
            refine ⟨33801259616970311000849069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90136692311920829335597517 33801259616970311000849069)
            ·
              refine ⟨12675472356363866625318401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33801259616970311000849069 12675472356363866625318401)
              ·
                refine ⟨9506604267272899968988801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12675472356363866625318401 9506604267272899968988801)
                ·
                  refine ⟨7129953200454674976741601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9506604267272899968988801 7129953200454674976741601)
                  ·
                    refine ⟨5347464900341006232556201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7129953200454674976741601 5347464900341006232556201)
                    ·
                      refine ⟨4010598675255754674417151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5347464900341006232556201 4010598675255754674417151)
                      ·
                        rfl

theorem cell23_7810613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_7810613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810613 prefixEnd_7810613 := by exact prefixLift 7810613
  have htrace : WordTrace (prefixWord ++ tailWord_7810613) baseStart_7810613 baseEnd_7810613 := by
    simpa [prefixWord, tailWord_7810613, baseEnd_7810613] using wordTrace_append hprefix tailTrace_7810613
  have hstable : (prefixWord ++ tailWord_7810613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810613).length < 2 ^ (prefixWord ++ tailWord_7810613).sum := by decide
  have hdescent : baseEnd_7810613 < baseStart_7810613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810682 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_7810682 : Nat := 118140960795 + 7810682 * 2 ^ 59
def prefixEnd_7810682 : Nat := 4983230072969 + 3 ^ 40 * 7810682 * 2
def baseEnd_7810682 : Nat := 4010634105420914904454333

theorem tailTrace_7810682 : CollatzResearch.WordTrace tailWord_7810682 prefixEnd_7810682 4010634105420914904454333 := by
  unfold tailWord_7810682
  simp only [CollatzResearch.WordTrace]
  refine ⟨71219744072310136782216575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189919317526160364752577533 71219744072310136782216575)
  ·
    refine ⟨106829616108465205173324863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71219744072310136782216575 106829616108465205173324863)
    ·
      refine ⟨160244424162697807759987295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106829616108465205173324863 160244424162697807759987295)
      ·
        refine ⟨240366636244046711639980943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160244424162697807759987295 240366636244046711639980943)
        ·
          refine ⟨360549954366070067459971415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240366636244046711639980943 360549954366070067459971415)
          ·
            refine ⟨540824931549105101189957123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360549954366070067459971415 540824931549105101189957123)
            ·
              refine ⟨811237397323657651784935685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540824931549105101189957123 811237397323657651784935685)
              ·
                refine ⟨152107011998185809709675441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 811237397323657651784935685 152107011998185809709675441)
                ·
                  refine ⟨114080258998639357282256581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152107011998185809709675441 114080258998639357282256581)
                  ·
                    refine ⟨21390048562244879490423109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114080258998639357282256581 21390048562244879490423109)
                    ·
                      refine ⟨4010634105420914904454333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21390048562244879490423109 4010634105420914904454333)
                      ·
                        rfl

theorem cell23_7810682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_7810682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810682 prefixEnd_7810682 := by exact prefixLift 7810682
  have htrace : WordTrace (prefixWord ++ tailWord_7810682) baseStart_7810682 baseEnd_7810682 := by
    simpa [prefixWord, tailWord_7810682, baseEnd_7810682] using wordTrace_append hprefix tailTrace_7810682
  have hstable : (prefixWord ++ tailWord_7810682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810682).length < 2 ^ (prefixWord ++ tailWord_7810682).sum := by decide
  have hdescent : baseEnd_7810682 < baseStart_7810682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810732 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_7810732 : Nat := 118140960795 + 7810732 * 2 ^ 59
def prefixEnd_7810732 : Nat := 4983230072969 + 3 ^ 40 * 7810732 * 2
def baseEnd_7810732 : Nat := 4010659779453639708829103

theorem tailTrace_7810732 : CollatzResearch.WordTrace tailWord_7810732 prefixEnd_7810732 4010659779453639708829103 := by
  unfold tailWord_7810732
  simp only [CollatzResearch.WordTrace]
  refine ⟨142440399969529702834093225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189920533292706270445457633 142440399969529702834093225)
  ·
    refine ⟨106830299977147277125569919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142440399969529702834093225 106830299977147277125569919)
    ·
      refine ⟨160245449965720915688354879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106830299977147277125569919 160245449965720915688354879)
      ·
        refine ⟨240368174948581373532532319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160245449965720915688354879 240368174948581373532532319)
        ·
          refine ⟨360552262422872060298798479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240368174948581373532532319 360552262422872060298798479)
          ·
            refine ⟨540828393634308090448197719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360552262422872060298798479 540828393634308090448197719)
            ·
              refine ⟨811242590451462135672296579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540828393634308090448197719 811242590451462135672296579)
              ·
                refine ⟨1216863885677193203508444869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811242590451462135672296579 1216863885677193203508444869)
                ·
                  refine ⟨228161978564473725657833413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216863885677193203508444869 228161978564473725657833413)
                  ·
                    refine ⟨42780370980838823560843765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228161978564473725657833413 42780370980838823560843765)
                    ·
                      refine ⟨4010659779453639708829103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42780370980838823560843765 4010659779453639708829103)
                      ·
                        rfl

theorem cell23_7810732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_7810732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810732 prefixEnd_7810732 := by exact prefixLift 7810732
  have htrace : WordTrace (prefixWord ++ tailWord_7810732) baseStart_7810732 baseEnd_7810732 := by
    simpa [prefixWord, tailWord_7810732, baseEnd_7810732] using wordTrace_append hprefix tailTrace_7810732
  have hstable : (prefixWord ++ tailWord_7810732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810732).length < 2 ^ (prefixWord ++ tailWord_7810732).sum := by decide
  have hdescent : baseEnd_7810732 < baseStart_7810732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810754 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_7810754 : Nat := 118140960795 + 7810754 * 2 ^ 59
def prefixEnd_7810754 : Nat := 4983230072969 + 3 ^ 40 * 7810754 * 2
def baseEnd_7810754 : Nat := 4010671076028038622754003

theorem tailTrace_7810754 : CollatzResearch.WordTrace tailWord_7810754 prefixEnd_7810754 4010671076028038622754003 := by
  unfold tailWord_7810754
  simp only [CollatzResearch.WordTrace]
  refine ⟨71220400586244925856371829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189921068229986468950324877 71220400586244925856371829)
  ·
    refine ⟨6676912554960461799034859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71220400586244925856371829 6676912554960461799034859)
    ·
      refine ⟨10015368832440692698552289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6676912554960461799034859 10015368832440692698552289)
      ·
        refine ⟨7511526624330519523914217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10015368832440692698552289 7511526624330519523914217)
        ·
          refine ⟨5633644968247889642935663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7511526624330519523914217 5633644968247889642935663)
          ·
            refine ⟨8450467452371834464403495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633644968247889642935663 8450467452371834464403495)
            ·
              refine ⟨12675701178557751696605243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8450467452371834464403495 12675701178557751696605243)
              ·
                refine ⟨19013551767836627544907865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12675701178557751696605243 19013551767836627544907865)
                ·
                  refine ⟨14260163825877470658680899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19013551767836627544907865 14260163825877470658680899)
                  ·
                    refine ⟨21390245738816205988021349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14260163825877470658680899 21390245738816205988021349)
                    ·
                      refine ⟨4010671076028038622754003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21390245738816205988021349 4010671076028038622754003)
                      ·
                        rfl

theorem cell23_7810754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_7810754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810754 prefixEnd_7810754 := by exact prefixLift 7810754
  have htrace : WordTrace (prefixWord ++ tailWord_7810754) baseStart_7810754 baseEnd_7810754 := by
    simpa [prefixWord, tailWord_7810754, baseEnd_7810754] using wordTrace_append hprefix tailTrace_7810754
  have hstable : (prefixWord ++ tailWord_7810754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810754).length < 2 ^ (prefixWord ++ tailWord_7810754).sum := by decide
  have hdescent : baseEnd_7810754 < baseStart_7810754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810756 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_7810756 : Nat := 118140960795 + 7810756 * 2 ^ 59
def prefixEnd_7810756 : Nat := 4983230072969 + 3 ^ 40 * 7810756 * 2
def baseEnd_7810756 : Nat := 1336890700996449204976331

theorem tailTrace_7810756 : CollatzResearch.WordTrace tailWord_7810756 prefixEnd_7810756 1336890700996449204976331 := by
  unfold tailWord_7810756
  simp only [CollatzResearch.WordTrace]
  refine ⟨142440837645486228883530061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189921116860648305178040081 142440837645486228883530061)
  ·
    refine ⟨53415314117057335831323773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142440837645486228883530061 53415314117057335831323773)
    ·
      refine ⟨20030742793896500936746415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53415314117057335831323773 20030742793896500936746415)
      ·
        refine ⟨30046114190844751405119623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20030742793896500936746415 30046114190844751405119623)
        ·
          refine ⟨45069171286267127107679435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30046114190844751405119623 45069171286267127107679435)
          ·
            refine ⟨67603756929400690661519153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45069171286267127107679435 67603756929400690661519153)
            ·
              refine ⟨50702817697050517996139365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67603756929400690661519153 50702817697050517996139365)
              ·
                refine ⟨9506778318196972124276131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50702817697050517996139365 9506778318196972124276131)
                ·
                  refine ⟨14260167477295458186414197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506778318196972124276131 14260167477295458186414197)
                  ·
                    refine ⟨1336890700996449204976331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14260167477295458186414197 1336890700996449204976331)
                    ·
                      rfl

theorem cell23_7810756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_7810756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810756 prefixEnd_7810756 := by exact prefixLift 7810756
  have htrace : WordTrace (prefixWord ++ tailWord_7810756) baseStart_7810756 baseEnd_7810756 := by
    simpa [prefixWord, tailWord_7810756, baseEnd_7810756] using wordTrace_append hprefix tailTrace_7810756
  have hstable : (prefixWord ++ tailWord_7810756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810756).length < 2 ^ (prefixWord ++ tailWord_7810756).sum := by decide
  have hdescent : baseEnd_7810756 < baseStart_7810756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810759 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_7810759 : Nat := 118140960795 + 7810759 * 2 ^ 59
def prefixEnd_7810759 : Nat := 4983230072969 + 3 ^ 40 * 7810759 * 2
def baseEnd_7810759 : Nat := 4010673643431311103191479

theorem tailTrace_7810759 : CollatzResearch.WordTrace tailWord_7810759 prefixEnd_7810759 4010673643431311103191479 := by
  unfold tailWord_7810759
  simp only [CollatzResearch.WordTrace]
  refine ⟨284881784709961589279419331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189921189806641059519612887 284881784709961589279419331)
  ·
    refine ⟨427322677064942383919128997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284881784709961589279419331 427322677064942383919128997)
    ·
      refine ⟨80123001949676696984836687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427322677064942383919128997 80123001949676696984836687)
      ·
        refine ⟨120184502924515045477255031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80123001949676696984836687 120184502924515045477255031)
        ·
          refine ⟨180276754386772568215882547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120184502924515045477255031 180276754386772568215882547)
          ·
            refine ⟨270415131580158852323823821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180276754386772568215882547 270415131580158852323823821)
            ·
              refine ⟨101405674342559569621433933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270415131580158852323823821 101405674342559569621433933)
              ·
                refine ⟨38027127878459838608037725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101405674342559569621433933 38027127878459838608037725)
                ·
                  refine ⟨14260172954422439478014147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38027127878459838608037725 14260172954422439478014147)
                  ·
                    refine ⟨21390259431633659217021221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14260172954422439478014147 21390259431633659217021221)
                    ·
                      refine ⟨4010673643431311103191479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21390259431633659217021221 4010673643431311103191479)
                      ·
                        rfl

theorem cell23_7810759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_7810759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810759 prefixEnd_7810759 := by exact prefixLift 7810759
  have htrace : WordTrace (prefixWord ++ tailWord_7810759) baseStart_7810759 baseEnd_7810759 := by
    simpa [prefixWord, tailWord_7810759, baseEnd_7810759] using wordTrace_append hprefix tailTrace_7810759
  have hstable : (prefixWord ++ tailWord_7810759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810759).length < 2 ^ (prefixWord ++ tailWord_7810759).sum := by decide
  have hdescent : baseEnd_7810759 < baseStart_7810759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810769 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 1, 6]
def baseStart_7810769 : Nat := 118140960795 + 7810769 * 2 ^ 59
def prefixEnd_7810769 : Nat := 4983230072969 + 3 ^ 40 * 7810769 * 2
def baseEnd_7810769 : Nat := 1336892926079285354688811

theorem tailTrace_7810769 : CollatzResearch.WordTrace tailWord_7810769 prefixEnd_7810769 1336892926079285354688811 := by
  unfold tailWord_7810769
  simp only [CollatzResearch.WordTrace]
  refine ⟨284882149439925360987283361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189921432959950240658188907 284882149439925360987283361)
  ·
    refine ⟨213661612079944020740462521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284882149439925360987283361 213661612079944020740462521)
    ·
      refine ⟨160246209059958015555346891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213661612079944020740462521 160246209059958015555346891)
      ·
        refine ⟨240369313589937023333020337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160246209059958015555346891 240369313589937023333020337)
        ·
          refine ⟨180276985192452767499765253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240369313589937023333020337 180276985192452767499765253)
          ·
            refine ⟨33801934723584893906205985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180276985192452767499765253 33801934723584893906205985)
            ·
              refine ⟨25351451042688670429654489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33801934723584893906205985 25351451042688670429654489)
              ·
                refine ⟨19013588282016502822240867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25351451042688670429654489 19013588282016502822240867)
                ·
                  refine ⟨28520382423024754233361301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19013588282016502822240867 28520382423024754233361301)
                  ·
                    refine ⟨1336892926079285354688811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28520382423024754233361301 1336892926079285354688811)
                    ·
                      rfl

theorem cell23_7810769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_7810769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810769 prefixEnd_7810769 := by exact prefixLift 7810769
  have htrace : WordTrace (prefixWord ++ tailWord_7810769) baseStart_7810769 baseEnd_7810769 := by
    simpa [prefixWord, tailWord_7810769, baseEnd_7810769] using wordTrace_append hprefix tailTrace_7810769
  have hstable : (prefixWord ++ tailWord_7810769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810769).length < 2 ^ (prefixWord ++ tailWord_7810769).sum := by decide
  have hdescent : baseEnd_7810769 < baseStart_7810769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810770 : List Nat := [3, 2, 2, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_7810770 : Nat := 118140960795 + 7810770 * 2 ^ 59
def prefixEnd_7810770 : Nat := 4983230072969 + 3 ^ 40 * 7810770 * 2
def baseEnd_7810770 : Nat := 4010679291718510560153929

theorem tailTrace_7810770 : CollatzResearch.WordTrace tailWord_7810770 prefixEnd_7810770 4010679291718510560153929 := by
  unfold tailWord_7810770
  simp only [CollatzResearch.WordTrace]
  refine ⟨71220546478230434539517441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189921457275281158772046509 71220546478230434539517441)
  ·
    refine ⟨53415409858672825904638081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71220546478230434539517441 53415409858672825904638081)
    ·
      refine ⟨40061557394004619428478561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53415409858672825904638081 40061557394004619428478561)
      ·
        refine ⟨30046168045503464571358921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40061557394004619428478561 30046168045503464571358921)
        ·
          refine ⟨22534626034127598428519191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30046168045503464571358921 22534626034127598428519191)
          ·
            refine ⟨33801939051191397642778787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22534626034127598428519191 33801939051191397642778787)
            ·
              refine ⟨50702908576787096464168181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33801939051191397642778787 50702908576787096464168181)
              ·
                refine ⟨4753397679073790293515767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50702908576787096464168181 4753397679073790293515767)
                ·
                  refine ⟨7130096518610685440273651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753397679073790293515767 7130096518610685440273651)
                  ·
                    refine ⟨10695144777916028160410477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7130096518610685440273651 10695144777916028160410477)
                    ·
                      refine ⟨4010679291718510560153929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10695144777916028160410477 4010679291718510560153929)
                      ·
                        rfl

theorem cell23_7810770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_7810770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810770 prefixEnd_7810770 := by exact prefixLift 7810770
  have htrace : WordTrace (prefixWord ++ tailWord_7810770) baseStart_7810770 baseEnd_7810770 := by
    simpa [prefixWord, tailWord_7810770, baseEnd_7810770] using wordTrace_append hprefix tailTrace_7810770
  have hstable : (prefixWord ++ tailWord_7810770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810770).length < 2 ^ (prefixWord ++ tailWord_7810770).sum := by decide
  have hdescent : baseEnd_7810770 < baseStart_7810770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810776 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 1, 1, 4]
def baseStart_7810776 : Nat := 118140960795 + 7810776 * 2 ^ 59
def prefixEnd_7810776 : Nat := 4983230072969 + 3 ^ 40 * 7810776 * 2
def baseEnd_7810776 : Nat := 4010682372602437536678901

theorem tailTrace_7810776 : CollatzResearch.WordTrace tailWord_7810776 prefixEnd_7810776 4010682372602437536678901 := by
  unfold tailWord_7810776
  simp only [CollatzResearch.WordTrace]
  refine ⟨142441202375450000591394091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189921603167266667455192121 142441202375450000591394091)
  ·
    refine ⟨213661803563175000887091137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142441202375450000591394091 213661803563175000887091137)
    ·
      refine ⟨160246352672381250665318353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213661803563175000887091137 160246352672381250665318353)
      ·
        refine ⟨120184764504285937998988765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160246352672381250665318353 120184764504285937998988765)
        ·
          refine ⟨45069286689107226749620787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120184764504285937998988765 45069286689107226749620787)
          ·
            refine ⟨67603930033660840124431181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45069286689107226749620787 67603930033660840124431181)
            ·
              refine ⟨25351473762622815046661693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67603930033660840124431181 25351473762622815046661693)
              ·
                refine ⟨9506802660983555642498135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25351473762622815046661693 9506802660983555642498135)
                ·
                  refine ⟨14260203991475333463747203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506802660983555642498135 14260203991475333463747203)
                  ·
                    refine ⟨21390305987213000195620805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14260203991475333463747203 21390305987213000195620805)
                    ·
                      refine ⟨4010682372602437536678901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21390305987213000195620805 4010682372602437536678901)
                      ·
                        rfl

theorem cell23_7810776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_7810776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810776 prefixEnd_7810776 := by exact prefixLift 7810776
  have htrace : WordTrace (prefixWord ++ tailWord_7810776) baseStart_7810776 baseEnd_7810776 := by
    simpa [prefixWord, tailWord_7810776, baseEnd_7810776] using wordTrace_append hprefix tailTrace_7810776
  have hstable : (prefixWord ++ tailWord_7810776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810776).length < 2 ^ (prefixWord ++ tailWord_7810776).sum := by decide
  have hdescent : baseEnd_7810776 < baseStart_7810776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810789 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_7810789 : Nat := 118140960795 + 7810789 * 2 ^ 59
def prefixEnd_7810789 : Nat := 4983230072969 + 3 ^ 40 * 7810789 * 2
def baseEnd_7810789 : Nat := 4010689047850945985816341

theorem tailTrace_7810789 : CollatzResearch.WordTrace tailWord_7810789 prefixEnd_7810789 4010689047850945985816341 := by
  unfold tailWord_7810789
  simp only [CollatzResearch.WordTrace]
  refine ⟨284882878899852904403011421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189921919266568602935340947 284882878899852904403011421)
  ·
    refine ⟨106831079587444839151129283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284882878899852904403011421 106831079587444839151129283)
    ·
      refine ⟨160246619381167258726693925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106831079587444839151129283 160246619381167258726693925)
      ·
        refine ⟨30046241133968861011255111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160246619381167258726693925 30046241133968861011255111)
        ·
          refine ⟨45069361700953291516882667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30046241133968861011255111 45069361700953291516882667)
          ·
            refine ⟨67604042551429937275324001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45069361700953291516882667 67604042551429937275324001)
            ·
              refine ⟨50703031913572452956493001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67604042551429937275324001 50703031913572452956493001)
              ·
                refine ⟨38027273935179339717369751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50703031913572452956493001 38027273935179339717369751)
                ·
                  refine ⟨57040910902769009576054627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38027273935179339717369751 57040910902769009576054627)
                  ·
                    refine ⟨85561366354153514364081941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57040910902769009576054627 85561366354153514364081941)
                    ·
                      refine ⟨4010689047850945985816341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85561366354153514364081941 4010689047850945985816341)
                      ·
                        rfl

theorem cell23_7810789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_7810789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810789 prefixEnd_7810789 := by exact prefixLift 7810789
  have htrace : WordTrace (prefixWord ++ tailWord_7810789) baseStart_7810789 baseEnd_7810789 := by
    simpa [prefixWord, tailWord_7810789, baseEnd_7810789] using wordTrace_append hprefix tailTrace_7810789
  have hstable : (prefixWord ++ tailWord_7810789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810789).length < 2 ^ (prefixWord ++ tailWord_7810789).sum := by decide
  have hdescent : baseEnd_7810789 < baseStart_7810789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810806 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_7810806 : Nat := 118140960795 + 7810806 * 2 ^ 59
def prefixEnd_7810806 : Nat := 4983230072969 + 3 ^ 40 * 7810806 * 2
def baseEnd_7810806 : Nat := 4010697777022072419303763

theorem tailTrace_7810806 : CollatzResearch.WordTrace tailWord_7810806 prefixEnd_7810806 4010697777022072419303763 := by
  unfold tailWord_7810806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17805218683799457269148767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189922332627194210870920181 17805218683799457269148767)
  ·
    refine ⟨26707828025699185903723151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17805218683799457269148767 26707828025699185903723151)
    ·
      refine ⟨40061742038548778855584727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26707828025699185903723151 40061742038548778855584727)
      ·
        refine ⟨60092613057823168283377091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40061742038548778855584727 60092613057823168283377091)
        ·
          refine ⟨90138919586734752425065637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60092613057823168283377091 90138919586734752425065637)
          ·
            refine ⟨16901047422512766079699807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90138919586734752425065637 16901047422512766079699807)
            ·
              refine ⟨25351571133769149119549711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16901047422512766079699807 25351571133769149119549711)
              ·
                refine ⟨38027356700653723679324567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25351571133769149119549711 38027356700653723679324567)
                ·
                  refine ⟨57041035050980585518986851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38027356700653723679324567 57041035050980585518986851)
                  ·
                    refine ⟨85561552576470878278480277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57041035050980585518986851 85561552576470878278480277)
                    ·
                      refine ⟨4010697777022072419303763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85561552576470878278480277 4010697777022072419303763)
                      ·
                        rfl

theorem cell23_7810806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_7810806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810806 prefixEnd_7810806 := by exact prefixLift 7810806
  have htrace : WordTrace (prefixWord ++ tailWord_7810806) baseStart_7810806 baseEnd_7810806 := by
    simpa [prefixWord, tailWord_7810806, baseEnd_7810806] using wordTrace_append hprefix tailTrace_7810806
  have hstable : (prefixWord ++ tailWord_7810806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810806).length < 2 ^ (prefixWord ++ tailWord_7810806).sum := by decide
  have hdescent : baseEnd_7810806 < baseStart_7810806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810860 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 3]
def baseStart_7810860 : Nat := 118140960795 + 7810860 * 2 ^ 59
def prefixEnd_7810860 : Nat := 4983230072969 + 3 ^ 40 * 7810860 * 2
def baseEnd_7810860 : Nat := 4010725504977415208028515

theorem tailTrace_7810860 : CollatzResearch.WordTrace tailWord_7810860 prefixEnd_7810860 4010725504977415208028515 := by
  unfold tailWord_7810860
  simp only [CollatzResearch.WordTrace]
  refine ⟨142442734241297841764423017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189923645655063789019230689 142442734241297841764423017)
  ·
    refine ⟨106832050680973381323317263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142442734241297841764423017 106832050680973381323317263)
    ·
      refine ⟨160248076021460071984975895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106832050680973381323317263 160248076021460071984975895)
      ·
        refine ⟨240372114032190107977463843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160248076021460071984975895 240372114032190107977463843)
        ·
          refine ⟨360558171048285161966195765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240372114032190107977463843 360558171048285161966195765)
          ·
            refine ⟨33802328535776733934330853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 360558171048285161966195765 33802328535776733934330853)
            ·
              refine ⟨6337936600458137612687035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33802328535776733934330853 6337936600458137612687035)
              ·
                refine ⟨9506904900687206419030553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337936600458137612687035 9506904900687206419030553)
                ·
                  refine ⟨7130178675515404814272915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9506904900687206419030553 7130178675515404814272915)
                  ·
                    refine ⟨10695268013273107221409373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7130178675515404814272915 10695268013273107221409373)
                    ·
                      refine ⟨4010725504977415208028515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10695268013273107221409373 4010725504977415208028515)
                      ·
                        rfl

theorem cell23_7810860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_7810860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810860 prefixEnd_7810860 := by exact prefixLift 7810860
  have htrace : WordTrace (prefixWord ++ tailWord_7810860) baseStart_7810860 baseEnd_7810860 := by
    simpa [prefixWord, tailWord_7810860, baseEnd_7810860] using wordTrace_append hprefix tailTrace_7810860
  have hstable : (prefixWord ++ tailWord_7810860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810860).length < 2 ^ (prefixWord ++ tailWord_7810860).sum := by decide
  have hdescent : baseEnd_7810860 < baseStart_7810860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810883 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 1, 4, 2]
def baseStart_7810883 : Nat := 118140960795 + 7810883 * 2 ^ 59
def prefixEnd_7810883 : Nat := 4983230072969 + 3 ^ 40 * 7810883 * 2
def baseEnd_7810883 : Nat := 4010737315032468618040909

theorem tailTrace_7810883 : CollatzResearch.WordTrace tailWord_7810883 prefixEnd_7810883 4010737315032468618040909 := by
  unfold tailWord_7810883
  simp only [CollatzResearch.WordTrace]
  refine ⟨284886307361512358456933303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189924204907674905637955535 284886307361512358456933303)
  ·
    refine ⟨427329461042268537685399955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284886307361512358456933303 427329461042268537685399955)
    ·
      refine ⟨640994191563402806528099933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427329461042268537685399955 640994191563402806528099933)
      ·
        refine ⟨240372821836276052448037475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640994191563402806528099933 240372821836276052448037475)
        ·
          refine ⟨360559232754414078672056213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240372821836276052448037475 360559232754414078672056213)
          ·
            refine ⟨16901214035363159937752635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 360559232754414078672056213 16901214035363159937752635)
            ·
              refine ⟨25351821053044739906628953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16901214035363159937752635 25351821053044739906628953)
              ·
                refine ⟨19013865789783554929971715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25351821053044739906628953 19013865789783554929971715)
                ·
                  refine ⟨28520798684675332394957573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19013865789783554929971715 28520798684675332394957573)
                  ·
                    refine ⟨5347649753376624824054545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28520798684675332394957573 5347649753376624824054545)
                    ·
                      refine ⟨4010737315032468618040909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5347649753376624824054545 4010737315032468618040909)
                      ·
                        rfl

theorem cell23_7810883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_7810883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810883 prefixEnd_7810883 := by exact prefixLift 7810883
  have htrace : WordTrace (prefixWord ++ tailWord_7810883) baseStart_7810883 baseEnd_7810883 := by
    simpa [prefixWord, tailWord_7810883, baseEnd_7810883] using wordTrace_append hprefix tailTrace_7810883
  have hstable : (prefixWord ++ tailWord_7810883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810883).length < 2 ^ (prefixWord ++ tailWord_7810883).sum := by decide
  have hdescent : baseEnd_7810883 < baseStart_7810883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810956 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_7810956 : Nat := 118140960795 + 7810956 * 2 ^ 59
def prefixEnd_7810956 : Nat := 4983230072969 + 3 ^ 40 * 7810956 * 2
def baseEnd_7810956 : Nat := 4010774799120246832428073

theorem tailTrace_7810956 : CollatzResearch.WordTrace tailWord_7810956 prefixEnd_7810956 4010774799120246832428073 := by
  unfold tailWord_7810956
  simp only [CollatzResearch.WordTrace]
  refine ⟨142444484945123945962170361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189925979926831927949560481 142444484945123945962170361)
  ·
    refine ⟨106833363708842959471627771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142444484945123945962170361 106833363708842959471627771)
    ·
      refine ⟨160250045563264439207441657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106833363708842959471627771 160250045563264439207441657)
      ·
        refine ⟨120187534172448329405581243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160250045563264439207441657 120187534172448329405581243)
        ·
          refine ⟨180281301258672494108371865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120187534172448329405581243 180281301258672494108371865)
          ·
            refine ⟨135210975944004370581278899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180281301258672494108371865 135210975944004370581278899)
            ·
              refine ⟨202816463916006555871918349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135210975944004370581278899 202816463916006555871918349)
              ·
                refine ⟨76056173968502458451969381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202816463916006555871918349 76056173968502458451969381)
                ·
                  refine ⟨14260532619094210959744259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76056173968502458451969381 14260532619094210959744259)
                  ·
                    refine ⟨21390798928641316439616389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14260532619094210959744259 21390798928641316439616389)
                    ·
                      refine ⟨4010774799120246832428073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21390798928641316439616389 4010774799120246832428073)
                      ·
                        rfl

theorem cell23_7810956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_7810956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810956 prefixEnd_7810956 := by exact prefixLift 7810956
  have htrace : WordTrace (prefixWord ++ tailWord_7810956) baseStart_7810956 baseEnd_7810956 := by
    simpa [prefixWord, tailWord_7810956, baseEnd_7810956] using wordTrace_append hprefix tailTrace_7810956
  have hstable : (prefixWord ++ tailWord_7810956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810956).length < 2 ^ (prefixWord ++ tailWord_7810956).sum := by decide
  have hdescent : baseEnd_7810956 < baseStart_7810956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7810993 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 1, 4, 3]
def baseStart_7810993 : Nat := 118140960795 + 7810993 * 2 ^ 59
def prefixEnd_7810993 : Nat := 4983230072969 + 3 ^ 40 * 7810993 * 2
def baseEnd_7810993 : Nat := 4010793797904463187665403

theorem tailTrace_7810993 : CollatzResearch.WordTrace tailWord_7810993 prefixEnd_7810993 4010793797904463187665403 := by
  unfold tailWord_7810993
  simp only [CollatzResearch.WordTrace]
  refine ⟨284890319391113847243437633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189926879594075898162291755 284890319391113847243437633)
  ·
    refine ⟨213667739543335385432578225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284890319391113847243437633 213667739543335385432578225)
    ·
      refine ⟨160250804657501539074433669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213667739543335385432578225 160250804657501539074433669)
      ·
        refine ⟨30047025873281538576456313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160250804657501539074433669 30047025873281538576456313)
        ·
          refine ⟨22535269404961153932342235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30047025873281538576456313 22535269404961153932342235)
          ·
            refine ⟨33802904107441730898513353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22535269404961153932342235 33802904107441730898513353)
            ·
              refine ⟨25352178080581298173885015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33802904107441730898513353 25352178080581298173885015)
              ·
                refine ⟨38028267120871947260827523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25352178080581298173885015 38028267120871947260827523)
                ·
                  refine ⟨57042400681307920891241285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38028267120871947260827523 57042400681307920891241285)
                  ·
                    refine ⟨10695450127745235167107741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57042400681307920891241285 10695450127745235167107741)
                    ·
                      refine ⟨4010793797904463187665403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10695450127745235167107741 4010793797904463187665403)
                      ·
                        rfl

theorem cell23_7810993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_7810993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7810993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7810993 prefixEnd_7810993 := by exact prefixLift 7810993
  have htrace : WordTrace (prefixWord ++ tailWord_7810993) baseStart_7810993 baseEnd_7810993 := by
    simpa [prefixWord, tailWord_7810993, baseEnd_7810993] using wordTrace_append hprefix tailTrace_7810993
  have hstable : (prefixWord ++ tailWord_7810993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7810993).length < 2 ^ (prefixWord ++ tailWord_7810993).sum := by decide
  have hdescent : baseEnd_7810993 < baseStart_7810993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7810993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811043 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 3, 5]
def baseStart_7811043 : Nat := 118140960795 + 7811043 * 2 ^ 59
def prefixEnd_7811043 : Nat := 4983230072969 + 3 ^ 40 * 7811043 * 2
def baseEnd_7811043 : Nat := 1336939823979062664013391

theorem tailTrace_7811043 : CollatzResearch.WordTrace tailWord_7811043 prefixEnd_7811043 1336939823979062664013391 := by
  unfold tailWord_7811043
  simp only [CollatzResearch.WordTrace]
  refine ⟨284892143040932705782757783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189928095360621803855171855 284892143040932705782757783)
  ·
    refine ⟨427338214561399058674136675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284892143040932705782757783 427338214561399058674136675)
    ·
      refine ⟨641007321842098588011205013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427338214561399058674136675 641007321842098588011205013)
      ·
        refine ⟨30047218211348371313025235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 641007321842098588011205013 30047218211348371313025235)
        ·
          refine ⟨45070827317022556969537853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30047218211348371313025235 45070827317022556969537853)
          ·
            refine ⟨16901560243883458863576695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45070827317022556969537853 16901560243883458863576695)
            ·
              refine ⟨25352340365825188295365043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16901560243883458863576695 25352340365825188295365043)
              ·
                refine ⟨38028510548737782443047565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25352340365825188295365043 38028510548737782443047565)
                ·
                  refine ⟨14260691455776668416142837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38028510548737782443047565 14260691455776668416142837)
                  ·
                    refine ⟨1336939823979062664013391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14260691455776668416142837 1336939823979062664013391)
                    ·
                      rfl

theorem cell23_7811043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 5].length) (baseStart_7811043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811043 prefixEnd_7811043 := by exact prefixLift 7811043
  have htrace : WordTrace (prefixWord ++ tailWord_7811043) baseStart_7811043 baseEnd_7811043 := by
    simpa [prefixWord, tailWord_7811043, baseEnd_7811043] using wordTrace_append hprefix tailTrace_7811043
  have hstable : (prefixWord ++ tailWord_7811043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811043).length < 2 ^ (prefixWord ++ tailWord_7811043).sum := by decide
  have hdescent : baseEnd_7811043 < baseStart_7811043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811056 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 3, 6]
def baseStart_7811056 : Nat := 118140960795 + 7811056 * 2 ^ 59
def prefixEnd_7811056 : Nat := 4983230072969 + 3 ^ 40 * 7811056 * 2
def baseEnd_7811056 : Nat := 1336942049061898813725871

theorem tailTrace_7811056 : CollatzResearch.WordTrace tailWord_7811056 prefixEnd_7811056 1336942049061898813725871 := by
  unfold tailWord_7811056
  simp only [CollatzResearch.WordTrace]
  refine ⟨142446308594942804501490511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189928411459923739335320681 142446308594942804501490511)
  ·
    refine ⟨213669462892414206752235767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142446308594942804501490511 213669462892414206752235767)
    ·
      refine ⟨320504194338621310128353651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213669462892414206752235767 320504194338621310128353651)
      ·
        refine ⟨480756291507931965192530477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320504194338621310128353651 480756291507931965192530477)
        ·
          refine ⟨180283609315474486947198929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480756291507931965192530477 180283609315474486947198929)
          ·
            refine ⟨135212706986605865210399197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180283609315474486947198929 135212706986605865210399197)
            ·
              refine ⟨50704765119977199453899699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135212706986605865210399197 50704765119977199453899699)
              ·
                refine ⟨76057147679965799180849549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50704765119977199453899699 76057147679965799180849549)
                ·
                  refine ⟨28521430379987174692818581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76057147679965799180849549 28521430379987174692818581)
                  ·
                    refine ⟨1336942049061898813725871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28521430379987174692818581 1336942049061898813725871)
                    ·
                      rfl

theorem cell23_7811056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_7811056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811056 prefixEnd_7811056 := by exact prefixLift 7811056
  have htrace : WordTrace (prefixWord ++ tailWord_7811056) baseStart_7811056 baseEnd_7811056 := by
    simpa [prefixWord, tailWord_7811056, baseEnd_7811056] using wordTrace_append hprefix tailTrace_7811056
  have hstable : (prefixWord ++ tailWord_7811056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811056).length < 2 ^ (prefixWord ++ tailWord_7811056).sum := by decide
  have hdescent : baseEnd_7811056 < baseStart_7811056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811083 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 3]
def baseStart_7811083 : Nat := 118140960795 + 7811083 * 2 ^ 59
def prefixEnd_7811083 : Nat := 4983230072969 + 3 ^ 40 * 7811083 * 2
def baseEnd_7811083 : Nat := 4010840011163367835539989

theorem tailTrace_7811083 : CollatzResearch.WordTrace tailWord_7811083 prefixEnd_7811083 4010840011163367835539989 := by
  unfold tailWord_7811083
  simp only [CollatzResearch.WordTrace]
  refine ⟨284893601960787792614213903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189929067973858528409475935 284893601960787792614213903)
  ·
    refine ⟨427340402941181688921320855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284893601960787792614213903 427340402941181688921320855)
    ·
      refine ⟨641010604411772533381981283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427340402941181688921320855 641010604411772533381981283)
      ·
        refine ⟨961515906617658800072971925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641010604411772533381981283 961515906617658800072971925)
        ·
          refine ⟨45071058122702756253420559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 961515906617658800072971925 45071058122702756253420559)
          ·
            refine ⟨67606587184054134380130839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45071058122702756253420559 67606587184054134380130839)
            ·
              refine ⟨101409880776081201570196259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67606587184054134380130839 101409880776081201570196259)
              ·
                refine ⟨152114821164121802355294389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101409880776081201570196259 152114821164121802355294389)
                ·
                  refine ⟨14260764484136418970808849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152114821164121802355294389 14260764484136418970808849)
                  ·
                    refine ⟨10695573363102314228106637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14260764484136418970808849 10695573363102314228106637)
                    ·
                      refine ⟨4010840011163367835539989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10695573363102314228106637 4010840011163367835539989)
                      ·
                        rfl

theorem cell23_7811083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 3].length) (baseStart_7811083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811083 prefixEnd_7811083 := by exact prefixLift 7811083
  have htrace : WordTrace (prefixWord ++ tailWord_7811083) baseStart_7811083 baseEnd_7811083 := by
    simpa [prefixWord, tailWord_7811083, baseEnd_7811083] using wordTrace_append hprefix tailTrace_7811083
  have hstable : (prefixWord ++ tailWord_7811083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811083).length < 2 ^ (prefixWord ++ tailWord_7811083).sum := by decide
  have hdescent : baseEnd_7811083 < baseStart_7811083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811100 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_7811100 : Nat := 118140960795 + 7811100 * 2 ^ 59
def prefixEnd_7811100 : Nat := 4983230072969 + 3 ^ 40 * 7811100 * 2
def baseEnd_7811100 : Nat := 4010848740334494269027411

theorem tailTrace_7811100 : CollatzResearch.WordTrace tailWord_7811100 prefixEnd_7811100 4010848740334494269027411 := by
  unfold tailWord_7811100
  simp only [CollatzResearch.WordTrace]
  refine ⟨142447111000863102258791377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189929481334484136345055169 142447111000863102258791377)
  ·
    refine ⟨106835333250647326694093533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142447111000863102258791377 106835333250647326694093533)
    ·
      refine ⟨40063249968992747510285075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106835333250647326694093533 40063249968992747510285075)
      ·
        refine ⟨60094874953489121265427613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40063249968992747510285075 60094874953489121265427613)
        ·
          refine ⟨22535578107558420474535355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60094874953489121265427613 22535578107558420474535355)
          ·
            refine ⟨33803367161337630711803033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22535578107558420474535355 33803367161337630711803033)
            ·
              refine ⟨25352525371003223033852275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33803367161337630711803033 25352525371003223033852275)
              ·
                refine ⟨38028788056504834550778413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25352525371003223033852275 38028788056504834550778413)
                ·
                  refine ⟨14260795521189312956541905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38028788056504834550778413 14260795521189312956541905)
                  ·
                    refine ⟨10695596640891984717406429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14260795521189312956541905 10695596640891984717406429)
                    ·
                      refine ⟨4010848740334494269027411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10695596640891984717406429 4010848740334494269027411)
                      ·
                        rfl

theorem cell23_7811100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_7811100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811100 prefixEnd_7811100 := by exact prefixLift 7811100
  have htrace : WordTrace (prefixWord ++ tailWord_7811100) baseStart_7811100 baseEnd_7811100 := by
    simpa [prefixWord, tailWord_7811100, baseEnd_7811100] using wordTrace_append hprefix tailTrace_7811100
  have hstable : (prefixWord ++ tailWord_7811100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811100).length < 2 ^ (prefixWord ++ tailWord_7811100).sum := by decide
  have hdescent : baseEnd_7811100 < baseStart_7811100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811103 : List Nat := [1, 1, 2, 4, 1, 2, 5, 7]
def baseStart_7811103 : Nat := 118140960795 + 7811103 * 2 ^ 59
def prefixEnd_7811103 : Nat := 4983230072969 + 3 ^ 40 * 7811103 * 2
def baseEnd_7811103 : Nat := 148550010399128065084811

theorem tailTrace_7811103 : CollatzResearch.WordTrace tailWord_7811103 prefixEnd_7811103 148550010399128065084811 := by
  unfold tailWord_7811103
  simp only [CollatzResearch.WordTrace]
  refine ⟨284894331420715336029941963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189929554280476890686627975 284894331420715336029941963)
  ·
    refine ⟨427341497131073004044912945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284894331420715336029941963 427341497131073004044912945)
    ·
      refine ⟨320506122848304753033684709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427341497131073004044912945 320506122848304753033684709)
      ·
        refine ⟨60094898034057141193815883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320506122848304753033684709 60094898034057141193815883)
        ·
          refine ⟨90142347051085711790723825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60094898034057141193815883 90142347051085711790723825)
          ·
            refine ⟨67606760288314283843042869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90142347051085711790723825 67606760288314283843042869)
            ·
              refine ⟨6338133777029464110285269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67606760288314283843042869 6338133777029464110285269)
              ·
                refine ⟨148550010399128065084811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6338133777029464110285269 148550010399128065084811)
                ·
                  rfl

theorem cell23_7811103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 7].length) (baseStart_7811103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811103 prefixEnd_7811103 := by exact prefixLift 7811103
  have htrace : WordTrace (prefixWord ++ tailWord_7811103) baseStart_7811103 baseEnd_7811103 := by
    simpa [prefixWord, tailWord_7811103, baseEnd_7811103] using wordTrace_append hprefix tailTrace_7811103
  have hstable : (prefixWord ++ tailWord_7811103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811103).length < 2 ^ (prefixWord ++ tailWord_7811103).sum := by decide
  have hdescent : baseEnd_7811103 < baseStart_7811103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811111 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 1, 5]
def baseStart_7811111 : Nat := 118140960795 + 7811111 * 2 ^ 59
def prefixEnd_7811111 : Nat := 4983230072969 + 3 ^ 40 * 7811111 * 2
def baseEnd_7811111 : Nat := 1336951462873897908663287

theorem tailTrace_7811111 : CollatzResearch.WordTrace tailWord_7811111 prefixEnd_7811111 1336951462873897908663287 := by
  unfold tailWord_7811111
  simp only [CollatzResearch.WordTrace]
  refine ⟨284894623204686353396233187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189929748803124235597488791 284894623204686353396233187)
  ·
    refine ⟨427341934807029530094349781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284894623204686353396233187 427341934807029530094349781)
    ·
      refine ⟨10015826597039754611586323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 427341934807029530094349781 10015826597039754611586323)
      ·
        refine ⟨15023739895559631917379485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10015826597039754611586323 15023739895559631917379485)
        ·
          refine ⟨5633902460834861969017307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15023739895559631917379485 5633902460834861969017307)
          ·
            refine ⟨8450853691252292953525961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633902460834861969017307 8450853691252292953525961)
            ·
              refine ⟨6338140268439219715144471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8450853691252292953525961 6338140268439219715144471)
              ·
                refine ⟨9507210402658829572716707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6338140268439219715144471 9507210402658829572716707)
                ·
                  refine ⟨14260815603988244359075061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9507210402658829572716707 14260815603988244359075061)
                  ·
                    refine ⟨1336951462873897908663287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14260815603988244359075061 1336951462873897908663287)
                    ·
                      rfl

theorem cell23_7811111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_7811111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811111 prefixEnd_7811111 := by exact prefixLift 7811111
  have htrace : WordTrace (prefixWord ++ tailWord_7811111) baseStart_7811111 baseEnd_7811111 := by
    simpa [prefixWord, tailWord_7811111, baseEnd_7811111] using wordTrace_append hprefix tailTrace_7811111
  have hstable : (prefixWord ++ tailWord_7811111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811111).length < 2 ^ (prefixWord ++ tailWord_7811111).sum := by decide
  have hdescent : baseEnd_7811111 < baseStart_7811111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811114 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_7811114 : Nat := 118140960795 + 7811114 * 2 ^ 59
def prefixEnd_7811114 : Nat := 4983230072969 + 3 ^ 40 * 7811114 * 2
def baseEnd_7811114 : Nat := 4010855929063657214252347

theorem tailTrace_7811114 : CollatzResearch.WordTrace tailWord_7811114 prefixEnd_7811114 4010855929063657214252347 := by
  unfold tailWord_7811114
  simp only [CollatzResearch.WordTrace]
  refine ⟨71223683155918871227148099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189929821749116989939061597 71223683155918871227148099)
  ·
    refine ⟨106835524733878306840722149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71223683155918871227148099 106835524733878306840722149)
    ·
      refine ⟨20031660887602182532635403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106835524733878306840722149 20031660887602182532635403)
      ·
        refine ⟨30047491331403273798953105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20031660887602182532635403 30047491331403273798953105)
        ·
          refine ⟨22535618498552455349214829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30047491331403273798953105 22535618498552455349214829)
          ·
            refine ⟨8450856936957170755955561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22535618498552455349214829 8450856936957170755955561)
            ·
              refine ⟨6338142702717878066966671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8450856936957170755955561 6338142702717878066966671)
              ·
                refine ⟨9507214054076817100450007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6338142702717878066966671 9507214054076817100450007)
                ·
                  refine ⟨14260821081115225650675011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9507214054076817100450007 14260821081115225650675011)
                  ·
                    refine ⟨21391231621672838476012517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14260821081115225650675011 21391231621672838476012517)
                    ·
                      refine ⟨4010855929063657214252347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21391231621672838476012517 4010855929063657214252347)
                      ·
                        rfl

theorem cell23_7811114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_7811114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811114 prefixEnd_7811114 := by exact prefixLift 7811114
  have htrace : WordTrace (prefixWord ++ tailWord_7811114) baseStart_7811114 baseEnd_7811114 := by
    simpa [prefixWord, tailWord_7811114, baseEnd_7811114] using wordTrace_append hprefix tailTrace_7811114
  have hstable : (prefixWord ++ tailWord_7811114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811114).length < 2 ^ (prefixWord ++ tailWord_7811114).sum := by decide
  have hdescent : baseEnd_7811114 < baseStart_7811114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811116 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_7811116 : Nat := 118140960795 + 7811116 * 2 ^ 59
def prefixEnd_7811116 : Nat := 4983230072969 + 3 ^ 40 * 7811116 * 2
def baseEnd_7811116 : Nat := 1336952318674988735475779

theorem tailTrace_7811116 : CollatzResearch.WordTrace tailWord_7811116 prefixEnd_7811116 1336952318674988735475779 := by
  unfold tailWord_7811116
  simp only [CollatzResearch.WordTrace]
  refine ⟨142447402784834119625082601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189929870379778826166776801 142447402784834119625082601)
  ·
    refine ⟨106835552088625589718811951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142447402784834119625082601 106835552088625589718811951)
    ·
      refine ⟨160253328132938384578217927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106835552088625589718811951 160253328132938384578217927)
      ·
        refine ⟨240379992199407576867326891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160253328132938384578217927 240379992199407576867326891)
        ·
          refine ⟨360569988299111365300990337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240379992199407576867326891 360569988299111365300990337)
          ·
            refine ⟨270427491224333523975742753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360569988299111365300990337 270427491224333523975742753)
            ·
              refine ⟨202820618418250142981807065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270427491224333523975742753 202820618418250142981807065)
              ·
                refine ⟨152115463813687607236355299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202820618418250142981807065 152115463813687607236355299)
                ·
                  refine ⟨228173195720531410854532949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152115463813687607236355299 228173195720531410854532949)
                  ·
                    refine ⟨1336952318674988735475779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 228173195720531410854532949 1336952318674988735475779)
                    ·
                      rfl

theorem cell23_7811116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_7811116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811116 prefixEnd_7811116 := by exact prefixLift 7811116
  have htrace : WordTrace (prefixWord ++ tailWord_7811116) baseStart_7811116 baseEnd_7811116 := by
    simpa [prefixWord, tailWord_7811116, baseEnd_7811116] using wordTrace_append hprefix tailTrace_7811116
  have hstable : (prefixWord ++ tailWord_7811116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811116).length < 2 ^ (prefixWord ++ tailWord_7811116).sum := by decide
  have hdescent : baseEnd_7811116 < baseStart_7811116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811157 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 1, 3, 2]
def baseStart_7811157 : Nat := 118140960795 + 7811157 * 2 ^ 59
def prefixEnd_7811157 : Nat := 4983230072969 + 3 ^ 40 * 7811157 * 2
def baseEnd_7811157 : Nat := 4010878008731800546014649

theorem tailTrace_7811157 : CollatzResearch.WordTrace tailWord_7811157 prefixEnd_7811157 4010878008731800546014649 := by
  unfold tailWord_7811157
  simp only [CollatzResearch.WordTrace]
  refine ⟨284896300962519703252407725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189930867308346468834938483 284896300962519703252407725)
  ·
    refine ⟨106836112860944888719652897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284896300962519703252407725 106836112860944888719652897)
    ·
      refine ⟨80127084645708666539739673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106836112860944888719652897 80127084645708666539739673)
      ·
        refine ⟨60095313484281499904804755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80127084645708666539739673 60095313484281499904804755)
        ·
          refine ⟨90142970226422249857207133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60095313484281499904804755 90142970226422249857207133)
          ·
            refine ⟨33803613834908343696452675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90142970226422249857207133 33803613834908343696452675)
            ·
              refine ⟨50705420752362515544679013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33803613834908343696452675 50705420752362515544679013)
              ·
                refine ⟨9507266391067971664627315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50705420752362515544679013 9507266391067971664627315)
                ·
                  refine ⟨14260899586601957496940973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9507266391067971664627315 14260899586601957496940973)
                  ·
                    refine ⟨5347837344975734061352865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14260899586601957496940973 5347837344975734061352865)
                    ·
                      refine ⟨4010878008731800546014649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5347837344975734061352865 4010878008731800546014649)
                      ·
                        rfl

theorem cell23_7811157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_7811157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811157 prefixEnd_7811157 := by exact prefixLift 7811157
  have htrace : WordTrace (prefixWord ++ tailWord_7811157) baseStart_7811157 baseEnd_7811157 := by
    simpa [prefixWord, tailWord_7811157, baseEnd_7811157] using wordTrace_append hprefix tailTrace_7811157
  have hstable : (prefixWord ++ tailWord_7811157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811157).length < 2 ^ (prefixWord ++ tailWord_7811157).sum := by decide
  have hdescent : baseEnd_7811157 < baseStart_7811157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811173 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_7811173 : Nat := 118140960795 + 7811173 * 2 ^ 59
def prefixEnd_7811173 : Nat := 4983230072969 + 3 ^ 40 * 7811173 * 2
def baseEnd_7811173 : Nat := 4010886224422272483414575

theorem tailTrace_7811173 : CollatzResearch.WordTrace tailWord_7811173 prefixEnd_7811173 4010886224422272483414575 := by
  unfold tailWord_7811173
  simp only [CollatzResearch.WordTrace]
  refine ⟨284896884530461737984990173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189931256353641158656660115 284896884530461737984990173)
  ·
    refine ⟨106836331698923151744371315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284896884530461737984990173 106836331698923151744371315)
    ·
      refine ⟨160254497548384727616556973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106836331698923151744371315 160254497548384727616556973)
      ·
        refine ⟨60095436580644272856208865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160254497548384727616556973 60095436580644272856208865)
        ·
          refine ⟨45071577435483204642156649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60095436580644272856208865 45071577435483204642156649)
          ·
            refine ⟨33803683076612403481617487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45071577435483204642156649 33803683076612403481617487)
            ·
              refine ⟨50705524614918605222426231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33803683076612403481617487 50705524614918605222426231)
              ·
                refine ⟨76058286922377907833639347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50705524614918605222426231 76058286922377907833639347)
                ·
                  refine ⟨114087430383566861750459021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76058286922377907833639347 114087430383566861750459021)
                  ·
                    refine ⟨42782786393837573156422133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114087430383566861750459021 42782786393837573156422133)
                    ·
                      refine ⟨4010886224422272483414575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42782786393837573156422133 4010886224422272483414575)
                      ·
                        rfl

theorem cell23_7811173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_7811173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811173 prefixEnd_7811173 := by exact prefixLift 7811173
  have htrace : WordTrace (prefixWord ++ tailWord_7811173) baseStart_7811173 baseEnd_7811173 := by
    simpa [prefixWord, tailWord_7811173, baseEnd_7811173] using wordTrace_append hprefix tailTrace_7811173
  have hstable : (prefixWord ++ tailWord_7811173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811173).length < 2 ^ (prefixWord ++ tailWord_7811173).sum := by decide
  have hdescent : baseEnd_7811173 < baseStart_7811173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811204 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_7811204 : Nat := 118140960795 + 7811204 * 2 ^ 59
def prefixEnd_7811204 : Nat := 4983230072969 + 3 ^ 40 * 7811204 * 2
def baseEnd_7811204 : Nat := 4010902142322561862126933

theorem tailTrace_7811204 : CollatzResearch.WordTrace tailWord_7811204 prefixEnd_7811204 4010902142322561862126933 := by
  unfold tailWord_7811204
  simp only [CollatzResearch.WordTrace]
  refine ⟨142449007596674715139684333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189932010128899620186245777 142449007596674715139684333)
  ·
    refine ⟨53418377848753018177381625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142449007596674715139684333 53418377848753018177381625)
    ·
      refine ⟨40063783386564763633036219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53418377848753018177381625 40063783386564763633036219)
      ·
        refine ⟨60095675079847145449554329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40063783386564763633036219 60095675079847145449554329)
        ·
          refine ⟨45071756309885359087165747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60095675079847145449554329 45071756309885359087165747)
          ·
            refine ⟨67607634464828038630748621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45071756309885359087165747 67607634464828038630748621)
            ·
              refine ⟨25352862924310514486530733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67607634464828038630748621 25352862924310514486530733)
              ·
                refine ⟨9507323596616442932449025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25352862924310514486530733 9507323596616442932449025)
                ·
                  refine ⟨7130492697462332199336769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9507323596616442932449025 7130492697462332199336769)
                  ·
                    refine ⟨5347869523096749149502577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7130492697462332199336769 5347869523096749149502577)
                    ·
                      refine ⟨4010902142322561862126933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5347869523096749149502577 4010902142322561862126933)
                      ·
                        rfl

theorem cell23_7811204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_7811204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811204 prefixEnd_7811204 := by exact prefixLift 7811204
  have htrace : WordTrace (prefixWord ++ tailWord_7811204) baseStart_7811204 baseEnd_7811204 := by
    simpa [prefixWord, tailWord_7811204, baseEnd_7811204] using wordTrace_append hprefix tailTrace_7811204
  have hstable : (prefixWord ++ tailWord_7811204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811204).length < 2 ^ (prefixWord ++ tailWord_7811204).sum := by decide
  have hdescent : baseEnd_7811204 < baseStart_7811204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811273 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_7811273 : Nat := 118140960795 + 7811273 * 2 ^ 59
def prefixEnd_7811273 : Nat := 4983230072969 + 3 ^ 40 * 7811273 * 2
def baseEnd_7811273 : Nat := 4010937572487722092164115

theorem tailTrace_7811273 : CollatzResearch.WordTrace tailWord_7811273 prefixEnd_7811273 4010937572487722092164115 := by
  unfold tailWord_7811273
  simp only [CollatzResearch.WordTrace]
  refine ⟨284900531830099455063630473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189933687886732970042420315 284900531830099455063630473)
  ·
    refine ⟨213675398872574591297722855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284900531830099455063630473 213675398872574591297722855)
    ·
      refine ⟨320513098308861886946584283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213675398872574591297722855 320513098308861886946584283)
      ·
        refine ⟨480769647463292830419876425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320513098308861886946584283 480769647463292830419876425)
        ·
          refine ⟨360577235597469622814907319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480769647463292830419876425 360577235597469622814907319)
          ·
            refine ⟨540865853396204434222360979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360577235597469622814907319 540865853396204434222360979)
            ·
              refine ⟨811298780094306651333541469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540865853396204434222360979 811298780094306651333541469)
              ·
                refine ⟨304237042535364994250078051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 811298780094306651333541469 304237042535364994250078051)
                ·
                  refine ⟨456355563803047491375117077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304237042535364994250078051 456355563803047491375117077)
                  ·
                    refine ⟨21391667053267851158208613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 456355563803047491375117077 21391667053267851158208613)
                    ·
                      refine ⟨4010937572487722092164115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21391667053267851158208613 4010937572487722092164115)
                      ·
                        rfl

theorem cell23_7811273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_7811273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811273 prefixEnd_7811273 := by exact prefixLift 7811273
  have htrace : WordTrace (prefixWord ++ tailWord_7811273) baseStart_7811273 baseEnd_7811273 := by
    simpa [prefixWord, tailWord_7811273, baseEnd_7811273] using wordTrace_append hprefix tailTrace_7811273
  have hstable : (prefixWord ++ tailWord_7811273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811273).length < 2 ^ (prefixWord ++ tailWord_7811273).sum := by decide
  have hdescent : baseEnd_7811273 < baseStart_7811273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811304 : List Nat := [2, 1, 4, 1, 2, 2, 2, 4, 1, 4]
def baseStart_7811304 : Nat := 118140960795 + 7811304 * 2 ^ 59
def prefixEnd_7811304 : Nat := 4983230072969 + 3 ^ 40 * 7811304 * 2
def baseEnd_7811304 : Nat := 1336984496796003823625491

theorem tailTrace_7811304 : CollatzResearch.WordTrace tailWord_7811304 prefixEnd_7811304 1336984496796003823625491 := by
  unfold tailWord_7811304
  simp only [CollatzResearch.WordTrace]
  refine ⟨142450831246493573679004483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189934441661991431572005977 142450831246493573679004483)
  ·
    refine ⟨213676246869740360518506725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142450831246493573679004483 213676246869740360518506725)
    ·
      refine ⟨40064296288076317597220011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213676246869740360518506725 40064296288076317597220011)
      ·
        refine ⟨60096444432114476395830017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40064296288076317597220011 60096444432114476395830017)
        ·
          refine ⟨45072333324085857296872513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60096444432114476395830017 45072333324085857296872513)
          ·
            refine ⟨33804249993064392972654385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45072333324085857296872513 33804249993064392972654385)
            ·
              refine ⟨25353187494798294729490789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33804249993064392972654385 25353187494798294729490789)
              ·
                refine ⟨4753722655274680261779523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25353187494798294729490789 4753722655274680261779523)
                ·
                  refine ⟨7130583982912020392669285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753722655274680261779523 7130583982912020392669285)
                  ·
                    refine ⟨1336984496796003823625491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7130583982912020392669285 1336984496796003823625491)
                    ·
                      rfl

theorem cell23_7811304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_7811304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811304 prefixEnd_7811304 := by exact prefixLift 7811304
  have htrace : WordTrace (prefixWord ++ tailWord_7811304) baseStart_7811304 baseEnd_7811304 := by
    simpa [prefixWord, tailWord_7811304, baseEnd_7811304] using wordTrace_append hprefix tailTrace_7811304
  have hstable : (prefixWord ++ tailWord_7811304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811304).length < 2 ^ (prefixWord ++ tailWord_7811304).sum := by decide
  have hdescent : baseEnd_7811304 < baseStart_7811304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811327 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 3, 1, 3]
def baseStart_7811327 : Nat := 118140960795 + 7811327 * 2 ^ 59
def prefixEnd_7811327 : Nat := 4983230072969 + 3 ^ 40 * 7811327 * 2
def baseEnd_7811327 : Nat := 4010965300443064880888867

theorem tailTrace_7811327 : CollatzResearch.WordTrace tailWord_7811327 prefixEnd_7811327 4010965300443064880888867 := by
  unfold tailWord_7811327
  simp only [CollatzResearch.WordTrace]
  refine ⟨284902501371903822286096235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189935000914602548190730823 284902501371903822286096235)
  ·
    refine ⟨427353752057855733429144353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284902501371903822286096235 427353752057855733429144353)
    ·
      refine ⟨320515314043391800071858265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427353752057855733429144353 320515314043391800071858265)
      ·
        refine ⟨240386485532543850053893699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320515314043391800071858265 240386485532543850053893699)
        ·
          refine ⟨360579728298815775080840549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240386485532543850053893699 360579728298815775080840549)
          ·
            refine ⟨67608699056027957827657603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360579728298815775080840549 67608699056027957827657603)
            ·
              refine ⟨101413048584041936741486405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67608699056027957827657603 101413048584041936741486405)
              ·
                refine ⟨19014946609507863139028701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101413048584041936741486405 19014946609507863139028701)
                ·
                  refine ⟨7130604978565448677135763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19014946609507863139028701 7130604978565448677135763)
                  ·
                    refine ⟨10695907467848173015703645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7130604978565448677135763 10695907467848173015703645)
                    ·
                      refine ⟨4010965300443064880888867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10695907467848173015703645 4010965300443064880888867)
                      ·
                        rfl

theorem cell23_7811327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_7811327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811327 prefixEnd_7811327 := by exact prefixLift 7811327
  have htrace : WordTrace (prefixWord ++ tailWord_7811327) baseStart_7811327 baseEnd_7811327 := by
    simpa [prefixWord, tailWord_7811327, baseEnd_7811327] using wordTrace_append hprefix tailTrace_7811327
  have hstable : (prefixWord ++ tailWord_7811327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811327).length < 2 ^ (prefixWord ++ tailWord_7811327).sum := by decide
  have hdescent : baseEnd_7811327 < baseStart_7811327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811337 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 1, 5, 2]
def baseStart_7811337 : Nat := 118140960795 + 7811337 * 2 ^ 59
def prefixEnd_7811337 : Nat := 4983230072969 + 3 ^ 40 * 7811337 * 2
def baseEnd_7811337 : Nat := 4010970435249609841763821

theorem tailTrace_7811337 : CollatzResearch.WordTrace tailWord_7811337 prefixEnd_7811337 4010970435249609841763821 := by
  unfold tailWord_7811337
  simp only [CollatzResearch.WordTrace]
  refine ⟨284902866101867593993960265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189935244067911729329306843 284902866101867593993960265)
  ·
    refine ⟨213677149576400695495470199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284902866101867593993960265 213677149576400695495470199)
    ·
      refine ⟨320515724364601043243205299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213677149576400695495470199 320515724364601043243205299)
      ·
        refine ⟨480773586546901564864807949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320515724364601043243205299 480773586546901564864807949)
        ·
          refine ⟨180290094955088086824302981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480773586546901564864807949 180290094955088086824302981)
          ·
            refine ⟨33804392804079016279556809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180290094955088086824302981 33804392804079016279556809)
            ·
              refine ⟨25353294603059262209667607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33804392804079016279556809 25353294603059262209667607)
              ·
                refine ⟨38029941904588893314501411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25353294603059262209667607 38029941904588893314501411)
                ·
                  refine ⟨57044912856883339971752117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38029941904588893314501411 57044912856883339971752117)
                  ·
                    refine ⟨5347960580332813122351761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57044912856883339971752117 5347960580332813122351761)
                    ·
                      refine ⟨4010970435249609841763821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5347960580332813122351761 4010970435249609841763821)
                      ·
                        rfl

theorem cell23_7811337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 5, 2].length) (baseStart_7811337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811337 prefixEnd_7811337 := by exact prefixLift 7811337
  have htrace : WordTrace (prefixWord ++ tailWord_7811337) baseStart_7811337 baseEnd_7811337 := by
    simpa [prefixWord, tailWord_7811337, baseEnd_7811337] using wordTrace_append hprefix tailTrace_7811337
  have hstable : (prefixWord ++ tailWord_7811337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811337).length < 2 ^ (prefixWord ++ tailWord_7811337).sum := by decide
  have hdescent : baseEnd_7811337 < baseStart_7811337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811384 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 3, 2, 2]
def baseStart_7811384 : Nat := 118140960795 + 7811384 * 2 ^ 59
def prefixEnd_7811384 : Nat := 4983230072969 + 3 ^ 40 * 7811384 * 2
def baseEnd_7811384 : Nat := 4010994568840371157876105

theorem tailTrace_7811384 : CollatzResearch.WordTrace tailWord_7811384 prefixEnd_7811384 4010994568840371157876105 := by
  unfold tailWord_7811384
  simp only [CollatzResearch.WordTrace]
  refine ⟨142452290166348660510460603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189936386888464880680614137 142452290166348660510460603)
  ·
    refine ⟨213678435249522990765690905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142452290166348660510460603 213678435249522990765690905)
    ·
      refine ⟨160258826437142243074268179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213678435249522990765690905 160258826437142243074268179)
      ·
        refine ⟨240388239655713364611402269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160258826437142243074268179 240388239655713364611402269)
        ·
          refine ⟨90145589870892511729275851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240388239655713364611402269 90145589870892511729275851)
          ·
            refine ⟨135218384806338767593913777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90145589870892511729275851 135218384806338767593913777)
            ·
              refine ⟨101413788604754075695435333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135218384806338767593913777 101413788604754075695435333)
              ·
                refine ⟨19015085363391389192894125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101413788604754075695435333 19015085363391389192894125)
                ·
                  refine ⟨7130657011271770947335297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19015085363391389192894125 7130657011271770947335297)
                  ·
                    refine ⟨5347992758453828210501473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7130657011271770947335297 5347992758453828210501473)
                    ·
                      refine ⟨4010994568840371157876105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5347992758453828210501473 4010994568840371157876105)
                      ·
                        rfl

theorem cell23_7811384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_7811384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811384 prefixEnd_7811384 := by exact prefixLift 7811384
  have htrace : WordTrace (prefixWord ++ tailWord_7811384) baseStart_7811384 baseEnd_7811384 := by
    simpa [prefixWord, tailWord_7811384, baseEnd_7811384] using wordTrace_append hprefix tailTrace_7811384
  have hstable : (prefixWord ++ tailWord_7811384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811384).length < 2 ^ (prefixWord ++ tailWord_7811384).sum := by decide
  have hdescent : baseEnd_7811384 < baseStart_7811384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811401 : List Nat := [1, 2, 1, 1, 2, 3, 1, 7, 1, 2, 2]
def baseStart_7811401 : Nat := 118140960795 + 7811401 * 2 ^ 59
def prefixEnd_7811401 : Nat := 4983230072969 + 3 ^ 40 * 7811401 * 2
def baseEnd_7811401 : Nat := 4011003298011497591363527

theorem tailTrace_7811401 : CollatzResearch.WordTrace tailWord_7811401 prefixEnd_7811401 4011003298011497591363527 := by
  unfold tailWord_7811401
  simp only [CollatzResearch.WordTrace]
  refine ⟨284905200373635732924290057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189936800249090488616193371 284905200373635732924290057)
  ·
    refine ⟨213678900280226799693217543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284905200373635732924290057 213678900280226799693217543)
    ·
      refine ⟨320518350420340199539826315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213678900280226799693217543 320518350420340199539826315)
      ·
        refine ⟨480777525630510299309739473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320518350420340199539826315 480777525630510299309739473)
        ·
          refine ⟨360583144222882724482304605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480777525630510299309739473 360583144222882724482304605)
          ·
            refine ⟨135218679083581021680864227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360583144222882724482304605 135218679083581021680864227)
            ·
              refine ⟨202828018625371532521296341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135218679083581021680864227 202828018625371532521296341)
              ·
                refine ⟨4753781686532145293467883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 202828018625371532521296341 4753781686532145293467883)
                ·
                  refine ⟨7130672529798217940201825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753781686532145293467883 7130672529798217940201825)
                  ·
                    refine ⟨5348004397348663455151369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7130672529798217940201825 5348004397348663455151369)
                    ·
                      refine ⟨4011003298011497591363527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348004397348663455151369 4011003298011497591363527)
                      ·
                        rfl

theorem cell23_7811401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 1, 2, 2].length) (baseStart_7811401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811401 prefixEnd_7811401 := by exact prefixLift 7811401
  have htrace : WordTrace (prefixWord ++ tailWord_7811401) baseStart_7811401 baseEnd_7811401 := by
    simpa [prefixWord, tailWord_7811401, baseEnd_7811401] using wordTrace_append hprefix tailTrace_7811401
  have hstable : (prefixWord ++ tailWord_7811401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811401).length < 2 ^ (prefixWord ++ tailWord_7811401).sum := by decide
  have hdescent : baseEnd_7811401 < baseStart_7811401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811424 : List Nat := [2, 1, 1, 3, 6, 1, 1, 8]
def baseStart_7811424 : Nat := 118140960795 + 7811424 * 2 ^ 59
def prefixEnd_7811424 : Nat := 4983230072969 + 3 ^ 40 * 7811424 * 2
def baseEnd_7811424 : Nat := 148556115113575963013923

theorem tailTrace_7811424 : CollatzResearch.WordTrace tailWord_7811424 prefixEnd_7811424 148556115113575963013923 := by
  unfold tailWord_7811424
  simp only [CollatzResearch.WordTrace]
  refine ⟨142453019626276203926188663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189937359501701605234918217 142453019626276203926188663)
  ·
    refine ⟨213679529439414305889282995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142453019626276203926188663 213679529439414305889282995)
    ·
      refine ⟨320519294159121458833924493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213679529439414305889282995 320519294159121458833924493)
      ·
        refine ⟨120194735309670547062721685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320519294159121458833924493 120194735309670547062721685)
        ·
          refine ⟨5634128217640806893565079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120194735309670547062721685 5634128217640806893565079)
          ·
            refine ⟨8451192326461210340347619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634128217640806893565079 8451192326461210340347619)
            ·
              refine ⟨12676788489691815510521429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8451192326461210340347619 12676788489691815510521429)
              ·
                refine ⟨148556115113575963013923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12676788489691815510521429 148556115113575963013923)
                ·
                  rfl

theorem cell23_7811424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 8].length) (baseStart_7811424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811424 prefixEnd_7811424 := by exact prefixLift 7811424
  have htrace : WordTrace (prefixWord ++ tailWord_7811424) baseStart_7811424 baseEnd_7811424 := by
    simpa [prefixWord, tailWord_7811424, baseEnd_7811424] using wordTrace_append hprefix tailTrace_7811424
  have hstable : (prefixWord ++ tailWord_7811424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811424).length < 2 ^ (prefixWord ++ tailWord_7811424).sum := by decide
  have hdescent : baseEnd_7811424 < baseStart_7811424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811434 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_7811434 : Nat := 118140960795 + 7811434 * 2 ^ 59
def prefixEnd_7811434 : Nat := 4983230072969 + 3 ^ 40 * 7811434 * 2
def baseEnd_7811434 : Nat := 4011020242873095962250875

theorem tailTrace_7811434 : CollatzResearch.WordTrace tailWord_7811434 prefixEnd_7811434 4011020242873095962250875 := by
  unfold tailWord_7811434
  simp only [CollatzResearch.WordTrace]
  refine ⟨71226600995629044890060339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189937602655010786373494237 71226600995629044890060339)
  ·
    refine ⟨106839901493443567335090509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71226600995629044890060339 106839901493443567335090509)
    ·
      refine ⟨40064963060041337750658941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106839901493443567335090509 40064963060041337750658941)
      ·
        refine ⟨15024361147515501656497103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40064963060041337750658941 15024361147515501656497103)
        ·
          refine ⟨22536541721273252484745655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15024361147515501656497103 22536541721273252484745655)
          ·
            refine ⟨33804812581909878727118483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22536541721273252484745655 33804812581909878727118483)
            ·
              refine ⟨50707218872864818090677725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33804812581909878727118483 50707218872864818090677725)
              ·
                refine ⟨19015207077324306784004147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50707218872864818090677725 19015207077324306784004147)
                ·
                  refine ⟨28522810615986460176006221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19015207077324306784004147 28522810615986460176006221)
                  ·
                    refine ⟨10696053980994922566002333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28522810615986460176006221 10696053980994922566002333)
                    ·
                      refine ⟨4011020242873095962250875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10696053980994922566002333 4011020242873095962250875)
                      ·
                        rfl

theorem cell23_7811434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_7811434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811434 prefixEnd_7811434 := by exact prefixLift 7811434
  have htrace : WordTrace (prefixWord ++ tailWord_7811434) baseStart_7811434 baseEnd_7811434 := by
    simpa [prefixWord, tailWord_7811434, baseEnd_7811434] using wordTrace_append hprefix tailTrace_7811434
  have hstable : (prefixWord ++ tailWord_7811434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811434).length < 2 ^ (prefixWord ++ tailWord_7811434).sum := by decide
  have hdescent : baseEnd_7811434 < baseStart_7811434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811450 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_7811450 : Nat := 118140960795 + 7811450 * 2 ^ 59
def prefixEnd_7811450 : Nat := 4983230072969 + 3 ^ 40 * 7811450 * 2
def baseEnd_7811450 : Nat := 1337009486187855966550267

theorem tailTrace_7811450 : CollatzResearch.WordTrace tailWord_7811450 prefixEnd_7811450 1337009486187855966550267 := by
  unfold tailWord_7811450
  simp only [CollatzResearch.WordTrace]
  refine ⟨71226746887614553573205951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189937991700305476195215869 71226746887614553573205951)
  ·
    refine ⟨106840120331421830359808927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71226746887614553573205951 106840120331421830359808927)
    ·
      refine ⟨160260180497132745539713391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106840120331421830359808927 160260180497132745539713391)
      ·
        refine ⟨240390270745699118309570087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160260180497132745539713391 240390270745699118309570087)
        ·
          refine ⟨360585406118548677464355131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240390270745699118309570087 360585406118548677464355131)
          ·
            refine ⟨540878109177823016196532697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360585406118548677464355131 540878109177823016196532697)
            ·
              refine ⟨405658581883367262147399523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540878109177823016196532697 405658581883367262147399523)
              ·
                refine ⟨608487872825050893221099285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405658581883367262147399523 608487872825050893221099285)
                ·
                  refine ⟨28522869038674260619739029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 608487872825050893221099285 28522869038674260619739029)
                  ·
                    refine ⟨1337009486187855966550267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28522869038674260619739029 1337009486187855966550267)
                    ·
                      rfl

theorem cell23_7811450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_7811450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811450 prefixEnd_7811450 := by exact prefixLift 7811450
  have htrace : WordTrace (prefixWord ++ tailWord_7811450) baseStart_7811450 baseEnd_7811450 := by
    simpa [prefixWord, tailWord_7811450, baseEnd_7811450] using wordTrace_append hprefix tailTrace_7811450
  have hstable : (prefixWord ++ tailWord_7811450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811450).length < 2 ^ (prefixWord ++ tailWord_7811450).sum := by decide
  have hdescent : baseEnd_7811450 < baseStart_7811450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811487 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_7811487 : Nat := 118140960795 + 7811487 * 2 ^ 59
def prefixEnd_7811487 : Nat := 4983230072969 + 3 ^ 40 * 7811487 * 2
def baseEnd_7811487 : Nat := 4011047457347784254888131

theorem tailTrace_7811487 : CollatzResearch.WordTrace tailWord_7811487 prefixEnd_7811487 4011047457347784254888131 := by
  unfold tailWord_7811487
  simp only [CollatzResearch.WordTrace]
  refine ⟨284908337051324169611920715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189938891367549446407947143 284908337051324169611920715)
  ·
    refine ⟨427362505576986254417881073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284908337051324169611920715 427362505576986254417881073)
    ·
      refine ⟨320521879182739690813410805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427362505576986254417881073 320521879182739690813410805)
      ·
        refine ⟨30048926173381846013757263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320521879182739690813410805 30048926173381846013757263)
        ·
          refine ⟨45073389260072769020635895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30048926173381846013757263 45073389260072769020635895)
          ·
            refine ⟨67610083890109153530953843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45073389260072769020635895 67610083890109153530953843)
            ·
              refine ⟨101415125835163730296430765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67610083890109153530953843 101415125835163730296430765)
              ·
                refine ⟨38030672188186398861161537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101415125835163730296430765 38030672188186398861161537)
                ·
                  refine ⟨28523004141139799145871153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38030672188186398861161537 28523004141139799145871153)
                  ·
                    refine ⟨21392253105854849359403365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28523004141139799145871153 21392253105854849359403365)
                    ·
                      refine ⟨4011047457347784254888131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21392253105854849359403365 4011047457347784254888131)
                      ·
                        rfl

theorem cell23_7811487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_7811487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811487 prefixEnd_7811487 := by exact prefixLift 7811487
  have htrace : WordTrace (prefixWord ++ tailWord_7811487) baseStart_7811487 baseEnd_7811487 := by
    simpa [prefixWord, tailWord_7811487, baseEnd_7811487] using wordTrace_append hprefix tailTrace_7811487
  have hstable : (prefixWord ++ tailWord_7811487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811487).length < 2 ^ (prefixWord ++ tailWord_7811487).sum := by decide
  have hdescent : baseEnd_7811487 < baseStart_7811487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811491 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 1, 4, 2]
def baseStart_7811491 : Nat := 118140960795 + 7811491 * 2 ^ 59
def prefixEnd_7811491 : Nat := 4983230072969 + 3 ^ 40 * 7811491 * 2
def baseEnd_7811491 : Nat := 4011049511270402239238113

theorem tailTrace_7811491 : CollatzResearch.WordTrace tailWord_7811491 prefixEnd_7811491 4011049511270402239238113 := by
  unfold tailWord_7811491
  simp only [CollatzResearch.WordTrace]
  refine ⟨284908482943309678295066327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189938988628873118863377551 284908482943309678295066327)
  ·
    refine ⟨427362724414964517442599491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284908482943309678295066327 427362724414964517442599491)
    ·
      refine ⟨641044086622446776163899237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427362724414964517442599491 641044086622446776163899237)
      ·
        refine ⟨120195766241708770530731107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 641044086622446776163899237 120195766241708770530731107)
        ·
          refine ⟨180293649362563155796096661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120195766241708770530731107 180293649362563155796096661)
          ·
            refine ⟨8451264813870147927942031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180293649362563155796096661 8451264813870147927942031)
            ·
              refine ⟨12676897220805221891913047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8451264813870147927942031 12676897220805221891913047)
              ·
                refine ⟨19015345831207832837869571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12676897220805221891913047 19015345831207832837869571)
                ·
                  refine ⟨28523018746811749256804357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19015345831207832837869571 28523018746811749256804357)
                  ·
                    refine ⟨5348066015027202985650817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28523018746811749256804357 5348066015027202985650817)
                    ·
                      refine ⟨4011049511270402239238113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348066015027202985650817 4011049511270402239238113)
                      ·
                        rfl

theorem cell23_7811491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_7811491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811491 prefixEnd_7811491 := by exact prefixLift 7811491
  have htrace : WordTrace (prefixWord ++ tailWord_7811491) baseStart_7811491 baseEnd_7811491 := by
    simpa [prefixWord, tailWord_7811491, baseEnd_7811491] using wordTrace_append hprefix tailTrace_7811491
  have hstable : (prefixWord ++ tailWord_7811491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811491).length < 2 ^ (prefixWord ++ tailWord_7811491).sum := by decide
  have hdescent : baseEnd_7811491 < baseStart_7811491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811527 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 4, 5]
def baseStart_7811527 : Nat := 118140960795 + 7811527 * 2 ^ 59
def prefixEnd_7811527 : Nat := 4983230072969 + 3 ^ 40 * 7811527 * 2
def baseEnd_7811527 : Nat := 1337022665524654699462649

theorem tailTrace_7811527 : CollatzResearch.WordTrace tailWord_7811527 prefixEnd_7811527 1337022665524654699462649 := by
  unfold tailWord_7811527
  simp only [CollatzResearch.WordTrace]
  refine ⟨284909795971179256443376835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189939863980786170962251223 284909795971179256443376835)
  ·
    refine ⟨427364693956768884665065253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284909795971179256443376835 427364693956768884665065253)
    ·
      refine ⟨80130880116894165874699735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427364693956768884665065253 80130880116894165874699735)
      ·
        refine ⟨120196320175341248812049603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80130880116894165874699735 120196320175341248812049603)
        ·
          refine ⟨180294480263011873218074405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120196320175341248812049603 180294480263011873218074405)
          ·
            refine ⟨33805215049314726228388951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180294480263011873218074405 33805215049314726228388951)
            ·
              refine ⟨50707822573972089342583427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33805215049314726228388951 50707822573972089342583427)
              ·
                refine ⟨76061733860958134013875141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50707822573972089342583427 76061733860958134013875141)
                ·
                  refine ⟨14261575098929650127601589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76061733860958134013875141 14261575098929650127601589)
                  ·
                    refine ⟨1337022665524654699462649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14261575098929650127601589 1337022665524654699462649)
                    ·
                      rfl

theorem cell23_7811527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_7811527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811527 prefixEnd_7811527 := by exact prefixLift 7811527
  have htrace : WordTrace (prefixWord ++ tailWord_7811527) baseStart_7811527 baseEnd_7811527 := by
    simpa [prefixWord, tailWord_7811527, baseEnd_7811527] using wordTrace_append hprefix tailTrace_7811527
  have hstable : (prefixWord ++ tailWord_7811527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811527).length < 2 ^ (prefixWord ++ tailWord_7811527).sum := by decide
  have hdescent : baseEnd_7811527 < baseStart_7811527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811534 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2]
def baseStart_7811534 : Nat := 118140960795 + 7811534 * 2 ^ 59
def prefixEnd_7811534 : Nat := 4983230072969 + 3 ^ 40 * 7811534 * 2
def baseEnd_7811534 : Nat := 4011071590938545571000415

theorem tailTrace_7811534 : CollatzResearch.WordTrace tailWord_7811534 prefixEnd_7811534 4011071590938545571000415 := by
  unfold tailWord_7811534
  simp only [CollatzResearch.WordTrace]
  refine ⟨35613756410269237079860207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189940034188102597759254437 35613756410269237079860207)
  ·
    refine ⟨53420634615403855619790311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35613756410269237079860207 53420634615403855619790311)
    ·
      refine ⟨80130951923105783429685467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53420634615403855619790311 80130951923105783429685467)
      ·
        refine ⟨120196427884658675144528201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80130951923105783429685467 120196427884658675144528201)
        ·
          refine ⟨90147320913494006358396151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120196427884658675144528201 90147320913494006358396151)
          ·
            refine ⟨135220981370241009537594227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90147320913494006358396151 135220981370241009537594227)
            ·
              refine ⟨202831472055361514306391341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135220981370241009537594227 202831472055361514306391341)
              ·
                refine ⟨76061802020760567864896753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202831472055361514306391341 76061802020760567864896753)
                ·
                  refine ⟨57046351515570425898672565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76061802020760567864896753 57046351515570425898672565)
                  ·
                    refine ⟨5348095454584727428000553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57046351515570425898672565 5348095454584727428000553)
                    ·
                      refine ⟨4011071590938545571000415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348095454584727428000553 4011071590938545571000415)
                      ·
                        rfl

theorem cell23_7811534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_7811534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811534 prefixEnd_7811534 := by exact prefixLift 7811534
  have htrace : WordTrace (prefixWord ++ tailWord_7811534) baseStart_7811534 baseEnd_7811534 := by
    simpa [prefixWord, tailWord_7811534, baseEnd_7811534] using wordTrace_append hprefix tailTrace_7811534
  have hstable : (prefixWord ++ tailWord_7811534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811534).length < 2 ^ (prefixWord ++ tailWord_7811534).sum := by decide
  have hdescent : baseEnd_7811534 < baseStart_7811534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811564 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 4]
def baseStart_7811564 : Nat := 118140960795 + 7811564 * 2 ^ 59
def prefixEnd_7811564 : Nat := 4983230072969 + 3 ^ 40 * 7811564 * 2
def baseEnd_7811564 : Nat := 4011086995358180453625277

theorem tailTrace_7811564 : CollatzResearch.WordTrace tailWord_7811564 prefixEnd_7811564 4011086995358180453625277 := by
  unfold tailWord_7811564
  simp only [CollatzResearch.WordTrace]
  refine ⟨142455572736022605881236873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189940763648030141174982497 142455572736022605881236873)
  ·
    refine ⟨106841679552016954410927655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142455572736022605881236873 106841679552016954410927655)
    ·
      refine ⟨160262519328025431616391483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106841679552016954410927655 160262519328025431616391483)
      ·
        refine ⟨240393778992038147424587225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160262519328025431616391483 240393778992038147424587225)
        ·
          refine ⟨180295334244028610568440419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240393778992038147424587225 180295334244028610568440419)
          ·
            refine ⟨270443001366042915852660629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180295334244028610568440419 270443001366042915852660629)
            ·
              refine ⟨12677015689033261680593467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 270443001366042915852660629 12677015689033261680593467)
              ·
                refine ⟨19015523533549892520890201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12677015689033261680593467 19015523533549892520890201)
                ·
                  refine ⟨14261642650162419390667651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19015523533549892520890201 14261642650162419390667651)
                  ·
                    refine ⟨21392463975243629086001477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14261642650162419390667651 21392463975243629086001477)
                    ·
                      refine ⟨4011086995358180453625277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21392463975243629086001477 4011086995358180453625277)
                      ·
                        rfl

theorem cell23_7811564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_7811564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811564 prefixEnd_7811564 := by exact prefixLift 7811564
  have htrace : WordTrace (prefixWord ++ tailWord_7811564) baseStart_7811564 baseEnd_7811564 := by
    simpa [prefixWord, tailWord_7811564, baseEnd_7811564] using wordTrace_append hprefix tailTrace_7811564
  have hstable : (prefixWord ++ tailWord_7811564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811564).length < 2 ^ (prefixWord ++ tailWord_7811564).sum := by decide
  have hdescent : baseEnd_7811564 < baseStart_7811564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811638 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_7811638 : Nat := 118140960795 + 7811638 * 2 ^ 59
def prefixEnd_7811638 : Nat := 4983230072969 + 3 ^ 40 * 7811638 * 2
def baseEnd_7811638 : Nat := 445680554769623684899993

theorem tailTrace_7811638 : CollatzResearch.WordTrace tailWord_7811638 prefixEnd_7811638 445680554769623684899993 := by
  unfold tailWord_7811638
  simp only [CollatzResearch.WordTrace]
  refine ⟨17807115279611070150041723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189942562982518081600445045 17807115279611070150041723)
  ·
    refine ⟨26710672919416605225062585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17807115279611070150041723 26710672919416605225062585)
    ·
      refine ⟨20033004689562453918796939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26710672919416605225062585 20033004689562453918796939)
      ·
        refine ⟨30049507034343680878195409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20033004689562453918796939 30049507034343680878195409)
        ·
          refine ⟨22537130275757760658646557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30049507034343680878195409 22537130275757760658646557)
          ·
            refine ⟨8451423853409160246992459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22537130275757760658646557 8451423853409160246992459)
            ·
              refine ⟨12677135780113740370488689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8451423853409160246992459 12677135780113740370488689)
              ·
                refine ⟨9507851835085305277866517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12677135780113740370488689 9507851835085305277866517)
                ·
                  refine ⟨445680554769623684899993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9507851835085305277866517 445680554769623684899993)
                  ·
                    rfl

theorem cell23_7811638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_7811638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811638 prefixEnd_7811638 := by exact prefixLift 7811638
  have htrace : WordTrace (prefixWord ++ tailWord_7811638) baseStart_7811638 baseEnd_7811638 := by
    simpa [prefixWord, tailWord_7811638, baseEnd_7811638] using wordTrace_append hprefix tailTrace_7811638
  have hstable : (prefixWord ++ tailWord_7811638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811638).length < 2 ^ (prefixWord ++ tailWord_7811638).sum := by decide
  have hdescent : baseEnd_7811638 < baseStart_7811638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811641 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 4, 3, 2]
def baseStart_7811641 : Nat := 118140960795 + 7811641 * 2 ^ 59
def prefixEnd_7811641 : Nat := 4983230072969 + 3 ^ 40 * 7811641 * 2
def baseEnd_7811641 : Nat := 4011126533368576652362423

theorem tailTrace_7811641 : CollatzResearch.WordTrace tailWord_7811641 prefixEnd_7811641 4011126533368576652362423 := by
  unfold tailWord_7811641
  simp only [CollatzResearch.WordTrace]
  refine ⟨284913953892766253913026777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189942635928510835942017851 284913953892766253913026777)
  ·
    refine ⟨213685465419574690434770083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284913953892766253913026777 213685465419574690434770083)
    ·
      refine ⟨320528198129362035652155125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213685465419574690434770083 320528198129362035652155125)
      ·
        refine ⟨30049518574627690842389543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320528198129362035652155125 30049518574627690842389543)
        ·
          refine ⟨45074277861941536263584315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30049518574627690842389543 45074277861941536263584315)
          ·
            refine ⟨67611416792912304395376473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45074277861941536263584315 67611416792912304395376473)
            ·
              refine ⟨50708562594684228296532355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67611416792912304395376473 50708562594684228296532355)
              ·
                refine ⟨76062843892026342444798533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50708562594684228296532355 76062843892026342444798533)
                ·
                  refine ⟨14261783229754939208399725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76062843892026342444798533 14261783229754939208399725)
                  ·
                    refine ⟨5348168711158102203149897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14261783229754939208399725 5348168711158102203149897)
                    ·
                      refine ⟨4011126533368576652362423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348168711158102203149897 4011126533368576652362423)
                      ·
                        rfl

theorem cell23_7811641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_7811641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811641 prefixEnd_7811641 := by exact prefixLift 7811641
  have htrace : WordTrace (prefixWord ++ tailWord_7811641) baseStart_7811641 baseEnd_7811641 := by
    simpa [prefixWord, tailWord_7811641, baseEnd_7811641] using wordTrace_append hprefix tailTrace_7811641
  have hstable : (prefixWord ++ tailWord_7811641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811641).length < 2 ^ (prefixWord ++ tailWord_7811641).sum := by decide
  have hdescent : baseEnd_7811641 < baseStart_7811641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811648 : List Nat := [2, 1, 1, 2, 2, 2, 4, 4, 1, 1, 3]
def baseStart_7811648 : Nat := 118140960795 + 7811648 * 2 ^ 59
def prefixEnd_7811648 : Nat := 4983230072969 + 3 ^ 40 * 7811648 * 2
def baseEnd_7811648 : Nat := 4011130127733158124974891

theorem tailTrace_7811648 : CollatzResearch.WordTrace tailWord_7811648 prefixEnd_7811648 4011130127733158124974891 := by
  unfold tailWord_7811648
  simp only [CollatzResearch.WordTrace]
  refine ⟨142457104601870447054265799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189942806135827262739021065 142457104601870447054265799)
  ·
    refine ⟨213685656902805670581398699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142457104601870447054265799 213685656902805670581398699)
    ·
      refine ⟨320528485354208505872098049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213685656902805670581398699 320528485354208505872098049)
      ·
        refine ⟨240396364015656379404073537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320528485354208505872098049 240396364015656379404073537)
        ·
          refine ⟨180297273011742284553055153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240396364015656379404073537 180297273011742284553055153)
          ·
            refine ⟨135222954758806713414791365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180297273011742284553055153 135222954758806713414791365)
            ·
              refine ⟨25354304017276258765273381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135222954758806713414791365 25354304017276258765273381)
              ·
                refine ⟨4753932003239298518488759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25354304017276258765273381 4753932003239298518488759)
                ·
                  refine ⟨7130898004858947777733139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753932003239298518488759 7130898004858947777733139)
                  ·
                    refine ⟨10696347007288421666599709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7130898004858947777733139 10696347007288421666599709)
                    ·
                      refine ⟨4011130127733158124974891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10696347007288421666599709 4011130127733158124974891)
                      ·
                        rfl

theorem cell23_7811648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 1, 1, 3].length) (baseStart_7811648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811648 prefixEnd_7811648 := by exact prefixLift 7811648
  have htrace : WordTrace (prefixWord ++ tailWord_7811648) baseStart_7811648 baseEnd_7811648 := by
    simpa [prefixWord, tailWord_7811648, baseEnd_7811648] using wordTrace_append hprefix tailTrace_7811648
  have hstable : (prefixWord ++ tailWord_7811648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811648).length < 2 ^ (prefixWord ++ tailWord_7811648).sum := by decide
  have hdescent : baseEnd_7811648 < baseStart_7811648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811671 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 4]
def baseStart_7811671 : Nat := 118140960795 + 7811671 * 2 ^ 59
def prefixEnd_7811671 : Nat := 4983230072969 + 3 ^ 40 * 7811671 * 2
def baseEnd_7811671 : Nat := 4011141937788211534987285

theorem tailTrace_7811671 : CollatzResearch.WordTrace tailWord_7811671 prefixEnd_7811671 4011141937788211534987285 := by
  unfold tailWord_7811671
  simp only [CollatzResearch.WordTrace]
  refine ⟨284915048082657569036618867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189943365388438379357745911 284915048082657569036618867)
  ·
    refine ⟨427372572123986353554928301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284915048082657569036618867 427372572123986353554928301)
    ·
      refine ⟨160264714546494882583098113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427372572123986353554928301 160264714546494882583098113)
      ·
        refine ⟨120198535909871161937323585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160264714546494882583098113 120198535909871161937323585)
        ·
          refine ⟨90148901932403371452992689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120198535909871161937323585 90148901932403371452992689)
          ·
            refine ⟨67611676449302528589744517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90148901932403371452992689 67611676449302528589744517)
            ·
              refine ⟨12677189334244224110577097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67611676449302528589744517 12677189334244224110577097)
              ·
                refine ⟨9507892000683168082932823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12677189334244224110577097 9507892000683168082932823)
                ·
                  refine ⟨14261838001024752124399235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9507892000683168082932823 14261838001024752124399235)
                  ·
                    refine ⟨21392757001537128186598853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14261838001024752124399235 21392757001537128186598853)
                    ·
                      refine ⟨4011141937788211534987285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21392757001537128186598853 4011141937788211534987285)
                      ·
                        rfl

theorem cell23_7811671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_7811671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811671 prefixEnd_7811671 := by exact prefixLift 7811671
  have htrace : WordTrace (prefixWord ++ tailWord_7811671) baseStart_7811671 baseEnd_7811671 := by
    simpa [prefixWord, tailWord_7811671, baseEnd_7811671] using wordTrace_append hprefix tailTrace_7811671
  have hstable : (prefixWord ++ tailWord_7811671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811671).length < 2 ^ (prefixWord ++ tailWord_7811671).sum := by decide
  have hdescent : baseEnd_7811671 < baseStart_7811671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811684 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_7811684 : Nat := 118140960795 + 7811684 * 2 ^ 59
def prefixEnd_7811684 : Nat := 4983230072969 + 3 ^ 40 * 7811684 * 2
def baseEnd_7811684 : Nat := 4011148613036719984124725

theorem tailTrace_7811684 : CollatzResearch.WordTrace tailWord_7811684 prefixEnd_7811684 4011148613036719984124725 := by
  unfold tailWord_7811684
  simp only [CollatzResearch.WordTrace]
  refine ⟨142457761115805236128421053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189943681487740314837894737 142457761115805236128421053)
  ·
    refine ⟨53421660418426963548157895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142457761115805236128421053 53421660418426963548157895)
    ·
      refine ⟨80132490627640445322236843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53421660418426963548157895 80132490627640445322236843)
      ·
        refine ⟨120198735941460667983355265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80132490627640445322236843 120198735941460667983355265)
        ·
          refine ⟨90149051956095500987516449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120198735941460667983355265 90149051956095500987516449)
          ·
            refine ⟨67611788967071625740637337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90149051956095500987516449 67611788967071625740637337)
            ·
              refine ⟨50708841725303719305478003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67611788967071625740637337 50708841725303719305478003)
              ·
                refine ⟨76063262587955578958217005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50708841725303719305478003 76063262587955578958217005)
                ·
                  refine ⟨28523723470483342109331377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76063262587955578958217005 28523723470483342109331377)
                  ·
                    refine ⟨21392792602862506581998533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28523723470483342109331377 21392792602862506581998533)
                    ·
                      refine ⟨4011148613036719984124725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21392792602862506581998533 4011148613036719984124725)
                      ·
                        rfl

theorem cell23_7811684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_7811684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811684 prefixEnd_7811684 := by exact prefixLift 7811684
  have htrace : WordTrace (prefixWord ++ tailWord_7811684) baseStart_7811684 baseEnd_7811684 := by
    simpa [prefixWord, tailWord_7811684, baseEnd_7811684] using wordTrace_append hprefix tailTrace_7811684
  have hstable : (prefixWord ++ tailWord_7811684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811684).length < 2 ^ (prefixWord ++ tailWord_7811684).sum := by decide
  have hdescent : baseEnd_7811684 < baseStart_7811684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811694 : List Nat := [4, 1, 2, 2, 2, 1, 11]
def baseStart_7811694 : Nat := 118140960795 + 7811694 * 2 ^ 59
def prefixEnd_7811694 : Nat := 4983230072969 + 3 ^ 40 * 7811694 * 2
def baseEnd_7811694 : Nat := 49520416640040307962959

theorem tailTrace_7811694 : CollatzResearch.WordTrace tailWord_7811694 prefixEnd_7811694 49520416640040307962959 := by
  unfold tailWord_7811694
  simp only [CollatzResearch.WordTrace]
  refine ⟨35614485870196780495588267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189943924641049495976470757 35614485870196780495588267)
  ·
    refine ⟨53421728805295170743382401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35614485870196780495588267 53421728805295170743382401)
    ·
      refine ⟨40066296603971378057536801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53421728805295170743382401 40066296603971378057536801)
      ·
        refine ⟨30049722452978533543152601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40066296603971378057536801 30049722452978533543152601)
        ·
          refine ⟨22537291839733900157364451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30049722452978533543152601 22537291839733900157364451)
          ·
            refine ⟨33805937759600850236046677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22537291839733900157364451 33805937759600850236046677)
            ·
              refine ⟨49520416640040307962959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33805937759600850236046677 49520416640040307962959)
              ·
                rfl

theorem cell23_7811694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 11].length) (baseStart_7811694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811694 prefixEnd_7811694 := by exact prefixLift 7811694
  have htrace : WordTrace (prefixWord ++ tailWord_7811694) baseStart_7811694 baseEnd_7811694 := by
    simpa [prefixWord, tailWord_7811694, baseEnd_7811694] using wordTrace_append hprefix tailTrace_7811694
  have hstable : (prefixWord ++ tailWord_7811694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811694).length < 2 ^ (prefixWord ++ tailWord_7811694).sum := by decide
  have hdescent : baseEnd_7811694 < baseStart_7811694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811704 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 3, 3, 3]
def baseStart_7811704 : Nat := 118140960795 + 7811704 * 2 ^ 59
def prefixEnd_7811704 : Nat := 4983230072969 + 3 ^ 40 * 7811704 * 2
def baseEnd_7811704 : Nat := 4011158882649809905874633

theorem tailTrace_7811704 : CollatzResearch.WordTrace tailWord_7811704 prefixEnd_7811704 4011158882649809905874633 := by
  unfold tailWord_7811704
  simp only [CollatzResearch.WordTrace]
  refine ⟨142458125845769007836285083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189944167794358677115046777 142458125845769007836285083)
  ·
    refine ⟨213687188768653511754427625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142458125845769007836285083 213687188768653511754427625)
    ·
      refine ⟨160265391576490133815820719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213687188768653511754427625 160265391576490133815820719)
      ·
        refine ⟨240398087364735200723731079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160265391576490133815820719 240398087364735200723731079)
        ·
          refine ⟨360597131047102801085596619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240398087364735200723731079 360597131047102801085596619)
          ·
            refine ⟨540895696570654201628394929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360597131047102801085596619 540895696570654201628394929)
            ·
              refine ⟨405671772427990651221296197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540895696570654201628394929 405671772427990651221296197)
              ·
                refine ⟨76063457330248247103993037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405671772427990651221296197 76063457330248247103993037)
                ·
                  refine ⟨28523796498843092663997389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76063457330248247103993037 28523796498843092663997389)
                  ·
                    refine ⟨10696423687066159748999021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28523796498843092663997389 10696423687066159748999021)
                    ·
                      refine ⟨4011158882649809905874633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10696423687066159748999021 4011158882649809905874633)
                      ·
                        rfl

theorem cell23_7811704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_7811704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811704 prefixEnd_7811704 := by exact prefixLift 7811704
  have htrace : WordTrace (prefixWord ++ tailWord_7811704) baseStart_7811704 baseEnd_7811704 := by
    simpa [prefixWord, tailWord_7811704, baseEnd_7811704] using wordTrace_append hprefix tailTrace_7811704
  have hstable : (prefixWord ++ tailWord_7811704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811704).length < 2 ^ (prefixWord ++ tailWord_7811704).sum := by decide
  have hdescent : baseEnd_7811704 < baseStart_7811704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811705 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 3, 2, 2]
def baseStart_7811705 : Nat := 118140960795 + 7811705 * 2 ^ 59
def prefixEnd_7811705 : Nat := 4983230072969 + 3 ^ 40 * 7811705 * 2
def baseEnd_7811705 : Nat := 4011159396130464401962129

theorem tailTrace_7811705 : CollatzResearch.WordTrace tailWord_7811705 prefixEnd_7811705 4011159396130464401962129 := by
  unfold tailWord_7811705
  simp only [CollatzResearch.WordTrace]
  refine ⟨284916288164534392843356569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189944192109689595228904379 284916288164534392843356569)
  ·
    refine ⟨213687216123400794632517427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284916288164534392843356569 213687216123400794632517427)
    ·
      refine ⟨320530824185101191948776141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213687216123400794632517427 320530824185101191948776141)
      ·
        refine ⟨120199059069412946980791053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320530824185101191948776141 120199059069412946980791053)
        ·
          refine ⟨45074647151029855117796645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120199059069412946980791053 45074647151029855117796645)
          ·
            refine ⟨8451496340818097834586871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45074647151029855117796645 8451496340818097834586871)
            ·
              refine ⟨12677244511227146751880307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8451496340818097834586871 12677244511227146751880307)
              ·
                refine ⟨19015866766840720127820461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12677244511227146751880307 19015866766840720127820461)
                ·
                  refine ⟨7130950037565270047932673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19015866766840720127820461 7130950037565270047932673)
                  ·
                    refine ⟨5348212528173952535949505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7130950037565270047932673 5348212528173952535949505)
                    ·
                      refine ⟨4011159396130464401962129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348212528173952535949505 4011159396130464401962129)
                      ·
                        rfl

theorem cell23_7811705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_7811705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811705 prefixEnd_7811705 := by exact prefixLift 7811705
  have htrace : WordTrace (prefixWord ++ tailWord_7811705) baseStart_7811705 baseEnd_7811705 := by
    simpa [prefixWord, tailWord_7811705, baseEnd_7811705] using wordTrace_append hprefix tailTrace_7811705
  have hstable : (prefixWord ++ tailWord_7811705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811705).length < 2 ^ (prefixWord ++ tailWord_7811705).sum := by decide
  have hdescent : baseEnd_7811705 < baseStart_7811705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811731 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 3, 3, 2]
def baseStart_7811731 : Nat := 118140960795 + 7811731 * 2 ^ 59
def prefixEnd_7811731 : Nat := 4983230072969 + 3 ^ 40 * 7811731 * 2
def baseEnd_7811731 : Nat := 4011172746627481300237009

theorem tailTrace_7811731 : CollatzResearch.WordTrace tailWord_7811731 prefixEnd_7811731 4011172746627481300237009 := by
  unfold tailWord_7811731
  simp only [CollatzResearch.WordTrace]
  refine ⟨284917236462440199283803047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189944824308293466189202031 284917236462440199283803047)
  ·
    refine ⟨427375854693660298925704571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284917236462440199283803047 427375854693660298925704571)
    ·
      refine ⟨641063782040490448388556857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427375854693660298925704571 641063782040490448388556857)
      ·
        refine ⟨480797836530367836291417643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641063782040490448388556857 480797836530367836291417643)
        ·
          refine ⟨721196754795551754437126465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480797836530367836291417643 721196754795551754437126465)
          ·
            refine ⟨540897566096663815827844849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721196754795551754437126465 540897566096663815827844849)
            ·
              refine ⟨405673174572497861870883637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540897566096663815827844849 405673174572497861870883637)
              ·
                refine ⟨38031860116171674550395341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405673174572497861870883637 38031860116171674550395341)
                ·
                  refine ⟨14261947543564377956398253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38031860116171674550395341 14261947543564377956398253)
                  ·
                    refine ⟨5348230328836641733649345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14261947543564377956398253 5348230328836641733649345)
                    ·
                      refine ⟨4011172746627481300237009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348230328836641733649345 4011172746627481300237009)
                      ·
                        rfl

theorem cell23_7811731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 3, 2].length) (baseStart_7811731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811731 prefixEnd_7811731 := by exact prefixLift 7811731
  have htrace : WordTrace (prefixWord ++ tailWord_7811731) baseStart_7811731 baseEnd_7811731 := by
    simpa [prefixWord, tailWord_7811731, baseEnd_7811731] using wordTrace_append hprefix tailTrace_7811731
  have hstable : (prefixWord ++ tailWord_7811731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811731).length < 2 ^ (prefixWord ++ tailWord_7811731).sum := by decide
  have hdescent : baseEnd_7811731 < baseStart_7811731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811784 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 9]
def baseStart_7811784 : Nat := 118140960795 + 7811784 * 2 ^ 59
def prefixEnd_7811784 : Nat := 4983230072969 + 3 ^ 40 * 7811784 * 2
def baseEnd_7811784 : Nat := 445688884566907732541585

theorem tailTrace_7811784 : CollatzResearch.WordTrace tailWord_7811784 prefixEnd_7811784 445688884566907732541585 := by
  unfold tailWord_7811784
  simp only [CollatzResearch.WordTrace]
  refine ⟨142459584765624094667741203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189946113020832126223654937 142459584765624094667741203)
  ·
    refine ⟨213689377148436142001611805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142459584765624094667741203 213689377148436142001611805)
    ·
      refine ⟨80133516430663553250604427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213689377148436142001611805 80133516430663553250604427)
      ·
        refine ⟨120200274645995329875906641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80133516430663553250604427 120200274645995329875906641)
        ·
          refine ⟨90150205984496497406929981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120200274645995329875906641 90150205984496497406929981)
          ·
            refine ⟨33806327244186186527598743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90150205984496497406929981 33806327244186186527598743)
            ·
              refine ⟨50709490866279279791398115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33806327244186186527598743 50709490866279279791398115)
              ·
                refine ⟨76064236299418919687097173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50709490866279279791398115 76064236299418919687097173)
                ·
                  refine ⟨445688884566907732541585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76064236299418919687097173 445688884566907732541585)
                  ·
                    rfl

theorem cell23_7811784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 9].length) (baseStart_7811784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811784 prefixEnd_7811784 := by exact prefixLift 7811784
  have htrace : WordTrace (prefixWord ++ tailWord_7811784) baseStart_7811784 baseEnd_7811784 := by
    simpa [prefixWord, tailWord_7811784, baseEnd_7811784] using wordTrace_append hprefix tailTrace_7811784
  have hstable : (prefixWord ++ tailWord_7811784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811784).length < 2 ^ (prefixWord ++ tailWord_7811784).sum := by decide
  have hdescent : baseEnd_7811784 < baseStart_7811784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811812 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 2, 2, 2]
def baseStart_7811812 : Nat := 118140960795 + 7811812 * 2 ^ 59
def prefixEnd_7811812 : Nat := 4983230072969 + 3 ^ 40 * 7811812 * 2
def baseEnd_7811812 : Nat := 4011214338560495483324137

theorem tailTrace_7811812 : CollatzResearch.WordTrace tailWord_7811812 prefixEnd_7811812 4011214338560495483324137 := by
  unfold tailWord_7811812
  simp only [CollatzResearch.WordTrace]
  refine ⟨142460095387573375058750845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189946793850097833411667793 142460095387573375058750845)
  ·
    refine ⟨53422535770340015647031567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142460095387573375058750845 53422535770340015647031567)
    ·
      refine ⟨80133803655510023470547351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53422535770340015647031567 80133803655510023470547351)
      ·
        refine ⟨120200705483265035205821027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80133803655510023470547351 120200705483265035205821027)
        ·
          refine ⟨180301058224897552808731541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120200705483265035205821027 180301058224897552808731541)
          ·
            refine ⟨8451612104292072787909291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180301058224897552808731541 8451612104292072787909291)
            ·
              refine ⟨12677418156438109181863937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8451612104292072787909291 12677418156438109181863937)
              ·
                refine ⟨9508063617328581886397953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12677418156438109181863937 9508063617328581886397953)
                ·
                  refine ⟨7131047712996436414798465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9508063617328581886397953 7131047712996436414798465)
                  ·
                    refine ⟨5348285784747327311098849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7131047712996436414798465 5348285784747327311098849)
                    ·
                      refine ⟨4011214338560495483324137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348285784747327311098849 4011214338560495483324137)
                      ·
                        rfl

theorem cell23_7811812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_7811812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811812 prefixEnd_7811812 := by exact prefixLift 7811812
  have htrace : WordTrace (prefixWord ++ tailWord_7811812) baseStart_7811812 baseEnd_7811812 := by
    simpa [prefixWord, tailWord_7811812, baseEnd_7811812] using wordTrace_append hprefix tailTrace_7811812
  have hstable : (prefixWord ++ tailWord_7811812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811812).length < 2 ^ (prefixWord ++ tailWord_7811812).sum := by decide
  have hdescent : baseEnd_7811812 < baseStart_7811812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811824 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_7811824 : Nat := 118140960795 + 7811824 * 2 ^ 59
def prefixEnd_7811824 : Nat := 4983230072969 + 3 ^ 40 * 7811824 * 2
def baseEnd_7811824 : Nat := 4011220500328349436374081

theorem tailTrace_7811824 : CollatzResearch.WordTrace tailWord_7811824 prefixEnd_7811824 4011220500328349436374081 := by
  unfold tailWord_7811824
  simp only [CollatzResearch.WordTrace]
  refine ⟨142460314225551638083469263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189947085634068850777959017 142460314225551638083469263)
  ·
    refine ⟨213690471338327457125203895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142460314225551638083469263 213690471338327457125203895)
    ·
      refine ⟨320535707007491185687805843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213690471338327457125203895 320535707007491185687805843)
      ·
        refine ⟨480803560511236778531708765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320535707007491185687805843 480803560511236778531708765)
        ·
          refine ⟨180301335191713791949390787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480803560511236778531708765 180301335191713791949390787)
          ·
            refine ⟨270452002787570687924086181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180301335191713791949390787 270452002787570687924086181)
            ·
              refine ⟨50709750522669503985766159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270452002787570687924086181 50709750522669503985766159)
              ·
                refine ⟨76064625784004255978649239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50709750522669503985766159 76064625784004255978649239)
                ·
                  refine ⟨114096938676006383967973859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76064625784004255978649239 114096938676006383967973859)
                  ·
                    refine ⟨171145408014009575951960789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114096938676006383967973859 171145408014009575951960789)
                    ·
                      refine ⟨4011220500328349436374081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171145408014009575951960789 4011220500328349436374081)
                      ·
                        rfl

theorem cell23_7811824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_7811824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811824 prefixEnd_7811824 := by exact prefixLift 7811824
  have htrace : WordTrace (prefixWord ++ tailWord_7811824) baseStart_7811824 baseEnd_7811824 := by
    simpa [prefixWord, tailWord_7811824, baseEnd_7811824] using wordTrace_append hprefix tailTrace_7811824
  have hstable : (prefixWord ++ tailWord_7811824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811824).length < 2 ^ (prefixWord ++ tailWord_7811824).sum := by decide
  have hdescent : baseEnd_7811824 < baseStart_7811824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811851 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 4]
def baseStart_7811851 : Nat := 118140960795 + 7811851 * 2 ^ 59
def prefixEnd_7811851 : Nat := 4983230072969 + 3 ^ 40 * 7811851 * 2
def baseEnd_7811851 : Nat := 4011234364306020830736457

theorem tailTrace_7811851 : CollatzResearch.WordTrace tailWord_7811851 prefixEnd_7811851 4011234364306020830736457 := by
  unfold tailWord_7811851
  simp only [CollatzResearch.WordTrace]
  refine ⟨284921613222005459778171407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189947742148003639852114271 284921613222005459778171407)
  ·
    refine ⟨427382419833008189667257111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284921613222005459778171407 427382419833008189667257111)
    ·
      refine ⟨641073629749512284500885667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427382419833008189667257111 641073629749512284500885667)
      ·
        refine ⟨961610444624268426751328501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641073629749512284500885667 961610444624268426751328501)
        ·
          refine ⟨90150979183525165007937047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 961610444624268426751328501 90150979183525165007937047)
          ·
            refine ⟨135226468775287747511905571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90150979183525165007937047 135226468775287747511905571)
            ·
              refine ⟨202839703162931621267858357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135226468775287747511905571 202839703162931621267858357)
              ·
                refine ⟨19016222171524839493861721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202839703162931621267858357 19016222171524839493861721)
                ·
                  refine ⟨14262166628643629620396291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19016222171524839493861721 14262166628643629620396291)
                  ·
                    refine ⟨21393249942965444430594437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14262166628643629620396291 21393249942965444430594437)
                    ·
                      refine ⟨4011234364306020830736457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21393249942965444430594437 4011234364306020830736457)
                      ·
                        rfl

theorem cell23_7811851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 4].length) (baseStart_7811851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811851 prefixEnd_7811851 := by exact prefixLift 7811851
  have htrace : WordTrace (prefixWord ++ tailWord_7811851) baseStart_7811851 baseEnd_7811851 := by
    simpa [prefixWord, tailWord_7811851, baseEnd_7811851] using wordTrace_append hprefix tailTrace_7811851
  have hstable : (prefixWord ++ tailWord_7811851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811851).length < 2 ^ (prefixWord ++ tailWord_7811851).sum := by decide
  have hdescent : baseEnd_7811851 < baseStart_7811851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811868 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_7811868 : Nat := 118140960795 + 7811868 * 2 ^ 59
def prefixEnd_7811868 : Nat := 4983230072969 + 3 ^ 40 * 7811868 * 2
def baseEnd_7811868 : Nat := 4011243093477147264223879

theorem tailTrace_7811868 : CollatzResearch.WordTrace tailWord_7811868 prefixEnd_7811868 4011243093477147264223879 := by
  unfold tailWord_7811868
  simp only [CollatzResearch.WordTrace]
  refine ⟨142461116631471935840770129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189948155508629247787693505 142461116631471935840770129)
  ·
    refine ⟨106845837473603951880577597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142461116631471935840770129 106845837473603951880577597)
    ·
      refine ⟨40067189052601481955216599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106845837473603951880577597 40067189052601481955216599)
      ·
        refine ⟨60100783578902222932824899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40067189052601481955216599 60100783578902222932824899)
        ·
          refine ⟨90151175368353334399237349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60100783578902222932824899 90151175368353334399237349)
          ·
            refine ⟨16903345381566250199857003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90151175368353334399237349 16903345381566250199857003)
            ·
              refine ⟨25355018072349375299785505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16903345381566250199857003 25355018072349375299785505)
              ·
                refine ⟨19016263554262031474839129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25355018072349375299785505 19016263554262031474839129)
                ·
                  refine ⟨14262197665696523606129347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19016263554262031474839129 14262197665696523606129347)
                  ·
                    refine ⟨21393296498544785409194021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14262197665696523606129347 21393296498544785409194021)
                    ·
                      refine ⟨4011243093477147264223879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21393296498544785409194021 4011243093477147264223879)
                      ·
                        rfl

theorem cell23_7811868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_7811868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811868 prefixEnd_7811868 := by exact prefixLift 7811868
  have htrace : WordTrace (prefixWord ++ tailWord_7811868) baseStart_7811868 baseEnd_7811868 := by
    simpa [prefixWord, tailWord_7811868, baseEnd_7811868] using wordTrace_append hprefix tailTrace_7811868
  have hstable : (prefixWord ++ tailWord_7811868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811868).length < 2 ^ (prefixWord ++ tailWord_7811868).sum := by decide
  have hdescent : baseEnd_7811868 < baseStart_7811868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811975 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_7811975 : Nat := 118140960795 + 7811975 * 2 ^ 59
def prefixEnd_7811975 : Nat := 4983230072969 + 3 ^ 40 * 7811975 * 2
def baseEnd_7811975 : Nat := 4011298035907178345585887

theorem tailTrace_7811975 : CollatzResearch.WordTrace tailWord_7811975 prefixEnd_7811975 4011298035907178345585887 := by
  unfold tailWord_7811975
  simp only [CollatzResearch.WordTrace]
  refine ⟨284926135873556228955685379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189950757249037485970456919 284926135873556228955685379)
  ·
    refine ⟨427389203810334343433528069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284926135873556228955685379 427389203810334343433528069)
    ·
      refine ⟨80135475714437689393786513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427389203810334343433528069 80135475714437689393786513)
      ·
        refine ⟨60101606785828267045339885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80135475714437689393786513 60101606785828267045339885)
        ·
          refine ⟨22538102544685600142002457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60101606785828267045339885 22538102544685600142002457)
          ·
            refine ⟨16903576908514200106501843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22538102544685600142002457 16903576908514200106501843)
            ·
              refine ⟨25355365362771300159752765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16903576908514200106501843 25355365362771300159752765)
              ·
                refine ⟨9508262011039237559907287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25355365362771300159752765 9508262011039237559907287)
                ·
                  refine ⟨14262393016558856339860931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9508262011039237559907287 14262393016558856339860931)
                  ·
                    refine ⟨21393589524838284509791397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14262393016558856339860931 21393589524838284509791397)
                    ·
                      refine ⟨4011298035907178345585887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21393589524838284509791397 4011298035907178345585887)
                      ·
                        rfl

theorem cell23_7811975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_7811975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811975 prefixEnd_7811975 := by exact prefixLift 7811975
  have htrace : WordTrace (prefixWord ++ tailWord_7811975) baseStart_7811975 baseEnd_7811975 := by
    simpa [prefixWord, tailWord_7811975, baseEnd_7811975] using wordTrace_append hprefix tailTrace_7811975
  have hstable : (prefixWord ++ tailWord_7811975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811975).length < 2 ^ (prefixWord ++ tailWord_7811975).sum := by decide
  have hdescent : baseEnd_7811975 < baseStart_7811975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7811988 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_7811988 : Nat := 118140960795 + 7811988 * 2 ^ 59
def prefixEnd_7811988 : Nat := 4983230072969 + 3 ^ 40 * 7811988 * 2
def baseEnd_7811988 : Nat := 4011304711155686794723327

theorem tailTrace_7811988 : CollatzResearch.WordTrace tailWord_7811988 prefixEnd_7811988 4011304711155686794723327 := by
  unfold tailWord_7811988
  simp only [CollatzResearch.WordTrace]
  refine ⟨142463305011254566087954309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189951073348339421450605745 142463305011254566087954309)
  ·
    refine ⟨26711869689610231141491433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142463305011254566087954309 26711869689610231141491433)
    ·
      refine ⟨20033902267207673356118575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26711869689610231141491433 20033902267207673356118575)
      ·
        refine ⟨30050853400811510034177863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20033902267207673356118575 30050853400811510034177863)
        ·
          refine ⟨45076280101217265051266795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30050853400811510034177863 45076280101217265051266795)
          ·
            refine ⟨67614420151825897576900193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45076280101217265051266795 67614420151825897576900193)
            ·
              refine ⟨50710815113869423182675145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67614420151825897576900193 50710815113869423182675145)
              ·
                refine ⟨38033111335402067387006359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50710815113869423182675145 38033111335402067387006359)
                ·
                  refine ⟨57049667003103101080509539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38033111335402067387006359 57049667003103101080509539)
                  ·
                    refine ⟨85574500504654651620764309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57049667003103101080509539 85574500504654651620764309)
                    ·
                      refine ⟨4011304711155686794723327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85574500504654651620764309 4011304711155686794723327)
                      ·
                        rfl

theorem cell23_7811988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_7811988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7811988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7811988 prefixEnd_7811988 := by exact prefixLift 7811988
  have htrace : WordTrace (prefixWord ++ tailWord_7811988) baseStart_7811988 baseEnd_7811988 := by
    simpa [prefixWord, tailWord_7811988, baseEnd_7811988] using wordTrace_append hprefix tailTrace_7811988
  have hstable : (prefixWord ++ tailWord_7811988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7811988).length < 2 ^ (prefixWord ++ tailWord_7811988).sum := by decide
  have hdescent : baseEnd_7811988 < baseStart_7811988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7811988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812025 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 4, 1, 3]
def baseStart_7812025 : Nat := 118140960795 + 7812025 * 2 ^ 59
def prefixEnd_7812025 : Nat := 4983230072969 + 3 ^ 40 * 7812025 * 2
def baseEnd_7812025 : Nat := 4011323709939903149960657

theorem tailTrace_7812025 : CollatzResearch.WordTrace tailWord_7812025 prefixEnd_7812025 4011323709939903149960657 := by
  unfold tailWord_7812025
  simp only [CollatzResearch.WordTrace]
  refine ⟨284927959523375087495005529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189951973015583391663337019 284927959523375087495005529)
  ·
    refine ⟨213695969642531315621254147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284927959523375087495005529 213695969642531315621254147)
    ·
      refine ⟨320543954463796973431881221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213695969642531315621254147 320543954463796973431881221)
      ·
        refine ⟨60101991461961932518477729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320543954463796973431881221 60101991461961932518477729)
        ·
          refine ⟨45076493596471449388858297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60101991461961932518477729 45076493596471449388858297)
          ·
            refine ⟨33807370197353587041643723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45076493596471449388858297 33807370197353587041643723)
            ·
              refine ⟨50711055296030380562465585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33807370197353587041643723 50711055296030380562465585)
              ·
                refine ⟨38033291472022785421849189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50711055296030380562465585 38033291472022785421849189)
                ·
                  refine ⟨7131242151004272266596723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38033291472022785421849189 7131242151004272266596723)
                  ·
                    refine ⟨10696863226506408399895085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7131242151004272266596723 10696863226506408399895085)
                    ·
                      refine ⟨4011323709939903149960657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10696863226506408399895085 4011323709939903149960657)
                      ·
                        rfl

theorem cell23_7812025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_7812025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812025 prefixEnd_7812025 := by exact prefixLift 7812025
  have htrace : WordTrace (prefixWord ++ tailWord_7812025) baseStart_7812025 baseEnd_7812025 := by
    simpa [prefixWord, tailWord_7812025, baseEnd_7812025] using wordTrace_append hprefix tailTrace_7812025
  have hstable : (prefixWord ++ tailWord_7812025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812025).length < 2 ^ (prefixWord ++ tailWord_7812025).sum := by decide
  have hdescent : baseEnd_7812025 < baseStart_7812025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812065 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 1, 4, 2]
def baseStart_7812065 : Nat := 118140960795 + 7812065 * 2 ^ 59
def prefixEnd_7812065 : Nat := 4983230072969 + 3 ^ 40 * 7812065 * 2
def baseEnd_7812065 : Nat := 4011344249166082993460473

theorem tailTrace_7812065 : CollatzResearch.WordTrace tailWord_7812065 prefixEnd_7812065 4011344249166082993460473 := by
  unfold tailWord_7812065
  simp only [CollatzResearch.WordTrace]
  refine ⟨284929418443230174326461649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189952945628820116217641099 284929418443230174326461649)
  ·
    refine ⟨213697063832422630744846237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284929418443230174326461649 213697063832422630744846237)
    ·
      refine ⟨80136398937158486529317339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213697063832422630744846237 80136398937158486529317339)
      ·
        refine ⟨120204598405737729793976009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80136398937158486529317339 120204598405737729793976009)
        ·
          refine ⟨90153448804303297345482007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120204598405737729793976009 90153448804303297345482007)
          ·
            refine ⟨135230173206454946018223011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90153448804303297345482007 135230173206454946018223011)
            ·
              refine ⟨202845259809682419027334517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135230173206454946018223011 202845259809682419027334517)
              ·
                refine ⟨19016743107157726783812611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202845259809682419027334517 19016743107157726783812611)
                ·
                  refine ⟨28525114660736590175718917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19016743107157726783812611 28525114660736590175718917)
                  ·
                    refine ⟨5348458998888110657947297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28525114660736590175718917 5348458998888110657947297)
                    ·
                      refine ⟨4011344249166082993460473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348458998888110657947297 4011344249166082993460473)
                      ·
                        rfl

theorem cell23_7812065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_7812065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812065 prefixEnd_7812065 := by exact prefixLift 7812065
  have htrace : WordTrace (prefixWord ++ tailWord_7812065) baseStart_7812065 baseEnd_7812065 := by
    simpa [prefixWord, tailWord_7812065, baseEnd_7812065] using wordTrace_append hprefix tailTrace_7812065
  have hstable : (prefixWord ++ tailWord_7812065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812065).length < 2 ^ (prefixWord ++ tailWord_7812065).sum := by decide
  have hdescent : baseEnd_7812065 < baseStart_7812065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812068 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_7812068 : Nat := 118140960795 + 7812068 * 2 ^ 59
def prefixEnd_7812068 : Nat := 4983230072969 + 3 ^ 40 * 7812068 * 2
def baseEnd_7812068 : Nat := 4011345789608046481722959

theorem tailTrace_7812068 : CollatzResearch.WordTrace tailWord_7812068 prefixEnd_7812068 4011345789608046481722959 := by
  unfold tailWord_7812068
  simp only [CollatzResearch.WordTrace]
  refine ⟨142464763931109652919410429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189953018574812870559213905 142464763931109652919410429)
  ·
    refine ⟨53424286474166119844778911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142464763931109652919410429 53424286474166119844778911)
    ·
      refine ⟨80136429711249179767168367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53424286474166119844778911 80136429711249179767168367)
      ·
        refine ⟨120204644566873769650752551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80136429711249179767168367 120204644566873769650752551)
        ·
          refine ⟨180306966850310654476128827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120204644566873769650752551 180306966850310654476128827)
          ·
            refine ⟨270460450275465981714193241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180306966850310654476128827 270460450275465981714193241)
            ·
              refine ⟨202845337706599486285644931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270460450275465981714193241 202845337706599486285644931)
              ·
                refine ⟨304268006559899229428467397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202845337706599486285644931 304268006559899229428467397)
                ·
                  refine ⟨57050251229981105517837637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304268006559899229428467397 57050251229981105517837637)
                  ·
                    refine ⟨10696922105621457284594557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57050251229981105517837637 10696922105621457284594557)
                    ·
                      refine ⟨4011345789608046481722959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10696922105621457284594557 4011345789608046481722959)
                      ·
                        rfl

theorem cell23_7812068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_7812068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812068 prefixEnd_7812068 := by exact prefixLift 7812068
  have htrace : WordTrace (prefixWord ++ tailWord_7812068) baseStart_7812068 baseEnd_7812068 := by
    simpa [prefixWord, tailWord_7812068, baseEnd_7812068] using wordTrace_append hprefix tailTrace_7812068
  have hstable : (prefixWord ++ tailWord_7812068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812068).length < 2 ^ (prefixWord ++ tailWord_7812068).sum := by decide
  have hdescent : baseEnd_7812068 < baseStart_7812068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812069 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 3, 3, 2]
def baseStart_7812069 : Nat := 118140960795 + 7812069 * 2 ^ 59
def prefixEnd_7812069 : Nat := 4983230072969 + 3 ^ 40 * 7812069 * 2
def baseEnd_7812069 : Nat := 4011346303088700977810455

theorem tailTrace_7812069 : CollatzResearch.WordTrace tailWord_7812069 prefixEnd_7812069 4011346303088700977810455 := by
  unfold tailWord_7812069
  simp only [CollatzResearch.WordTrace]
  refine ⟨284929564335215683009607261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189953042890143788673071507 284929564335215683009607261)
  ·
    refine ⟨106848586625705881128602723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284929564335215683009607261 106848586625705881128602723)
    ·
      refine ⟨160272879938558821692904085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106848586625705881128602723 160272879938558821692904085)
      ·
        refine ⟨7512791247119944766854879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160272879938558821692904085 7512791247119944766854879)
        ·
          refine ⟨11269186870679917150282319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7512791247119944766854879 11269186870679917150282319)
          ·
            refine ⟨16903780306019875725423479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11269186870679917150282319 16903780306019875725423479)
            ·
              refine ⟨25355670459029813588135219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16903780306019875725423479 25355670459029813588135219)
              ·
                refine ⟨38033505688544720382202829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25355670459029813588135219 38033505688544720382202829)
                ·
                  refine ⟨14262564633204270143326061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38033505688544720382202829 14262564633204270143326061)
                  ·
                    refine ⟨5348461737451601303747273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14262564633204270143326061 5348461737451601303747273)
                    ·
                      refine ⟨4011346303088700977810455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348461737451601303747273 4011346303088700977810455)
                      ·
                        rfl

theorem cell23_7812069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_7812069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812069 prefixEnd_7812069 := by exact prefixLift 7812069
  have htrace : WordTrace (prefixWord ++ tailWord_7812069) baseStart_7812069 baseEnd_7812069 := by
    simpa [prefixWord, tailWord_7812069, baseEnd_7812069] using wordTrace_append hprefix tailTrace_7812069
  have hstable : (prefixWord ++ tailWord_7812069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812069).length < 2 ^ (prefixWord ++ tailWord_7812069).sum := by decide
  have hdescent : baseEnd_7812069 < baseStart_7812069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812086 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_7812086 : Nat := 118140960795 + 7812086 * 2 ^ 59
def prefixEnd_7812086 : Nat := 4983230072969 + 3 ^ 40 * 7812086 * 2
def baseEnd_7812086 : Nat := 4011355032259827411297877

theorem tailTrace_7812086 : CollatzResearch.WordTrace tailWord_7812086 prefixEnd_7812086 4011355032259827411297877 := by
  unfold tailWord_7812086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808136523509630932061007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189953456250769396608650741 17808136523509630932061007)
  ·
    refine ⟨26712204785264446398091511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17808136523509630932061007 26712204785264446398091511)
    ·
      refine ⟨40068307177896669597137267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26712204785264446398091511 40068307177896669597137267)
      ·
        refine ⟨60102460766845004395705901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40068307177896669597137267 60102460766845004395705901)
        ·
          refine ⟨22538422787566876648389713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60102460766845004395705901 22538422787566876648389713)
          ·
            refine ⟨16903817090675157486292285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22538422787566876648389713 16903817090675157486292285)
            ·
              refine ⟨6338931409003184057359607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16903817090675157486292285 6338931409003184057359607)
              ·
                refine ⟨9508397113504776086039411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6338931409003184057359607 9508397113504776086039411)
                ·
                  refine ⟨14262595670257164129059117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9508397113504776086039411 14262595670257164129059117)
                  ·
                    refine ⟨5348473376346436548397169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14262595670257164129059117 5348473376346436548397169)
                    ·
                      refine ⟨4011355032259827411297877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348473376346436548397169 4011355032259827411297877)
                      ·
                        rfl

theorem cell23_7812086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_7812086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812086 prefixEnd_7812086 := by exact prefixLift 7812086
  have htrace : WordTrace (prefixWord ++ tailWord_7812086) baseStart_7812086 baseEnd_7812086 := by
    simpa [prefixWord, tailWord_7812086, baseEnd_7812086] using wordTrace_append hprefix tailTrace_7812086
  have hstable : (prefixWord ++ tailWord_7812086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812086).length < 2 ^ (prefixWord ++ tailWord_7812086).sum := by decide
  have hdescent : baseEnd_7812086 < baseStart_7812086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812165 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_7812165 : Nat := 118140960795 + 7812165 * 2 ^ 59
def prefixEnd_7812165 : Nat := 4983230072969 + 3 ^ 40 * 7812165 * 2
def baseEnd_7812165 : Nat := 1337131865743844200736671

theorem tailTrace_7812165 : CollatzResearch.WordTrace tailWord_7812165 prefixEnd_7812165 1337131865743844200736671 := by
  unfold tailWord_7812165
  simp only [CollatzResearch.WordTrace]
  refine ⟨284933065742867891405101949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189955377161911927603401299 284933065742867891405101949)
  ·
    refine ⟨106849899653575459276913231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284933065742867891405101949 106849899653575459276913231)
    ·
      refine ⟨160274849480363188915369847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106849899653575459276913231 160274849480363188915369847)
      ·
        refine ⟨240412274220544783373054771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160274849480363188915369847 240412274220544783373054771)
        ·
          refine ⟨360618411330817175059582157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240412274220544783373054771 360618411330817175059582157)
          ·
            refine ⟨135231904249056440647343309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360618411330817175059582157 135231904249056440647343309)
            ·
              refine ⟨50711964093396165242753741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135231904249056440647343309 50711964093396165242753741)
              ·
                refine ⟨19016986535023561966032653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50711964093396165242753741 19016986535023561966032653)
                ·
                  refine ⟨7131369950633835737262245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19016986535023561966032653 7131369950633835737262245)
                  ·
                    refine ⟨1337131865743844200736671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7131369950633835737262245 1337131865743844200736671)
                    ·
                      rfl

theorem cell23_7812165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_7812165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812165 prefixEnd_7812165 := by exact prefixLift 7812165
  have htrace : WordTrace (prefixWord ++ tailWord_7812165) baseStart_7812165 baseEnd_7812165 := by
    simpa [prefixWord, tailWord_7812165, baseEnd_7812165] using wordTrace_append hprefix tailTrace_7812165
  have hstable : (prefixWord ++ tailWord_7812165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812165).length < 2 ^ (prefixWord ++ tailWord_7812165).sum := by decide
  have hdescent : baseEnd_7812165 < baseStart_7812165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812168 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_7812168 : Nat := 118140960795 + 7812168 * 2 ^ 59
def prefixEnd_7812168 : Nat := 4983230072969 + 3 ^ 40 * 7812168 * 2
def baseEnd_7812168 : Nat := 4011397137673496090472499

theorem tailTrace_7812168 : CollatzResearch.WordTrace tailWord_7812168 prefixEnd_7812168 4011397137673496090472499 := by
  unfold tailWord_7812168
  simp only [CollatzResearch.WordTrace]
  refine ⟨142466587580928511458730579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189955450107904681944974105 142466587580928511458730579)
  ·
    refine ⟨213699881371392767188095869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142466587580928511458730579 213699881371392767188095869)
    ·
      refine ⟨80137455514272287695535951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213699881371392767188095869 80137455514272287695535951)
      ·
        refine ⟨120206183271408431543303927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80137455514272287695535951 120206183271408431543303927)
        ·
          refine ⟨180309274907112647314955891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120206183271408431543303927 180309274907112647314955891)
          ·
            refine ⟨270463912360668970972433837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180309274907112647314955891 270463912360668970972433837)
            ·
              refine ⟨101423967135250864114662689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270463912360668970972433837 101423967135250864114662689)
              ·
                refine ⟨76067975351438148085997017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101423967135250864114662689 76067975351438148085997017)
                ·
                  refine ⟨57050981513578611064497763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76067975351438148085997017 57050981513578611064497763)
                  ·
                    refine ⟨85576472270367916596746645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57050981513578611064497763 85576472270367916596746645)
                    ·
                      refine ⟨4011397137673496090472499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85576472270367916596746645 4011397137673496090472499)
                      ·
                        rfl

theorem cell23_7812168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_7812168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812168 prefixEnd_7812168 := by exact prefixLift 7812168
  have htrace : WordTrace (prefixWord ++ tailWord_7812168) baseStart_7812168 baseEnd_7812168 := by
    simpa [prefixWord, tailWord_7812168, baseEnd_7812168] using wordTrace_append hprefix tailTrace_7812168
  have hstable : (prefixWord ++ tailWord_7812168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812168).length < 2 ^ (prefixWord ++ tailWord_7812168).sum := by decide
  have hdescent : baseEnd_7812168 < baseStart_7812168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812199 : List Nat := [1, 1, 5, 1, 1, 3, 3, 3, 1, 4]
def baseStart_7812199 : Nat := 118140960795 + 7812199 * 2 ^ 59
def prefixEnd_7812199 : Nat := 4983230072969 + 3 ^ 40 * 7812199 * 2
def baseEnd_7812199 : Nat := 1337137685191261823061619

theorem tailTrace_7812199 : CollatzResearch.WordTrace tailWord_7812199 prefixEnd_7812199 1337137685191261823061619 := by
  unfold tailWord_7812199
  simp only [CollatzResearch.WordTrace]
  refine ⟨284934305824744715211839651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189956203883163143474559767 284934305824744715211839651)
  ·
    refine ⟨427401458737117072817759477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284934305824744715211839651 427401458737117072817759477)
    ·
      refine ⟨40068886756604725576664951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427401458737117072817759477 40068886756604725576664951)
      ·
        refine ⟨60103330134907088364997427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40068886756604725576664951 60103330134907088364997427)
        ·
          refine ⟨90154995202360632547496141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60103330134907088364997427 90154995202360632547496141)
          ·
            refine ⟨33808123200885237205311053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90154995202360632547496141 33808123200885237205311053)
            ·
              refine ⟨12678046200331963951991645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33808123200885237205311053 12678046200331963951991645)
              ·
                refine ⟨4754267325124486481996867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12678046200331963951991645 4754267325124486481996867)
                ·
                  refine ⟨7131400987686729722995301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754267325124486481996867 7131400987686729722995301)
                  ·
                    refine ⟨1337137685191261823061619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7131400987686729722995301 1337137685191261823061619)
                    ·
                      rfl

theorem cell23_7812199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_7812199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812199 prefixEnd_7812199 := by exact prefixLift 7812199
  have htrace : WordTrace (prefixWord ++ tailWord_7812199) baseStart_7812199 baseEnd_7812199 := by
    simpa [prefixWord, tailWord_7812199, baseEnd_7812199] using wordTrace_append hprefix tailTrace_7812199
  have hstable : (prefixWord ++ tailWord_7812199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812199).length < 2 ^ (prefixWord ++ tailWord_7812199).sum := by decide
  have hdescent : baseEnd_7812199 < baseStart_7812199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812229 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 6]
def baseStart_7812229 : Nat := 118140960795 + 7812229 * 2 ^ 59
def prefixEnd_7812229 : Nat := 4983230072969 + 3 ^ 40 * 7812229 * 2
def baseEnd_7812229 : Nat := 445714273332602261312191

theorem tailTrace_7812229 : CollatzResearch.WordTrace tailWord_7812229 prefixEnd_7812229 445714273332602261312191 := by
  unfold tailWord_7812229
  simp only [CollatzResearch.WordTrace]
  refine ⟨284935400014636030335431741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189956933343090686890287827 284935400014636030335431741)
  ·
    refine ⟨106850775005488511375786903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284935400014636030335431741 106850775005488511375786903)
    ·
      refine ⟨160276162508232767063680355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106850775005488511375786903 160276162508232767063680355)
      ·
        refine ⟨240414243762349150595520533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160276162508232767063680355 240414243762349150595520533)
        ·
          refine ⟨11269417676360116434165025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 240414243762349150595520533 11269417676360116434165025)
          ·
            refine ⟨8452063257270087325623769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11269417676360116434165025 8452063257270087325623769)
            ·
              refine ⟨6339047442952565494217827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8452063257270087325623769 6339047442952565494217827)
              ·
                refine ⟨9508571164428848241326741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339047442952565494217827 9508571164428848241326741)
                ·
                  refine ⟨445714273332602261312191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9508571164428848241326741 445714273332602261312191)
                  ·
                    rfl

theorem cell23_7812229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_7812229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812229 prefixEnd_7812229 := by exact prefixLift 7812229
  have htrace : WordTrace (prefixWord ++ tailWord_7812229) baseStart_7812229 baseEnd_7812229 := by
    simpa [prefixWord, tailWord_7812229, baseEnd_7812229] using wordTrace_append hprefix tailTrace_7812229
  have hstable : (prefixWord ++ tailWord_7812229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812229).length < 2 ^ (prefixWord ++ tailWord_7812229).sum := by decide
  have hdescent : baseEnd_7812229 < baseStart_7812229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812242 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_7812242 : Nat := 118140960795 + 7812242 * 2 ^ 59
def prefixEnd_7812242 : Nat := 4983230072969 + 3 ^ 40 * 7812242 * 2
def baseEnd_7812242 : Nat := 1337145045080642933649053

theorem tailTrace_7812242 : CollatzResearch.WordTrace tailWord_7812242 prefixEnd_7812242 1337145045080642933649053 := by
  unfold tailWord_7812242
  simp only [CollatzResearch.WordTrace]
  refine ⟨71233968540897233388913745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189957249442392622370436653 71233968540897233388913745)
  ·
    refine ⟨53425476405672925041685309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71233968540897233388913745 53425476405672925041685309)
    ·
      refine ⟨20034553652127346890631991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53425476405672925041685309 20034553652127346890631991)
      ·
        refine ⟨30051830478191020335947987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20034553652127346890631991 30051830478191020335947987)
        ·
          refine ⟨45077745717286530503921981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30051830478191020335947987 45077745717286530503921981)
          ·
            refine ⟨16904154643982448938970743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45077745717286530503921981 16904154643982448938970743)
            ·
              refine ⟨25356231965973673408456115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16904154643982448938970743 25356231965973673408456115)
              ·
                refine ⟨38034347948960510112684173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25356231965973673408456115 38034347948960510112684173)
                ·
                  refine ⟨14262880480860191292256565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38034347948960510112684173 14262880480860191292256565)
                  ·
                    refine ⟨1337145045080642933649053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14262880480860191292256565 1337145045080642933649053)
                    ·
                      rfl

theorem cell23_7812242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_7812242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812242 prefixEnd_7812242 := by exact prefixLift 7812242
  have htrace : WordTrace (prefixWord ++ tailWord_7812242) baseStart_7812242 baseEnd_7812242 := by
    simpa [prefixWord, tailWord_7812242, baseEnd_7812242] using wordTrace_append hprefix tailTrace_7812242
  have hstable : (prefixWord ++ tailWord_7812242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812242).length < 2 ^ (prefixWord ++ tailWord_7812242).sum := by decide
  have hdescent : baseEnd_7812242 < baseStart_7812242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812266 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7812266 : Nat := 118140960795 + 7812266 * 2 ^ 59
def prefixEnd_7812266 : Nat := 4983230072969 + 3 ^ 40 * 7812266 * 2
def baseEnd_7812266 : Nat := 4011447458777636707047049

theorem tailTrace_7812266 : CollatzResearch.WordTrace tailWord_7812266 prefixEnd_7812266 4011447458777636707047049 := by
  unfold tailWord_7812266
  simp only [CollatzResearch.WordTrace]
  refine ⟨71234187378875496413632163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189957833010334657103019101 71234187378875496413632163)
  ·
    refine ⟨106851281068313244620448245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71234187378875496413632163 106851281068313244620448245)
    ·
      refine ⟨10017307600154366683167023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106851281068313244620448245 10017307600154366683167023)
      ·
        refine ⟨15025961400231550024750535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017307600154366683167023 15025961400231550024750535)
        ·
          refine ⟨22538942100347325037125803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15025961400231550024750535 22538942100347325037125803)
          ·
            refine ⟨33808413150520987555688705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22538942100347325037125803 33808413150520987555688705)
            ·
              refine ⟨25356309862890740666766529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33808413150520987555688705 25356309862890740666766529)
              ·
                refine ⟨19017232397168055500074897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25356309862890740666766529 19017232397168055500074897)
                ·
                  refine ⟨14262924297876041625056173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19017232397168055500074897 14262924297876041625056173)
                  ·
                    refine ⟨5348596611703515609396065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14262924297876041625056173 5348596611703515609396065)
                    ·
                      refine ⟨4011447458777636707047049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348596611703515609396065 4011447458777636707047049)
                      ·
                        rfl

theorem cell23_7812266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7812266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812266 prefixEnd_7812266 := by exact prefixLift 7812266
  have htrace : WordTrace (prefixWord ++ tailWord_7812266) baseStart_7812266 baseEnd_7812266 := by
    simpa [prefixWord, tailWord_7812266, baseEnd_7812266] using wordTrace_append hprefix tailTrace_7812266
  have hstable : (prefixWord ++ tailWord_7812266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812266).length < 2 ^ (prefixWord ++ tailWord_7812266).sum := by decide
  have hdescent : baseEnd_7812266 < baseStart_7812266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812273 : List Nat := [1, 2, 2, 5, 1, 1, 4, 2, 1, 1, 3]
def baseStart_7812273 : Nat := 118140960795 + 7812273 * 2 ^ 59
def prefixEnd_7812273 : Nat := 4983230072969 + 3 ^ 40 * 7812273 * 2
def baseEnd_7812273 : Nat := 4011451053142218179659517

theorem tailTrace_7812273 : CollatzResearch.WordTrace tailWord_7812273 prefixEnd_7812273 4011451053142218179659517 := by
  unfold tailWord_7812273
  simp only [CollatzResearch.WordTrace]
  refine ⟨284937004826476625850033473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189958003217651083900022315 284937004826476625850033473)
  ·
    refine ⟨213702753619857469387525105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284937004826476625850033473 213702753619857469387525105)
    ·
      refine ⟨160277065214893102040643829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213702753619857469387525105 160277065214893102040643829)
      ·
        refine ⟨15025974863896228316310359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160277065214893102040643829 15025974863896228316310359)
        ·
          refine ⟨22538962295844342474465539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15025974863896228316310359 22538962295844342474465539)
          ·
            refine ⟨33808443443766513711698309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22538962295844342474465539 33808443443766513711698309)
            ·
              refine ⟨6339083145706221320943433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33808443443766513711698309 6339083145706221320943433)
              ·
                refine ⟨4754312359279665990707575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6339083145706221320943433 4754312359279665990707575)
                ·
                  refine ⟨7131468538919498986061363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754312359279665990707575 7131468538919498986061363)
                  ·
                    refine ⟨10697202808379248479092045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7131468538919498986061363 10697202808379248479092045)
                    ·
                      refine ⟨4011451053142218179659517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10697202808379248479092045 4011451053142218179659517)
                      ·
                        rfl

theorem cell23_7812273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_7812273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812273 prefixEnd_7812273 := by exact prefixLift 7812273
  have htrace : WordTrace (prefixWord ++ tailWord_7812273) baseStart_7812273 baseEnd_7812273 := by
    simpa [prefixWord, tailWord_7812273, baseEnd_7812273] using wordTrace_append hprefix tailTrace_7812273
  have hstable : (prefixWord ++ tailWord_7812273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812273).length < 2 ^ (prefixWord ++ tailWord_7812273).sum := by decide
  have hdescent : baseEnd_7812273 < baseStart_7812273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812279 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 3, 2, 2]
def baseStart_7812279 : Nat := 118140960795 + 7812279 * 2 ^ 59
def prefixEnd_7812279 : Nat := 4983230072969 + 3 ^ 40 * 7812279 * 2
def baseEnd_7812279 : Nat := 4011454134026145156184489

theorem tailTrace_7812279 : CollatzResearch.WordTrace tailWord_7812279 prefixEnd_7812279 4011454134026145156184489 := by
  unfold tailWord_7812279
  simp only [CollatzResearch.WordTrace]
  refine ⟨284937223664454888874751891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189958149109636592583167927 284937223664454888874751891)
  ·
    refine ⟨427405835496682333312127837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284937223664454888874751891 427405835496682333312127837)
    ·
      refine ⟨160277188311255874992047939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427405835496682333312127837 160277188311255874992047939)
      ·
        refine ⟨240415782466883812488071909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160277188311255874992047939 240415782466883812488071909)
        ·
          refine ⟨45077959212540714841513483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240415782466883812488071909 45077959212540714841513483)
          ·
            refine ⟨67616938818811072262270225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45077959212540714841513483 67616938818811072262270225)
            ·
              refine ⟨50712704114108304196702669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67616938818811072262270225 50712704114108304196702669)
              ·
                refine ⟨19017264042790614073763501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50712704114108304196702669 19017264042790614073763501)
                ·
                  refine ⟨7131474016046480277661313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19017264042790614073763501 7131474016046480277661313)
                  ·
                    refine ⟨5348605512034860208245985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7131474016046480277661313 5348605512034860208245985)
                    ·
                      refine ⟨4011454134026145156184489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348605512034860208245985 4011454134026145156184489)
                      ·
                        rfl

theorem cell23_7812279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_7812279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812279 prefixEnd_7812279 := by exact prefixLift 7812279
  have htrace : WordTrace (prefixWord ++ tailWord_7812279) baseStart_7812279 baseEnd_7812279 := by
    simpa [prefixWord, tailWord_7812279, baseEnd_7812279] using wordTrace_append hprefix tailTrace_7812279
  have hstable : (prefixWord ++ tailWord_7812279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812279).length < 2 ^ (prefixWord ++ tailWord_7812279).sum := by decide
  have hdescent : baseEnd_7812279 < baseStart_7812279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812285 : List Nat := [1, 4, 1, 2, 1, 1, 5, 8]
def baseStart_7812285 : Nat := 118140960795 + 7812285 * 2 ^ 59
def prefixEnd_7812285 : Nat := 4983230072969 + 3 ^ 40 * 7812285 * 2
def baseEnd_7812285 : Nat := 148572489441113782692943

theorem tailTrace_7812285 : CollatzResearch.WordTrace tailWord_7812285 prefixEnd_7812285 148572489441113782692943 := by
  unfold tailWord_7812285
  simp only [CollatzResearch.WordTrace]
  refine ⟨284937442502433151899470309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189958295001622101266313539 284937442502433151899470309)
  ·
    refine ⟨53425770469206215981150683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284937442502433151899470309 53425770469206215981150683)
    ·
      refine ⟨80138655703809323971726025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53425770469206215981150683 80138655703809323971726025)
      ·
        refine ⟨60103991777856992978794519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80138655703809323971726025 60103991777856992978794519)
        ·
          refine ⟨90155987666785489468191779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60103991777856992978794519 90155987666785489468191779)
          ·
            refine ⟨135233981500178234202287669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90155987666785489468191779 135233981500178234202287669)
            ·
              refine ⟨12678185765641709456464469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135233981500178234202287669 12678185765641709456464469)
              ·
                refine ⟨148572489441113782692943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12678185765641709456464469 148572489441113782692943)
                ·
                  rfl

theorem cell23_7812285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 8].length) (baseStart_7812285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812285 prefixEnd_7812285 := by exact prefixLift 7812285
  have htrace : WordTrace (prefixWord ++ tailWord_7812285) baseStart_7812285 baseEnd_7812285 := by
    simpa [prefixWord, tailWord_7812285, baseEnd_7812285] using wordTrace_append hprefix tailTrace_7812285
  have hstable : (prefixWord ++ tailWord_7812285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812285).length < 2 ^ (prefixWord ++ tailWord_7812285).sum := by decide
  have hdescent : baseEnd_7812285 < baseStart_7812285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812289 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 1, 6]
def baseStart_7812289 : Nat := 118140960795 + 7812289 * 2 ^ 59
def prefixEnd_7812289 : Nat := 4983230072969 + 3 ^ 40 * 7812289 * 2
def baseEnd_7812289 : Nat := 1337153089610896705686481

theorem tailTrace_7812289 : CollatzResearch.WordTrace tailWord_7812289 prefixEnd_7812289 1337153089610896705686481 := by
  unfold tailWord_7812289
  simp only [CollatzResearch.WordTrace]
  refine ⟨284937588394418660582615921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189958392262945773721743947 284937588394418660582615921)
  ·
    refine ⟨213703191295813995436961941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284937588394418660582615921 213703191295813995436961941)
    ·
      refine ⟨10017337091991281036107591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 213703191295813995436961941 10017337091991281036107591)
      ·
        refine ⟨15026005637986921554161387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017337091991281036107591 15026005637986921554161387)
        ·
          refine ⟨22539008456980382331242081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15026005637986921554161387 22539008456980382331242081)
          ·
            refine ⟨16904256342735286748431561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22539008456980382331242081 16904256342735286748431561)
            ·
              refine ⟨12678192257051465061323671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16904256342735286748431561 12678192257051465061323671)
              ·
                refine ⟨19017288385577197591985507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12678192257051465061323671 19017288385577197591985507)
                ·
                  refine ⟨28525932578365796387978261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19017288385577197591985507 28525932578365796387978261)
                  ·
                    refine ⟨1337153089610896705686481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28525932578365796387978261 1337153089610896705686481)
                    ·
                      rfl

theorem cell23_7812289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_7812289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812289 prefixEnd_7812289 := by exact prefixLift 7812289
  have htrace : WordTrace (prefixWord ++ tailWord_7812289) baseStart_7812289 baseEnd_7812289 := by
    simpa [prefixWord, tailWord_7812289, baseEnd_7812289] using wordTrace_append hprefix tailTrace_7812289
  have hstable : (prefixWord ++ tailWord_7812289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812289).length < 2 ^ (prefixWord ++ tailWord_7812289).sum := by decide
  have hdescent : baseEnd_7812289 < baseStart_7812289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812310 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_7812310 : Nat := 118140960795 + 7812310 * 2 ^ 59
def prefixEnd_7812310 : Nat := 4983230072969 + 3 ^ 40 * 7812310 * 2
def baseEnd_7812310 : Nat := 1337156683975478178298949

theorem tailTrace_7812310 : CollatzResearch.WordTrace tailWord_7812310 prefixEnd_7812310 1337156683975478178298949 := by
  unfold tailWord_7812310
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808647145458911323070649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189958902884895054112753589 17808647145458911323070649)
  ·
    refine ⟨13356485359094183492302987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17808647145458911323070649 13356485359094183492302987)
    ·
      refine ⟨20034728038641275238454481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13356485359094183492302987 20034728038641275238454481)
      ·
        refine ⟨15026046028980956428840861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20034728038641275238454481 15026046028980956428840861)
        ·
          refine ⟨5634767260867858660815323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15026046028980956428840861 5634767260867858660815323)
          ·
            refine ⟨8452150891301787991222985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634767260867858660815323 8452150891301787991222985)
            ·
              refine ⟨6339113168476340993417239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8452150891301787991222985 6339113168476340993417239)
              ·
                refine ⟨9508669752714511490125859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339113168476340993417239 9508669752714511490125859)
                ·
                  refine ⟨14263004629071767235188789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9508669752714511490125859 14263004629071767235188789)
                  ·
                    refine ⟨1337156683975478178298949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14263004629071767235188789 1337156683975478178298949)
                    ·
                      rfl

theorem cell23_7812310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_7812310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812310 prefixEnd_7812310 := by exact prefixLift 7812310
  have htrace : WordTrace (prefixWord ++ tailWord_7812310) baseStart_7812310 baseEnd_7812310 := by
    simpa [prefixWord, tailWord_7812310, baseEnd_7812310] using wordTrace_append hprefix tailTrace_7812310
  have hstable : (prefixWord ++ tailWord_7812310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812310).length < 2 ^ (prefixWord ++ tailWord_7812310).sum := by decide
  have hdescent : baseEnd_7812310 < baseStart_7812310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812340 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7812340 : Nat := 118140960795 + 7812340 * 2 ^ 59
def prefixEnd_7812340 : Nat := 4983230072969 + 3 ^ 40 * 7812340 * 2
def baseEnd_7812340 : Nat := 1337161818782023139173903

theorem tailTrace_7812340 : CollatzResearch.WordTrace tailWord_7812340 prefixEnd_7812340 1337161818782023139173903 := by
  unfold tailWord_7812340
  simp only [CollatzResearch.WordTrace]
  refine ⟨142469724258616948146361237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189959632344822597528481649 142469724258616948146361237)
  ·
    refine ⟨6678268324622669444360683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142469724258616948146361237 6678268324622669444360683)
    ·
      refine ⟨10017402486934004166541025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6678268324622669444360683 10017402486934004166541025)
      ·
        refine ⟨7513051865200503124905769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10017402486934004166541025 7513051865200503124905769)
        ·
          refine ⟨5634788898900377343679327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7513051865200503124905769 5634788898900377343679327)
          ·
            refine ⟨8452183348350566015518991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634788898900377343679327 8452183348350566015518991)
            ·
              refine ⟨12678275022525849023278487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452183348350566015518991 12678275022525849023278487)
              ·
                refine ⟨19017412533788773534917731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12678275022525849023278487 19017412533788773534917731)
                ·
                  refine ⟨28526118800683160302376597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19017412533788773534917731 28526118800683160302376597)
                  ·
                    refine ⟨1337161818782023139173903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28526118800683160302376597 1337161818782023139173903)
                    ·
                      rfl

theorem cell23_7812340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7812340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812340 prefixEnd_7812340 := by exact prefixLift 7812340
  have htrace : WordTrace (prefixWord ++ tailWord_7812340) baseStart_7812340 baseEnd_7812340 := by
    simpa [prefixWord, tailWord_7812340, baseEnd_7812340] using wordTrace_append hprefix tailTrace_7812340
  have hstable : (prefixWord ++ tailWord_7812340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812340).length < 2 ^ (prefixWord ++ tailWord_7812340).sum := by decide
  have hdescent : baseEnd_7812340 < baseStart_7812340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
