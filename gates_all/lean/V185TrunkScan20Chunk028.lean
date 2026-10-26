import V185TrunkScan20Chunk027

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_170882 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 3]
def baseStart_170882 : Nat := 118140960795 + 170882 * 2 ^ 59
def prefixEnd_170882 : Nat := 4983230072969 + 3 ^ 40 * 170882 * 2
def baseEnd_170882 : Nat := 77995201068182806301453

theorem tailTrace_170882 : CollatzResearch.WordTrace tailWord_170882 prefixEnd_170882 77995201068182806301453 := by
  unfold tailWord_170882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558144641732793291806725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4155052377954115444817933 1558144641732793291806725)
  ·
    refine ⟨292152120324898742213761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1558144641732793291806725 292152120324898742213761)
    ·
      refine ⟨219114090243674056660321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292152120324898742213761 219114090243674056660321)
      ·
        refine ⟨164335567682755542495241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219114090243674056660321 164335567682755542495241)
        ·
          refine ⟨123251675762066656871431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164335567682755542495241 123251675762066656871431)
          ·
            refine ⟨184877513643099985307147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123251675762066656871431 184877513643099985307147)
            ·
              refine ⟨277316270464649977960721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184877513643099985307147 277316270464649977960721)
              ·
                refine ⟨207987202848487483470541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277316270464649977960721 207987202848487483470541)
                ·
                  refine ⟨77995201068182806301453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207987202848487483470541 77995201068182806301453)
                  ·
                    rfl

theorem cell20_170882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_170882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170882 prefixEnd_170882 := by exact prefixLift 170882
  have htrace : WordTrace (prefixWord ++ tailWord_170882) baseStart_170882 baseEnd_170882 := by
    simpa [prefixWord, tailWord_170882, baseEnd_170882] using wordTrace_append hprefix tailTrace_170882
  have hstable : (prefixWord ++ tailWord_170882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170882).length < 2 ^ (prefixWord ++ tailWord_170882).sum := by decide
  have hdescent : baseEnd_170882 < baseStart_170882 := by decide
  rcases family_descends (prefixWord ++ tailWord_170882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170890 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_170890 : Nat := 118140960795 + 170890 * 2 ^ 59
def prefixEnd_170890 : Nat := 4983230072969 + 3 ^ 40 * 170890 * 2
def baseEnd_170890 : Nat := 77998852486170334034753

theorem tailTrace_170890 : CollatzResearch.WordTrace tailWord_170890 prefixEnd_170890 77998852486170334034753 := by
  unfold tailWord_170890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558217587725547633379531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4155246900601460355678749 1558217587725547633379531)
  ·
    refine ⟨2337326381588321450069297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1558217587725547633379531 2337326381588321450069297)
    ·
      refine ⟨1752994786191241087551973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2337326381588321450069297 1752994786191241087551973)
      ·
        refine ⟨328686522410857703915995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1752994786191241087551973 328686522410857703915995)
        ·
          refine ⟨493029783616286555873993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328686522410857703915995 493029783616286555873993)
          ·
            refine ⟨369772337712214916905495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493029783616286555873993 369772337712214916905495)
            ·
              refine ⟨554658506568322375358243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369772337712214916905495 554658506568322375358243)
              ·
                refine ⟨831987759852483563037365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554658506568322375358243 831987759852483563037365)
                ·
                  refine ⟨77998852486170334034753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 831987759852483563037365 77998852486170334034753)
                  ·
                    rfl

theorem cell20_170890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_170890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170890 prefixEnd_170890 := by exact prefixLift 170890
  have htrace : WordTrace (prefixWord ++ tailWord_170890) baseStart_170890 baseEnd_170890 := by
    simpa [prefixWord, tailWord_170890, baseEnd_170890] using wordTrace_append hprefix tailTrace_170890
  have hstable : (prefixWord ++ tailWord_170890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170890).length < 2 ^ (prefixWord ++ tailWord_170890).sum := by decide
  have hdescent : baseEnd_170890 < baseStart_170890 := by decide
  rcases family_descends (prefixWord ++ tailWord_170890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170934 : List Nat := [5, 1, 4, 1, 2, 1, 6]
def baseStart_170934 : Nat := 118140960795 + 170934 * 2 ^ 59
def prefixEnd_170934 : Nat := 4983230072969 + 3 ^ 40 * 170934 * 2
def baseEnd_170934 : Nat := 8668770587233526285323

theorem tailTrace_170934 : CollatzResearch.WordTrace tailWord_170934 prefixEnd_170934 8668770587233526285323 := by
  unfold tailWord_170934
  simp only [CollatzResearch.WordTrace]
  refine ⟨389654697671424128007491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4156316775161857365413237 389654697671424128007491)
  ·
    refine ⟨584482046507136192011237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 389654697671424128007491 584482046507136192011237)
    ·
      refine ⟨109590383720088036002107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 584482046507136192011237 109590383720088036002107)
      ·
        refine ⟨164385575580132054003161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109590383720088036002107 164385575580132054003161)
        ·
          refine ⟨123289181685099040502371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164385575580132054003161 123289181685099040502371)
          ·
            refine ⟨184933772527648560753557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123289181685099040502371 184933772527648560753557)
            ·
              refine ⟨8668770587233526285323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184933772527648560753557 8668770587233526285323)
              ·
                rfl

theorem cell20_170934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 6].length) (baseStart_170934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170934 prefixEnd_170934 := by exact prefixLift 170934
  have htrace : WordTrace (prefixWord ++ tailWord_170934) baseStart_170934 baseEnd_170934 := by
    simpa [prefixWord, tailWord_170934, baseEnd_170934] using wordTrace_append hprefix tailTrace_170934
  have hstable : (prefixWord ++ tailWord_170934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170934).length < 2 ^ (prefixWord ++ tailWord_170934).sum := by decide
  have hdescent : baseEnd_170934 < baseStart_170934 := by decide
  rcases family_descends (prefixWord ++ tailWord_170934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170948 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 4]
def baseStart_170948 : Nat := 118140960795 + 170948 * 2 ^ 59
def prefixEnd_170948 : Nat := 4983230072969 + 3 ^ 40 * 170948 * 2
def baseEnd_170948 : Nat := 78025325266579910101183

theorem tailTrace_170948 : CollatzResearch.WordTrace tailWord_170948 prefixEnd_170948 78025325266579910101183 := by
  unfold tailWord_170948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117492892346033219564749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4156657189794710959419665 3117492892346033219564749)
  ·
    refine ⟨1169059834629762457336781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3117492892346033219564749 1169059834629762457336781)
    ·
      refine ⟨438397437986160921501293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1169059834629762457336781 438397437986160921501293)
      ·
        refine ⟨164399039244810345562985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438397437986160921501293 164399039244810345562985)
        ·
          refine ⟨123299279433607759172239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164399039244810345562985 123299279433607759172239)
          ·
            refine ⟨184948919150411638758359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123299279433607759172239 184948919150411638758359)
            ·
              refine ⟨277423378725617458137539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184948919150411638758359 277423378725617458137539)
              ·
                refine ⟨416135068088426187206309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277423378725617458137539 416135068088426187206309)
                ·
                  refine ⟨78025325266579910101183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 416135068088426187206309 78025325266579910101183)
                  ·
                    rfl

theorem cell20_170948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_170948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170948 prefixEnd_170948 := by exact prefixLift 170948
  have htrace : WordTrace (prefixWord ++ tailWord_170948) baseStart_170948 baseEnd_170948 := by
    simpa [prefixWord, tailWord_170948, baseEnd_170948] using wordTrace_append hprefix tailTrace_170948
  have hstable : (prefixWord ++ tailWord_170948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170948).length < 2 ^ (prefixWord ++ tailWord_170948).sum := by decide
  have hdescent : baseEnd_170948 < baseStart_170948 := by decide
  rcases family_descends (prefixWord ++ tailWord_170948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170952 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 4]
def baseStart_170952 : Nat := 118140960795 + 170952 * 2 ^ 59
def prefixEnd_170952 : Nat := 4983230072969 + 3 ^ 40 * 170952 * 2
def baseEnd_170952 : Nat := 78027150975573673967833

theorem tailTrace_170952 : CollatzResearch.WordTrace tailWord_170952 prefixEnd_170952 78027150975573673967833 := by
  unfold tailWord_170952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117565838338787561137555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4156754451118383414850073 3117565838338787561137555)
  ·
    refine ⟨4676348757508181341706333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3117565838338787561137555 4676348757508181341706333)
    ·
      refine ⟨1753630784065568003139875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4676348757508181341706333 1753630784065568003139875)
      ·
        refine ⟨2630446176098352004709813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1753630784065568003139875 2630446176098352004709813)
        ·
          refine ⟨246604329009220500441545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2630446176098352004709813 246604329009220500441545)
          ·
            refine ⟨184953246756915375331159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246604329009220500441545 184953246756915375331159)
            ·
              refine ⟨277429870135373062996739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184953246756915375331159 277429870135373062996739)
              ·
                refine ⟨416144805203059594495109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277429870135373062996739 416144805203059594495109)
                ·
                  refine ⟨78027150975573673967833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 416144805203059594495109 78027150975573673967833)
                  ·
                    rfl

theorem cell20_170952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_170952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170952 prefixEnd_170952 := by exact prefixLift 170952
  have htrace : WordTrace (prefixWord ++ tailWord_170952) baseStart_170952 baseEnd_170952 := by
    simpa [prefixWord, tailWord_170952, baseEnd_170952] using wordTrace_append hprefix tailTrace_170952
  have hstable : (prefixWord ++ tailWord_170952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170952).length < 2 ^ (prefixWord ++ tailWord_170952).sum := by decide
  have hdescent : baseEnd_170952 < baseStart_170952 := by decide
  rcases family_descends (prefixWord ++ tailWord_170952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170962 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_170962 : Nat := 118140960795 + 170962 * 2 ^ 59
def prefixEnd_170962 : Nat := 4983230072969 + 3 ^ 40 * 170962 * 2
def baseEnd_170962 : Nat := 78031715248058083634459

theorem tailTrace_170962 : CollatzResearch.WordTrace tailWord_170962 prefixEnd_170962 78031715248058083634459 := by
  unfold tailWord_170962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558874101660336707534785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4156997604427564553426093 1558874101660336707534785)
  ·
    refine ⟨1169155576245252530651089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1558874101660336707534785 1169155576245252530651089)
    ·
      refine ⟨876866682183939397988317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1169155576245252530651089 876866682183939397988317)
      ·
        refine ⟨328825005818977274245619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 876866682183939397988317 328825005818977274245619)
        ·
          refine ⟨493237508728465911368429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328825005818977274245619 493237508728465911368429)
          ·
            refine ⟨184964065773174716763161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 493237508728465911368429 184964065773174716763161)
            ·
              refine ⟨138723049329881037572371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184964065773174716763161 138723049329881037572371)
              ·
                refine ⟨208084573994821556358557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138723049329881037572371 208084573994821556358557)
                ·
                  refine ⟨78031715248058083634459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208084573994821556358557 78031715248058083634459)
                  ·
                    rfl

theorem cell20_170962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_170962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170962 prefixEnd_170962 := by exact prefixLift 170962
  have htrace : WordTrace (prefixWord ++ tailWord_170962) baseStart_170962 baseEnd_170962 := by
    simpa [prefixWord, tailWord_170962, baseEnd_170962] using wordTrace_append hprefix tailTrace_170962
  have hstable : (prefixWord ++ tailWord_170962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170962).length < 2 ^ (prefixWord ++ tailWord_170962).sum := by decide
  have hdescent : baseEnd_170962 < baseStart_170962 := by decide
  rcases family_descends (prefixWord ++ tailWord_170962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170996 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 3]
def baseStart_170996 : Nat := 118140960795 + 170996 * 2 ^ 59
def prefixEnd_170996 : Nat := 4983230072969 + 3 ^ 40 * 170996 * 2
def baseEnd_170996 : Nat := 78047233774505076500987

theorem tailTrace_170996 : CollatzResearch.WordTrace tailWord_170996 prefixEnd_170996 78047233774505076500987 := by
  unfold tailWord_170996
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118368244259085318438421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4157824325678780424584561 3118368244259085318438421)
  ·
    refine ⟨146173511449644624301801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3118368244259085318438421 146173511449644624301801)
    ·
      refine ⟨109630133587233468226351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146173511449644624301801 109630133587233468226351)
      ·
        refine ⟨164445200380850202339527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109630133587233468226351 164445200380850202339527)
        ·
          refine ⟨246667800571275303509291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164445200380850202339527 246667800571275303509291)
          ·
            refine ⟨370001700856912955263937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246667800571275303509291 370001700856912955263937)
            ·
              refine ⟨277501275642684716447953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370001700856912955263937 277501275642684716447953)
              ·
                refine ⟨208125956732013537335965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277501275642684716447953 208125956732013537335965)
                ·
                  refine ⟨78047233774505076500987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208125956732013537335965 78047233774505076500987)
                  ·
                    rfl

theorem cell20_170996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_170996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170996 prefixEnd_170996 := by exact prefixLift 170996
  have htrace : WordTrace (prefixWord ++ tailWord_170996) baseStart_170996 baseEnd_170996 := by
    simpa [prefixWord, tailWord_170996, baseEnd_170996] using wordTrace_append hprefix tailTrace_170996
  have hstable : (prefixWord ++ tailWord_170996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170996).length < 2 ^ (prefixWord ++ tailWord_170996).sum := by decide
  have hdescent : baseEnd_170996 < baseStart_170996 := by decide
  rcases family_descends (prefixWord ++ tailWord_170996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170997 : List Nat := [1, 3, 5, 2, 1, 8]
def baseStart_170997 : Nat := 118140960795 + 170997 * 2 ^ 59
def prefixEnd_170997 : Nat := 4983230072969 + 3 ^ 40 * 170997 * 2
def baseEnd_170997 : Nat := 2890655192657537683987

theorem tailTrace_170997 : CollatzResearch.WordTrace tailWord_170997 prefixEnd_170997 2890655192657537683987 := by
  unfold tailWord_170997
  simp only [CollatzResearch.WordTrace]
  refine ⟨6236772961514547807663245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4157848641009698538442163 6236772961514547807663245)
  ·
    refine ⟨2338789860567955427873717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6236772961514547807663245 2338789860567955427873717)
    ·
      refine ⟨219261549428245821363161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2338789860567955427873717 219261549428245821363161)
      ·
        refine ⟨164446162071184366022371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219261549428245821363161 164446162071184366022371)
        ·
          refine ⟨246669243106776549033557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164446162071184366022371 246669243106776549033557)
          ·
            refine ⟨2890655192657537683987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 246669243106776549033557 2890655192657537683987)
            ·
              rfl

theorem cell20_170997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 8].length) (baseStart_170997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170997 prefixEnd_170997 := by exact prefixLift 170997
  have htrace : WordTrace (prefixWord ++ tailWord_170997) baseStart_170997 baseEnd_170997 := by
    simpa [prefixWord, tailWord_170997, baseEnd_170997] using wordTrace_append hprefix tailTrace_170997
  have hstable : (prefixWord ++ tailWord_170997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170997).length < 2 ^ (prefixWord ++ tailWord_170997).sum := by decide
  have hdescent : baseEnd_170997 < baseStart_170997 := by decide
  rcases family_descends (prefixWord ++ tailWord_170997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171004 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 3]
def baseStart_171004 : Nat := 118140960795 + 171004 * 2 ^ 59
def prefixEnd_171004 : Nat := 4983230072969 + 3 ^ 40 * 171004 * 2
def baseEnd_171004 : Nat := 78050885192492604234287

theorem tailTrace_171004 : CollatzResearch.WordTrace tailWord_171004 prefixEnd_171004 78050885192492604234287 := by
  unfold tailWord_171004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118514136244594001584033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4158018848326125335445377 3118514136244594001584033)
  ·
    refine ⟨2338885602183445501188025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3118514136244594001584033 2338885602183445501188025)
    ·
      refine ⟨1754164201637584125891019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2338885602183445501188025 1754164201637584125891019)
      ·
        refine ⟨2631246302456376188836529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1754164201637584125891019 2631246302456376188836529)
        ·
          refine ⟨1973434726842282141627397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2631246302456376188836529 1973434726842282141627397)
          ·
            refine ⟨370019011282927901555137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1973434726842282141627397 370019011282927901555137)
            ·
              refine ⟨277514258462195926166353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370019011282927901555137 277514258462195926166353)
              ·
                refine ⟨208135693846646944624765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277514258462195926166353 208135693846646944624765)
                ·
                  refine ⟨78050885192492604234287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208135693846646944624765 78050885192492604234287)
                  ·
                    rfl

theorem cell20_171004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_171004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171004 prefixEnd_171004 := by exact prefixLift 171004
  have htrace : WordTrace (prefixWord ++ tailWord_171004) baseStart_171004 baseEnd_171004 := by
    simpa [prefixWord, tailWord_171004, baseEnd_171004] using wordTrace_append hprefix tailTrace_171004
  have hstable : (prefixWord ++ tailWord_171004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171004).length < 2 ^ (prefixWord ++ tailWord_171004).sum := by decide
  have hdescent : baseEnd_171004 < baseStart_171004 := by decide
  rcases family_descends (prefixWord ++ tailWord_171004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171008 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_171008 : Nat := 118140960795 + 171008 * 2 ^ 59
def prefixEnd_171008 : Nat := 4983230072969 + 3 ^ 40 * 171008 * 2
def baseEnd_171008 : Nat := 78052710901486368100937

theorem tailTrace_171008 : CollatzResearch.WordTrace tailWord_171008 prefixEnd_171008 78052710901486368100937 := by
  unfold tailWord_171008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118587082237348343156839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4158116109649797790875785 3118587082237348343156839)
  ·
    refine ⟨4677880623356022514735259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3118587082237348343156839 4677880623356022514735259)
    ·
      refine ⟨7016820935034033772102889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4677880623356022514735259 7016820935034033772102889)
      ·
        refine ⟨5262615701275525329077167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7016820935034033772102889 5262615701275525329077167)
        ·
          refine ⟨7893923551913287993615751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5262615701275525329077167 7893923551913287993615751)
          ·
            refine ⟨11840885327869931990423627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7893923551913287993615751 11840885327869931990423627)
            ·
              refine ⟨17761327991804897985635441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11840885327869931990423627 17761327991804897985635441)
              ·
                refine ⟨13320995993853673489226581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17761327991804897985635441 13320995993853673489226581)
                ·
                  refine ⟨78052710901486368100937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13320995993853673489226581 78052710901486368100937)
                  ·
                    rfl

theorem cell20_171008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_171008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171008 prefixEnd_171008 := by exact prefixLift 171008
  have htrace : WordTrace (prefixWord ++ tailWord_171008) baseStart_171008 baseEnd_171008 := by
    simpa [prefixWord, tailWord_171008, baseEnd_171008] using wordTrace_append hprefix tailTrace_171008
  have hstable : (prefixWord ++ tailWord_171008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171008).length < 2 ^ (prefixWord ++ tailWord_171008).sum := by decide
  have hdescent : baseEnd_171008 < baseStart_171008 := by decide
  rcases family_descends (prefixWord ++ tailWord_171008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171018 : List Nat := [3, 1, 2, 2, 3, 1, 3, 5]
def baseStart_171018 : Nat := 118140960795 + 171018 * 2 ^ 59
def prefixEnd_171018 : Nat := 4983230072969 + 3 ^ 40 * 171018 * 2
def baseEnd_171018 : Nat := 26019091724656925922521

theorem tailTrace_171018 : CollatzResearch.WordTrace tailWord_171018 prefixEnd_171018 26019091724656925922521 := by
  unfold tailWord_171018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559384723609617098544427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4158359262958978929451805 1559384723609617098544427)
  ·
    refine ⟨2339077085414425647816641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1559384723609617098544427 2339077085414425647816641)
    ·
      refine ⟨1754307814060819235862481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2339077085414425647816641 1754307814060819235862481)
      ·
        refine ⟨1315730860545614426896861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1754307814060819235862481 1315730860545614426896861)
        ·
          refine ⟨493399072704605410086323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1315730860545614426896861 493399072704605410086323)
          ·
            refine ⟨740098609056908115129485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493399072704605410086323 740098609056908115129485)
            ·
              refine ⟨277536978396340543173557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 740098609056908115129485 277536978396340543173557)
              ·
                refine ⟨26019091724656925922521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 277536978396340543173557 26019091724656925922521)
                ·
                  rfl

theorem cell20_171018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_171018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171018 prefixEnd_171018 := by exact prefixLift 171018
  have htrace : WordTrace (prefixWord ++ tailWord_171018) baseStart_171018 baseEnd_171018 := by
    simpa [prefixWord, tailWord_171018, baseEnd_171018] using wordTrace_append hprefix tailTrace_171018
  have hstable : (prefixWord ++ tailWord_171018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171018).length < 2 ^ (prefixWord ++ tailWord_171018).sum := by decide
  have hdescent : baseEnd_171018 < baseStart_171018 := by decide
  rcases family_descends (prefixWord ++ tailWord_171018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171032 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_171032 : Nat := 118140960795 + 171032 * 2 ^ 59
def prefixEnd_171032 : Nat := 4983230072969 + 3 ^ 40 * 171032 * 2
def baseEnd_171032 : Nat := 78063665155448951300839

theorem tailTrace_171032 : CollatzResearch.WordTrace tailWord_171032 prefixEnd_171032 78063665155448951300839 := by
  unfold tailWord_171032
  simp only [CollatzResearch.WordTrace]
  refine ⟨3119024758193874392593675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4158699677591832523458233 3119024758193874392593675)
  ·
    refine ⟨4678537137290811588890513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3119024758193874392593675 4678537137290811588890513)
    ·
      refine ⟨3508902852968108691667885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4678537137290811588890513 3508902852968108691667885)
      ·
        refine ⟨1315838569863040759375457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3508902852968108691667885 1315838569863040759375457)
        ·
          refine ⟨986878927397280569531593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1315838569863040759375457 986878927397280569531593)
          ·
            refine ⟨740159195547960427148695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 986878927397280569531593 740159195547960427148695)
            ·
              refine ⟨1110238793321940640723043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740159195547960427148695 1110238793321940640723043)
              ·
                refine ⟨1665358189982910961084565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110238793321940640723043 1665358189982910961084565)
                ·
                  refine ⟨78063665155448951300839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1665358189982910961084565 78063665155448951300839)
                  ·
                    rfl

theorem cell20_171032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_171032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171032 prefixEnd_171032 := by exact prefixLift 171032
  have htrace : WordTrace (prefixWord ++ tailWord_171032) baseStart_171032 baseEnd_171032 := by
    simpa [prefixWord, tailWord_171032, baseEnd_171032] using wordTrace_append hprefix tailTrace_171032
  have hstable : (prefixWord ++ tailWord_171032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171032).length < 2 ^ (prefixWord ++ tailWord_171032).sum := by decide
  have hdescent : baseEnd_171032 < baseStart_171032 := by decide
  rcases family_descends (prefixWord ++ tailWord_171032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171080 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 3]
def baseStart_171080 : Nat := 118140960795 + 171080 * 2 ^ 59
def prefixEnd_171080 : Nat := 4983230072969 + 3 ^ 40 * 171080 * 2
def baseEnd_171080 : Nat := 78085573663374117700643

theorem tailTrace_171080 : CollatzResearch.WordTrace tailWord_171080 prefixEnd_171080 78085573663374117700643 := by
  unfold tailWord_171080
  simp only [CollatzResearch.WordTrace]
  refine ⟨3119900110106926491467347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4159866813475901988623129 3119900110106926491467347)
  ·
    refine ⟨4679850165160389737201021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3119900110106926491467347 4679850165160389737201021)
    ·
      refine ⟨1754943811935146151450383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4679850165160389737201021 1754943811935146151450383)
      ·
        refine ⟨2632415717902719227175575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1754943811935146151450383 2632415717902719227175575)
        ·
          refine ⟨3948623576854078840763363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2632415717902719227175575 3948623576854078840763363)
          ·
            refine ⟨5922935365281118261145045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948623576854078840763363 5922935365281118261145045)
            ·
              refine ⟨138818797623776209245587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5922935365281118261145045 138818797623776209245587)
              ·
                refine ⟨208228196435664313868381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138818797623776209245587 208228196435664313868381)
                ·
                  refine ⟨78085573663374117700643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208228196435664313868381 78085573663374117700643)
                  ·
                    rfl

theorem cell20_171080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_171080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171080 prefixEnd_171080 := by exact prefixLift 171080
  have htrace : WordTrace (prefixWord ++ tailWord_171080) baseStart_171080 baseEnd_171080 := by
    simpa [prefixWord, tailWord_171080, baseEnd_171080] using wordTrace_append hprefix tailTrace_171080
  have hstable : (prefixWord ++ tailWord_171080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171080).length < 2 ^ (prefixWord ++ tailWord_171080).sum := by decide
  have hdescent : baseEnd_171080 < baseStart_171080 := by decide
  rcases family_descends (prefixWord ++ tailWord_171080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171139 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 3]
def baseStart_171139 : Nat := 118140960795 + 171139 * 2 ^ 59
def prefixEnd_171139 : Nat := 4983230072969 + 3 ^ 40 * 171139 * 2
def baseEnd_171139 : Nat := 78112502871032134733735

theorem tailTrace_171139 : CollatzResearch.WordTrace tailWord_171139 prefixEnd_171139 78112502871032134733735 := by
  unfold tailWord_171139
  simp only [CollatzResearch.WordTrace]
  refine ⟨6241952127000106059332471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4161301418000070706221647 6241952127000106059332471)
  ·
    refine ⟨9362928190500159088998707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6241952127000106059332471 9362928190500159088998707)
    ·
      refine ⟨14044392285750238633498061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9362928190500159088998707 14044392285750238633498061)
      ·
        refine ⟨5266647107156339487561773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14044392285750238633498061 5266647107156339487561773)
        ·
          refine ⟨1974992665183627307835665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5266647107156339487561773 1974992665183627307835665)
          ·
            refine ⟨1481244498887720480876749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974992665183627307835665 1481244498887720480876749)
            ·
              refine ⟨555466687082895180328781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1481244498887720480876749 555466687082895180328781)
              ·
                refine ⟨208300007656085692623293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555466687082895180328781 208300007656085692623293)
                ·
                  refine ⟨78112502871032134733735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208300007656085692623293 78112502871032134733735)
                  ·
                    rfl

theorem cell20_171139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 3].length) (baseStart_171139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171139 prefixEnd_171139 := by exact prefixLift 171139
  have htrace : WordTrace (prefixWord ++ tailWord_171139) baseStart_171139 baseEnd_171139 := by
    simpa [prefixWord, tailWord_171139, baseEnd_171139] using wordTrace_append hprefix tailTrace_171139
  have hstable : (prefixWord ++ tailWord_171139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171139).length < 2 ^ (prefixWord ++ tailWord_171139).sum := by decide
  have hdescent : baseEnd_171139 < baseStart_171139 := by decide
  rcases family_descends (prefixWord ++ tailWord_171139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171146 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_171146 : Nat := 118140960795 + 171146 * 2 ^ 59
def prefixEnd_171146 : Nat := 4983230072969 + 3 ^ 40 * 171146 * 2
def baseEnd_171146 : Nat := 78115697861771221500373

theorem tailTrace_171146 : CollatzResearch.WordTrace tailWord_171146 prefixEnd_171146 78115697861771221500373 := by
  unfold tailWord_171146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560551859493686563709323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4161471625316497503224861 1560551859493686563709323)
  ·
    refine ⟨2340827789240529845563985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1560551859493686563709323 2340827789240529845563985)
    ·
      refine ⟨1755620841930397384172989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2340827789240529845563985 1755620841930397384172989)
      ·
        refine ⟨658357815723899019064871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1755620841930397384172989 658357815723899019064871)
        ·
          refine ⟨987536723585848528597307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658357815723899019064871 987536723585848528597307)
          ·
            refine ⟨1481305085378772792895961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987536723585848528597307 1481305085378772792895961)
            ·
              refine ⟨1110978814034079594671971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481305085378772792895961 1110978814034079594671971)
              ·
                refine ⟨1666468221051119392007957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110978814034079594671971 1666468221051119392007957)
                ·
                  refine ⟨78115697861771221500373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1666468221051119392007957 78115697861771221500373)
                  ·
                    rfl

theorem cell20_171146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_171146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171146 prefixEnd_171146 := by exact prefixLift 171146
  have htrace : WordTrace (prefixWord ++ tailWord_171146) baseStart_171146 baseEnd_171146 := by
    simpa [prefixWord, tailWord_171146, baseEnd_171146] using wordTrace_append hprefix tailTrace_171146
  have hstable : (prefixWord ++ tailWord_171146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171146).length < 2 ^ (prefixWord ++ tailWord_171146).sum := by decide
  have hdescent : baseEnd_171146 < baseStart_171146 := by decide
  rcases family_descends (prefixWord ++ tailWord_171146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171170 : List Nat := [3, 3, 1, 3, 2, 8]
def baseStart_171170 : Nat := 118140960795 + 171170 * 2 ^ 59
def prefixEnd_171170 : Nat := 4983230072969 + 3 ^ 40 * 171170 * 2
def baseEnd_171170 : Nat := 2893579707990140914825

theorem tailTrace_171170 : CollatzResearch.WordTrace tailWord_171170 prefixEnd_171170 2893579707990140914825 := by
  unfold tailWord_171170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560770697471949588427741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4162055193258532235807309 1560770697471949588427741)
  ·
    refine ⟨585289011551981095660403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1560770697471949588427741 585289011551981095660403)
    ·
      refine ⟨877933517327971643490605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 585289011551981095660403 877933517327971643490605)
      ·
        refine ⟨329225068997989366308977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 877933517327971643490605 329225068997989366308977)
        ·
          refine ⟨246918801748492024731733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329225068997989366308977 246918801748492024731733)
          ·
            refine ⟨2893579707990140914825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 246918801748492024731733 2893579707990140914825)
            ·
              rfl

theorem cell20_171170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 8].length) (baseStart_171170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171170 prefixEnd_171170 := by exact prefixLift 171170
  have htrace : WordTrace (prefixWord ++ tailWord_171170) baseStart_171170 baseEnd_171170 := by
    simpa [prefixWord, tailWord_171170, baseEnd_171170] using wordTrace_append hprefix tailTrace_171170
  have hstable : (prefixWord ++ tailWord_171170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171170).length < 2 ^ (prefixWord ++ tailWord_171170).sum := by decide
  have hdescent : baseEnd_171170 < baseStart_171170 := by decide
  rcases family_descends (prefixWord ++ tailWord_171170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171201 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 6]
def baseStart_171201 : Nat := 118140960795 + 171201 * 2 ^ 59
def prefixEnd_171201 : Nat := 4983230072969 + 3 ^ 40 * 171201 * 2
def baseEnd_171201 : Nat := 78140801360435474666815

theorem tailTrace_171201 : CollatzResearch.WordTrace tailWord_171201 prefixEnd_171201 78140801360435474666815 := by
  unfold tailWord_171201
  simp only [CollatzResearch.WordTrace]
  refine ⟨6244213452775490648089457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4162808968516993765392971 6244213452775490648089457)
  ·
    refine ⟨4683160089581617986067093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6244213452775490648089457 4683160089581617986067093)
    ·
      refine ⟨219523129199138343096895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4683160089581617986067093 219523129199138343096895)
      ·
        refine ⟨329284693798707514645343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219523129199138343096895 329284693798707514645343)
        ·
          refine ⟨493927040698061271968015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329284693798707514645343 493927040698061271968015)
          ·
            refine ⟨740890561047091907952023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493927040698061271968015 740890561047091907952023)
            ·
              refine ⟨1111335841570637861928035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740890561047091907952023 1111335841570637861928035)
              ·
                refine ⟨1667003762355956792892053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111335841570637861928035 1667003762355956792892053)
                ·
                  refine ⟨78140801360435474666815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1667003762355956792892053 78140801360435474666815)
                  ·
                    rfl

theorem cell20_171201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_171201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171201 prefixEnd_171201 := by exact prefixLift 171201
  have htrace : WordTrace (prefixWord ++ tailWord_171201) baseStart_171201 baseEnd_171201 := by
    simpa [prefixWord, tailWord_171201, baseEnd_171201] using wordTrace_append hprefix tailTrace_171201
  have hstable : (prefixWord ++ tailWord_171201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171201).length < 2 ^ (prefixWord ++ tailWord_171201).sum := by decide
  have hdescent : baseEnd_171201 < baseStart_171201 := by decide
  rcases family_descends (prefixWord ++ tailWord_171201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171218 : List Nat := [3, 2, 2, 2, 1, 1, 4, 3, 2]
def baseStart_171218 : Nat := 118140960795 + 171218 * 2 ^ 59
def prefixEnd_171218 : Nat := 4983230072969 + 3 ^ 40 * 171218 * 2
def baseEnd_171218 : Nat := 78148560623658971100079

theorem tailTrace_171218 : CollatzResearch.WordTrace tailWord_171218 prefixEnd_171218 78148560623658971100079 := by
  unfold tailWord_171218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561208373428475637864577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4163222329142601700972205 1561208373428475637864577)
  ·
    refine ⟨1170906280071356728398433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1561208373428475637864577 1170906280071356728398433)
    ·
      refine ⟨878179710053517546298825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1170906280071356728398433 878179710053517546298825)
      ·
        refine ⟨658634782540138159724119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 878179710053517546298825 658634782540138159724119)
        ·
          refine ⟨987952173810207239586179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658634782540138159724119 987952173810207239586179)
          ·
            refine ⟨1481928260715310859379269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987952173810207239586179 1481928260715310859379269)
            ·
              refine ⟨277861548884120786133613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1481928260715310859379269 277861548884120786133613)
              ·
                refine ⟨104198080831545294800105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277861548884120786133613 104198080831545294800105)
                ·
                  refine ⟨78148560623658971100079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104198080831545294800105 78148560623658971100079)
                  ·
                    rfl

theorem cell20_171218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_171218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171218 prefixEnd_171218 := by exact prefixLift 171218
  have htrace : WordTrace (prefixWord ++ tailWord_171218) baseStart_171218 baseEnd_171218 := by
    simpa [prefixWord, tailWord_171218, baseEnd_171218] using wordTrace_append hprefix tailTrace_171218
  have hstable : (prefixWord ++ tailWord_171218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171218).length < 2 ^ (prefixWord ++ tailWord_171218).sum := by decide
  have hdescent : baseEnd_171218 < baseStart_171218 := by decide
  rcases family_descends (prefixWord ++ tailWord_171218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171232 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 3]
def baseStart_171232 : Nat := 118140960795 + 171232 * 2 ^ 59
def prefixEnd_171232 : Nat := 4983230072969 + 3 ^ 40 * 171232 * 2
def baseEnd_171232 : Nat := 78154950605137144633355

theorem tailTrace_171232 : CollatzResearch.WordTrace tailWord_171232 prefixEnd_171232 78154950605137144633355 := by
  unfold tailWord_171232
  simp only [CollatzResearch.WordTrace]
  refine ⟨3122672057831591471233975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4163562743775455294978633 3122672057831591471233975)
  ·
    refine ⟨4684008086747387206850963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3122672057831591471233975 4684008086747387206850963)
    ·
      refine ⟨7026012130121080810276445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4684008086747387206850963 7026012130121080810276445)
      ·
        refine ⟨2634754548795405303853667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7026012130121080810276445 2634754548795405303853667)
        ·
          refine ⟨3952131823193107955780501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2634754548795405303853667 3952131823193107955780501)
          ·
            refine ⟨185256179212176935427211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3952131823193107955780501 185256179212176935427211)
            ·
              refine ⟨277884268818265403140817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185256179212176935427211 277884268818265403140817)
              ·
                refine ⟨208413201613699052355613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277884268818265403140817 208413201613699052355613)
                ·
                  refine ⟨78154950605137144633355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208413201613699052355613 78154950605137144633355)
                  ·
                    rfl

theorem cell20_171232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_171232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171232 prefixEnd_171232 := by exact prefixLift 171232
  have htrace : WordTrace (prefixWord ++ tailWord_171232) baseStart_171232 baseEnd_171232 := by
    simpa [prefixWord, tailWord_171232, baseEnd_171232] using wordTrace_append hprefix tailTrace_171232
  have hstable : (prefixWord ++ tailWord_171232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171232).length < 2 ^ (prefixWord ++ tailWord_171232).sum := by decide
  have hdescent : baseEnd_171232 < baseStart_171232 := by decide
  rcases family_descends (prefixWord ++ tailWord_171232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171267 : List Nat := [1, 1, 1, 3, 2, 5, 1, 6]
def baseStart_171267 : Nat := 118140960795 + 171267 * 2 ^ 59
def prefixEnd_171267 : Nat := 4983230072969 + 3 ^ 40 * 171267 * 2
def baseEnd_171267 : Nat := 26056975186277526155515

theorem tailTrace_171267 : CollatzResearch.WordTrace tailWord_171267 prefixEnd_171267 26056975186277526155515 := by
  unfold tailWord_171267
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246620670536383919992055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4164413780357589279994703 6246620670536383919992055)
  ·
    refine ⟨9369931005804575879988083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6246620670536383919992055 9369931005804575879988083)
    ·
      refine ⟨14054896508706863819982125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9369931005804575879988083 14054896508706863819982125)
      ·
        refine ⟨5270586190765073932493297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14054896508706863819982125 5270586190765073932493297)
        ·
          refine ⟨3952939643073805449369973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5270586190765073932493297 3952939643073805449369973)
          ·
            refine ⟨370588091538169260878435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3952939643073805449369973 370588091538169260878435)
            ·
              refine ⟨555882137307253891317653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370588091538169260878435 555882137307253891317653)
              ·
                refine ⟨26056975186277526155515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 555882137307253891317653 26056975186277526155515)
                ·
                  rfl

theorem cell20_171267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_171267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171267 prefixEnd_171267 := by exact prefixLift 171267
  have htrace : WordTrace (prefixWord ++ tailWord_171267) baseStart_171267 baseEnd_171267 := by
    simpa [prefixWord, tailWord_171267, baseEnd_171267] using wordTrace_append hprefix tailTrace_171267
  have hstable : (prefixWord ++ tailWord_171267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171267).length < 2 ^ (prefixWord ++ tailWord_171267).sum := by decide
  have hdescent : baseEnd_171267 < baseStart_171267 := by decide
  rcases family_descends (prefixWord ++ tailWord_171267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171349 : List Nat := [1, 3, 2, 2, 3, 3, 2, 2, 2]
def baseStart_171349 : Nat := 118140960795 + 171349 * 2 ^ 59
def prefixEnd_171349 : Nat := 4983230072969 + 3 ^ 40 * 171349 * 2
def baseEnd_171349 : Nat := 78208352593204737732877

theorem tailTrace_171349 : CollatzResearch.WordTrace tailWord_171349 prefixEnd_171349 78208352593204737732877 := by
  unfold tailWord_171349
  simp only [CollatzResearch.WordTrace]
  refine ⟨6249611456239311924477101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4166407637492874616318067 6249611456239311924477101)
  ·
    refine ⟨2343604296089741971678913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6249611456239311924477101 2343604296089741971678913)
    ·
      refine ⟨1757703222067306478759185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2343604296089741971678913 1757703222067306478759185)
      ·
        refine ⟨1318277416550479859069389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1757703222067306478759185 1318277416550479859069389)
        ·
          refine ⟨494354031206429947151021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1318277416550479859069389 494354031206429947151021)
          ·
            refine ⟨185382761702411230181633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 494354031206429947151021 185382761702411230181633)
            ·
              refine ⟨139037071276808422636225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185382761702411230181633 139037071276808422636225)
              ·
                refine ⟨104277803457606316977169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139037071276808422636225 104277803457606316977169)
                ·
                  refine ⟨78208352593204737732877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104277803457606316977169 78208352593204737732877)
                  ·
                    rfl

theorem cell20_171349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_171349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171349 prefixEnd_171349 := by exact prefixLift 171349
  have htrace : WordTrace (prefixWord ++ tailWord_171349) baseStart_171349 baseEnd_171349 := by
    simpa [prefixWord, tailWord_171349, baseEnd_171349] using wordTrace_append hprefix tailTrace_171349
  have hstable : (prefixWord ++ tailWord_171349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171349).length < 2 ^ (prefixWord ++ tailWord_171349).sum := by decide
  have hdescent : baseEnd_171349 < baseStart_171349 := by decide
  rcases family_descends (prefixWord ++ tailWord_171349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171360 : List Nat := [2, 1, 1, 3, 4, 3, 1, 5]
def baseStart_171360 : Nat := 118140960795 + 171360 * 2 ^ 59
def prefixEnd_171360 : Nat := 4983230072969 + 3 ^ 40 * 171360 * 2
def baseEnd_171360 : Nat := 26071124430979196122055

theorem tailTrace_171360 : CollatzResearch.WordTrace tailWord_171360 prefixEnd_171360 26071124430979196122055 := by
  unfold tailWord_171360
  simp only [CollatzResearch.WordTrace]
  refine ⟨3125006329599730401563767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4166675106132973868751689 3125006329599730401563767)
  ·
    refine ⟨4687509494399595602345651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3125006329599730401563767 4687509494399595602345651)
    ·
      refine ⟨7031264241599393403518477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4687509494399595602345651 7031264241599393403518477)
      ·
        refine ⟨2636724090599772526319429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7031264241599393403518477 2636724090599772526319429)
        ·
          refine ⟨494385766987457348684893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2636724090599772526319429 494385766987457348684893)
          ·
            refine ⟨185394662620296505756835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 494385766987457348684893 185394662620296505756835)
            ·
              refine ⟨278091993930444758635253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185394662620296505756835 278091993930444758635253)
              ·
                refine ⟨26071124430979196122055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 278091993930444758635253 26071124430979196122055)
                ·
                  rfl

theorem cell20_171360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_171360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171360 prefixEnd_171360 := by exact prefixLift 171360
  have htrace : WordTrace (prefixWord ++ tailWord_171360) baseStart_171360 baseEnd_171360 := by
    simpa [prefixWord, tailWord_171360, baseEnd_171360] using wordTrace_append hprefix tailTrace_171360
  have hstable : (prefixWord ++ tailWord_171360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171360).length < 2 ^ (prefixWord ++ tailWord_171360).sum := by decide
  have hdescent : baseEnd_171360 < baseStart_171360 := by decide
  rcases family_descends (prefixWord ++ tailWord_171360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171388 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_171388 : Nat := 118140960795 + 171388 * 2 ^ 59
def prefixEnd_171388 : Nat := 4983230072969 + 3 ^ 40 * 171388 * 2
def baseEnd_171388 : Nat := 78226153255893935432717

theorem tailTrace_171388 : CollatzResearch.WordTrace tailWord_171388 prefixEnd_171388 78226153255893935432717 := by
  unfold tailWord_171388
  simp only [CollatzResearch.WordTrace]
  refine ⟨3125516951549010792573409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4167355935398681056764545 3125516951549010792573409)
  ·
    refine ⟨2344137713661758094430057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3125516951549010792573409 2344137713661758094430057)
    ·
      refine ⟨1758103285246318570822543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2344137713661758094430057 1758103285246318570822543)
      ·
        refine ⟨2637154927869477856233815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758103285246318570822543 2637154927869477856233815)
        ·
          refine ⟨3955732391804216784350723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637154927869477856233815 3955732391804216784350723)
          ·
            refine ⟨5933598587706325176526085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3955732391804216784350723 5933598587706325176526085)
            ·
              refine ⟨1112549735194935970598641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5933598587706325176526085 1112549735194935970598641)
              ·
                refine ⟨834412301396201977948981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112549735194935970598641 834412301396201977948981)
                ·
                  refine ⟨78226153255893935432717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 834412301396201977948981 78226153255893935432717)
                  ·
                    rfl

theorem cell20_171388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_171388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171388 prefixEnd_171388 := by exact prefixLift 171388
  have htrace : WordTrace (prefixWord ++ tailWord_171388) baseStart_171388 baseEnd_171388 := by
    simpa [prefixWord, tailWord_171388, baseEnd_171388] using wordTrace_append hprefix tailTrace_171388
  have hstable : (prefixWord ++ tailWord_171388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171388).length < 2 ^ (prefixWord ++ tailWord_171388).sum := by decide
  have hdescent : baseEnd_171388 < baseStart_171388 := by decide
  rcases family_descends (prefixWord ++ tailWord_171388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171401 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 3]
def baseStart_171401 : Nat := 118140960795 + 171401 * 2 ^ 59
def prefixEnd_171401 : Nat := 4983230072969 + 3 ^ 40 * 171401 * 2
def baseEnd_171401 : Nat := 78232086810123667999331

theorem tailTrace_171401 : CollatzResearch.WordTrace tailWord_171401 prefixEnd_171401 78232086810123667999331 := by
  unfold tailWord_171401
  simp only [CollatzResearch.WordTrace]
  refine ⟨6251508052050924805370057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4167672034700616536913371 6251508052050924805370057)
  ·
    refine ⟨4688631039038193604027543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6251508052050924805370057 4688631039038193604027543)
    ·
      refine ⟨7032946558557290406041315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4688631039038193604027543 7032946558557290406041315)
      ·
        refine ⟨10549419837835935609061973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7032946558557290406041315 10549419837835935609061973)
        ·
          refine ⟨123626013724639870418695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 10549419837835935609061973 123626013724639870418695)
          ·
            refine ⟨185439020586959805628043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123626013724639870418695 185439020586959805628043)
            ·
              refine ⟨278158530880439708442065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185439020586959805628043 278158530880439708442065)
              ·
                refine ⟨208618898160329781331549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278158530880439708442065 208618898160329781331549)
                ·
                  refine ⟨78232086810123667999331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208618898160329781331549 78232086810123667999331)
                  ·
                    rfl

theorem cell20_171401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_171401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171401 prefixEnd_171401 := by exact prefixLift 171401
  have htrace : WordTrace (prefixWord ++ tailWord_171401) baseStart_171401 baseEnd_171401 := by
    simpa [prefixWord, tailWord_171401, baseEnd_171401] using wordTrace_append hprefix tailTrace_171401
  have hstable : (prefixWord ++ tailWord_171401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171401).length < 2 ^ (prefixWord ++ tailWord_171401).sum := by decide
  have hdescent : baseEnd_171401 < baseStart_171401 := by decide
  rcases family_descends (prefixWord ++ tailWord_171401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171432 : List Nat := [2, 1, 6, 1, 2, 2, 2, 4]
def baseStart_171432 : Nat := 118140960795 + 171432 * 2 ^ 59
def prefixEnd_171432 : Nat := 4983230072969 + 3 ^ 40 * 171432 * 2
def baseEnd_171432 : Nat := 26082078684941779321957

theorem tailTrace_171432 : CollatzResearch.WordTrace tailWord_171432 prefixEnd_171432 26082078684941779321957 := by
  unfold tailWord_171432
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126319357469308549874275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4168425809959078066499033 3126319357469308549874275)
  ·
    refine ⟨4689479036203962824811413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3126319357469308549874275 4689479036203962824811413)
    ·
      refine ⟨219819329822060757413035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4689479036203962824811413 219819329822060757413035)
      ·
        refine ⟨329728994733091136119553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219819329822060757413035 329728994733091136119553)
        ·
          refine ⟨247296746049818352089665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329728994733091136119553 247296746049818352089665)
          ·
            refine ⟨185472559537363764067249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247296746049818352089665 185472559537363764067249)
            ·
              refine ⟨139104419653022823050437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185472559537363764067249 139104419653022823050437)
              ·
                refine ⟨26082078684941779321957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139104419653022823050437 26082078684941779321957)
                ·
                  rfl

theorem cell20_171432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_171432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171432 prefixEnd_171432 := by exact prefixLift 171432
  have htrace : WordTrace (prefixWord ++ tailWord_171432) baseStart_171432 baseEnd_171432 := by
    simpa [prefixWord, tailWord_171432, baseEnd_171432] using wordTrace_append hprefix tailTrace_171432
  have hstable : (prefixWord ++ tailWord_171432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171432).length < 2 ^ (prefixWord ++ tailWord_171432).sum := by decide
  have hdescent : baseEnd_171432 < baseStart_171432 := by decide
  rcases family_descends (prefixWord ++ tailWord_171432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171464 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_171464 : Nat := 118140960795 + 171464 * 2 ^ 59
def prefixEnd_171464 : Nat := 4983230072969 + 3 ^ 40 * 171464 * 2
def baseEnd_171464 : Nat := 78260841726775448899073

theorem tailTrace_171464 : CollatzResearch.WordTrace tailWord_171464 prefixEnd_171464 78260841726775448899073 := by
  unfold tailWord_171464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126902925411343282456723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4169203900548457709942297 3126902925411343282456723)
  ·
    refine ⟨4690354388117014923685085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3126902925411343282456723 4690354388117014923685085)
    ·
      refine ⟨1758882895543880596381907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4690354388117014923685085 1758882895543880596381907)
      ·
        refine ⟨2638324343315820894572861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758882895543880596381907 2638324343315820894572861)
        ·
          refine ⟨989371628743432835464823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2638324343315820894572861 989371628743432835464823)
          ·
            refine ⟨1484057443115149253197235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989371628743432835464823 1484057443115149253197235)
            ·
              refine ⟨2226086164672723879795853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484057443115149253197235 2226086164672723879795853)
              ·
                refine ⟨834782311752271454923445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2226086164672723879795853 834782311752271454923445)
                ·
                  refine ⟨78260841726775448899073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 834782311752271454923445 78260841726775448899073)
                  ·
                    rfl

theorem cell20_171464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_171464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171464 prefixEnd_171464 := by exact prefixLift 171464
  have htrace : WordTrace (prefixWord ++ tailWord_171464) baseStart_171464 baseEnd_171464 := by
    simpa [prefixWord, tailWord_171464, baseEnd_171464] using wordTrace_append hprefix tailTrace_171464
  have hstable : (prefixWord ++ tailWord_171464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171464).length < 2 ^ (prefixWord ++ tailWord_171464).sum := by decide
  have hdescent : baseEnd_171464 < baseStart_171464 := by decide
  rcases family_descends (prefixWord ++ tailWord_171464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171481 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 3]
def baseStart_171481 : Nat := 118140960795 + 171481 * 2 ^ 59
def prefixEnd_171481 : Nat := 4983230072969 + 3 ^ 40 * 171481 * 2
def baseEnd_171481 : Nat := 78268600989998945332337

theorem tailTrace_171481 : CollatzResearch.WordTrace tailWord_171481 prefixEnd_171481 78268600989998945332337 := by
  unfold tailWord_171481
  simp only [CollatzResearch.WordTrace]
  refine ⟨6254425891761098468282297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4169617261174065645521531 6254425891761098468282297)
  ·
    refine ⟨4690819418820823851211723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6254425891761098468282297 4690819418820823851211723)
    ·
      refine ⟨7036229128231235776817585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4690819418820823851211723 7036229128231235776817585)
      ·
        refine ⟨5277171846173426832613189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7036229128231235776817585 5277171846173426832613189)
        ·
          refine ⟨989469721157517531114973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5277171846173426832613189 989469721157517531114973)
          ·
            refine ⟨371051145434069074168115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 989469721157517531114973 371051145434069074168115)
            ·
              refine ⟨556576718151103611252173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371051145434069074168115 556576718151103611252173)
              ·
                refine ⟨208716269306663854219565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 556576718151103611252173 208716269306663854219565)
                ·
                  refine ⟨78268600989998945332337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208716269306663854219565 78268600989998945332337)
                  ·
                    rfl

theorem cell20_171481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_171481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171481 prefixEnd_171481 := by exact prefixLift 171481
  have htrace : WordTrace (prefixWord ++ tailWord_171481) baseStart_171481 baseEnd_171481 := by
    simpa [prefixWord, tailWord_171481, baseEnd_171481] using wordTrace_append hprefix tailTrace_171481
  have hstable : (prefixWord ++ tailWord_171481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171481).length < 2 ^ (prefixWord ++ tailWord_171481).sum := by decide
  have hdescent : baseEnd_171481 < baseStart_171481 := by decide
  rcases family_descends (prefixWord ++ tailWord_171481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171495 : List Nat := [1, 1, 5, 2, 1, 2, 2, 6]
def baseStart_171495 : Nat := 118140960795 + 171495 * 2 ^ 59
def prefixEnd_171495 : Nat := 4983230072969 + 3 ^ 40 * 171495 * 2
def baseEnd_171495 : Nat := 26091663657159039621871

theorem tailTrace_171495 : CollatzResearch.WordTrace tailWord_171495 prefixEnd_171495 26091663657159039621871 := by
  unfold tailWord_171495
  simp only [CollatzResearch.WordTrace]
  refine ⟨6254936513710378859291939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4169957675806919239527959 6254936513710378859291939)
  ·
    refine ⟨9382404770565568288937909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6254936513710378859291939 9382404770565568288937909)
    ·
      refine ⟨879600447240522027087929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9382404770565568288937909 879600447240522027087929)
      ·
        refine ⟨659700335430391520315947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 879600447240522027087929 659700335430391520315947)
        ·
          refine ⟨989550503145587280473921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659700335430391520315947 989550503145587280473921)
          ·
            refine ⟨742162877359190460355441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 989550503145587280473921 742162877359190460355441)
            ·
              refine ⟨556622158019392845266581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 742162877359190460355441 556622158019392845266581)
              ·
                refine ⟨26091663657159039621871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 556622158019392845266581 26091663657159039621871)
                ·
                  rfl

theorem cell20_171495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_171495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171495 prefixEnd_171495 := by exact prefixLift 171495
  have htrace : WordTrace (prefixWord ++ tailWord_171495) baseStart_171495 baseEnd_171495 := by
    simpa [prefixWord, tailWord_171495, baseEnd_171495] using wordTrace_append hprefix tailTrace_171495
  have hstable : (prefixWord ++ tailWord_171495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171495).length < 2 ^ (prefixWord ++ tailWord_171495).sum := by decide
  have hdescent : baseEnd_171495 < baseStart_171495 := by decide
  rcases family_descends (prefixWord ++ tailWord_171495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171574 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_171574 : Nat := 118140960795 + 171574 * 2 ^ 59
def prefixEnd_171574 : Nat := 4983230072969 + 3 ^ 40 * 171574 * 2
def baseEnd_171574 : Nat := 78311048724103955231957

theorem tailTrace_171574 : CollatzResearch.WordTrace tailWord_171574 prefixEnd_171574 78311048724103955231957 := by
  unfold tailWord_171574
  simp only [CollatzResearch.WordTrace]
  refine ⟨391113617526510959463611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4171878586949450234278517 391113617526510959463611)
  ·
    refine ⟨586670426289766439195417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 391113617526510959463611 586670426289766439195417)
    ·
      refine ⟨440002819717324829396563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 586670426289766439195417 440002819717324829396563)
      ·
        refine ⟨660004229575987244094845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440002819717324829396563 660004229575987244094845)
        ·
          refine ⟨247501586090995216535567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 660004229575987244094845 247501586090995216535567)
          ·
            refine ⟨371252379136492824803351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247501586090995216535567 371252379136492824803351)
            ·
              refine ⟨556878568704739237205027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371252379136492824803351 556878568704739237205027)
              ·
                refine ⟨835317853057108855807541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556878568704739237205027 835317853057108855807541)
                ·
                  refine ⟨78311048724103955231957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 835317853057108855807541 78311048724103955231957)
                  ·
                    rfl

theorem cell20_171574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_171574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171574 prefixEnd_171574 := by exact prefixLift 171574
  have htrace : WordTrace (prefixWord ++ tailWord_171574) baseStart_171574 baseEnd_171574 := by
    simpa [prefixWord, tailWord_171574, baseEnd_171574] using wordTrace_append hprefix tailTrace_171574
  have hstable : (prefixWord ++ tailWord_171574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171574).length < 2 ^ (prefixWord ++ tailWord_171574).sum := by decide
  have hdescent : baseEnd_171574 < baseStart_171574 := by decide
  rcases family_descends (prefixWord ++ tailWord_171574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171578 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_171578 : Nat := 118140960795 + 171578 * 2 ^ 59
def prefixEnd_171578 : Nat := 4983230072969 + 3 ^ 40 * 171578 * 2
def baseEnd_171578 : Nat := 78312874433097719098607

theorem tailTrace_171578 : CollatzResearch.WordTrace tailWord_171578 prefixEnd_171578 78312874433097719098607 := by
  unfold tailWord_171578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564490943102421008640847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4171975848273122689708925 1564490943102421008640847)
  ·
    refine ⟨2346736414653631512961271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1564490943102421008640847 2346736414653631512961271)
    ·
      refine ⟨3520104621980447269441907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2346736414653631512961271 3520104621980447269441907)
      ·
        refine ⟨5280156932970670904162861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520104621980447269441907 5280156932970670904162861)
        ·
          refine ⟨1980058849864001589061073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5280156932970670904162861 1980058849864001589061073)
          ·
            refine ⟨1485044137398001191795805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1980058849864001589061073 1485044137398001191795805)
            ·
              refine ⟨556891551524250446923427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1485044137398001191795805 556891551524250446923427)
              ·
                refine ⟨835337327286375670385141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556891551524250446923427 835337327286375670385141)
                ·
                  refine ⟨78312874433097719098607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 835337327286375670385141 78312874433097719098607)
                  ·
                    rfl

theorem cell20_171578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_171578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171578 prefixEnd_171578 := by exact prefixLift 171578
  have htrace : WordTrace (prefixWord ++ tailWord_171578) baseStart_171578 baseEnd_171578 := by
    simpa [prefixWord, tailWord_171578, baseEnd_171578] using wordTrace_append hprefix tailTrace_171578
  have hstable : (prefixWord ++ tailWord_171578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171578).length < 2 ^ (prefixWord ++ tailWord_171578).sum := by decide
  have hdescent : baseEnd_171578 < baseStart_171578 := by decide
  rcases family_descends (prefixWord ++ tailWord_171578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171581 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 4]
def baseStart_171581 : Nat := 118140960795 + 171581 * 2 ^ 59
def prefixEnd_171581 : Nat := 4983230072969 + 3 ^ 40 * 171581 * 2
def baseEnd_171581 : Nat := 78314243714843041998595

theorem tailTrace_171581 : CollatzResearch.WordTrace tailWord_171581 prefixEnd_171581 78314243714843041998595 := by
  unfold tailWord_171581
  simp only [CollatzResearch.WordTrace]
  refine ⟨6258073191398815546922597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4172048794265877031281731 6258073191398815546922597)
  ·
    refine ⟨1173388723387277915047987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6258073191398815546922597 1173388723387277915047987)
    ·
      refine ⟨1760083085080916872571981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1173388723387277915047987 1760083085080916872571981)
      ·
        refine ⟨660031156905343827214493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1760083085080916872571981 660031156905343827214493)
        ·
          refine ⟨247511683839503935205435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 660031156905343827214493 247511683839503935205435)
          ·
            refine ⟨371267525759255902808153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247511683839503935205435 371267525759255902808153)
            ·
              refine ⟨278450644319441927106115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371267525759255902808153 278450644319441927106115)
              ·
                refine ⟨417675966479162890659173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278450644319441927106115 417675966479162890659173)
                ·
                  refine ⟨78314243714843041998595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417675966479162890659173 78314243714843041998595)
                  ·
                    rfl

theorem cell20_171581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_171581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171581 prefixEnd_171581 := by exact prefixLift 171581
  have htrace : WordTrace (prefixWord ++ tailWord_171581) baseStart_171581 baseEnd_171581 := by
    simpa [prefixWord, tailWord_171581, baseEnd_171581] using wordTrace_append hprefix tailTrace_171581
  have hstable : (prefixWord ++ tailWord_171581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171581).length < 2 ^ (prefixWord ++ tailWord_171581).sum := by decide
  have hdescent : baseEnd_171581 < baseStart_171581 := by decide
  rcases family_descends (prefixWord ++ tailWord_171581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171602 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_171602 : Nat := 118140960795 + 171602 * 2 ^ 59
def prefixEnd_171602 : Nat := 4983230072969 + 3 ^ 40 * 171602 * 2
def baseEnd_171602 : Nat := 78323828687060302298509

theorem tailTrace_171602 : CollatzResearch.WordTrace tailWord_171602 prefixEnd_171602 78323828687060302298509 := by
  unfold tailWord_171602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564709781080684033359265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4172559416215157422291373 1564709781080684033359265)
  ·
    refine ⟨1173532335810513025019449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1564709781080684033359265 1173532335810513025019449)
    ·
      refine ⟨880149251857884768764587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1173532335810513025019449 880149251857884768764587)
      ·
        refine ⟨1320223877786827153146881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880149251857884768764587 1320223877786827153146881)
        ·
          refine ⟨990167908340120364860161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320223877786827153146881 990167908340120364860161)
          ·
            refine ⟨742625931255090273645121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990167908340120364860161 742625931255090273645121)
            ·
              refine ⟨556969448441317705233841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 742625931255090273645121 556969448441317705233841)
              ·
                refine ⟨417727086330988278925381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 556969448441317705233841 417727086330988278925381)
                ·
                  refine ⟨78323828687060302298509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417727086330988278925381 78323828687060302298509)
                  ·
                    rfl

theorem cell20_171602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_171602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171602 prefixEnd_171602 := by exact prefixLift 171602
  have htrace : WordTrace (prefixWord ++ tailWord_171602) baseStart_171602 baseEnd_171602 := by
    simpa [prefixWord, tailWord_171602, baseEnd_171602] using wordTrace_append hprefix tailTrace_171602
  have hstable : (prefixWord ++ tailWord_171602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171602).length < 2 ^ (prefixWord ++ tailWord_171602).sum := by decide
  have hdescent : baseEnd_171602 < baseStart_171602 := by decide
  rcases family_descends (prefixWord ++ tailWord_171602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171619 : List Nat := [1, 1, 1, 5, 1, 3, 3, 3, 2]
def baseStart_171619 : Nat := 118140960795 + 171619 * 2 ^ 59
def prefixEnd_171619 : Nat := 4983230072969 + 3 ^ 40 * 171619 * 2
def baseEnd_171619 : Nat := 78331587950283798731773

theorem tailTrace_171619 : CollatzResearch.WordTrace tailWord_171619 prefixEnd_171619 78331587950283798731773 := by
  unfold tailWord_171619
  simp only [CollatzResearch.WordTrace]
  refine ⟨6259459165261148036805911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4172972776840765357870607 6259459165261148036805911)
  ·
    refine ⟨9389188747891722055208867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6259459165261148036805911 9389188747891722055208867)
    ·
      refine ⟨14083783121837583082813301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9389188747891722055208867 14083783121837583082813301)
      ·
        refine ⟨1320354667672273414013747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14083783121837583082813301 1320354667672273414013747)
        ·
          refine ⟨1980532001508410121020621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320354667672273414013747 1980532001508410121020621)
          ·
            refine ⟨742699500565653795382733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1980532001508410121020621 742699500565653795382733)
            ·
              refine ⟨278512312712120173268525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742699500565653795382733 278512312712120173268525)
              ·
                refine ⟨104442117267045064975697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278512312712120173268525 104442117267045064975697)
                ·
                  refine ⟨78331587950283798731773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104442117267045064975697 78331587950283798731773)
                  ·
                    rfl

theorem cell20_171619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 2].length) (baseStart_171619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171619 prefixEnd_171619 := by exact prefixLift 171619
  have htrace : WordTrace (prefixWord ++ tailWord_171619) baseStart_171619 baseEnd_171619 := by
    simpa [prefixWord, tailWord_171619, baseEnd_171619] using wordTrace_append hprefix tailTrace_171619
  have hstable : (prefixWord ++ tailWord_171619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171619).length < 2 ^ (prefixWord ++ tailWord_171619).sum := by decide
  have hdescent : baseEnd_171619 < baseStart_171619 := by decide
  rcases family_descends (prefixWord ++ tailWord_171619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171623 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_171623 : Nat := 118140960795 + 171623 * 2 ^ 59
def prefixEnd_171623 : Nat := 4983230072969 + 3 ^ 40 * 171623 * 2
def baseEnd_171623 : Nat := 78333413659277562598423

theorem tailTrace_171623 : CollatzResearch.WordTrace tailWord_171623 prefixEnd_171623 78333413659277562598423 := by
  unfold tailWord_171623
  simp only [CollatzResearch.WordTrace]
  refine ⟨6259605057246656719951523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4173070038164437813301015 6259605057246656719951523)
  ·
    refine ⟨9389407585869985079927285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6259605057246656719951523 9389407585869985079927285)
    ·
      refine ⟨880256961175311101243183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9389407585869985079927285 880256961175311101243183)
      ·
        refine ⟨1320385441762966651864775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880256961175311101243183 1320385441762966651864775)
        ·
          refine ⟨1980578162644449977797163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320385441762966651864775 1980578162644449977797163)
          ·
            refine ⟨2970867243966674966695745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980578162644449977797163 2970867243966674966695745)
            ·
              refine ⟨2228150432975006225021809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2970867243966674966695745 2228150432975006225021809)
              ·
                refine ⟨1671112824731254668766357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2228150432975006225021809 1671112824731254668766357)
                ·
                  refine ⟨78333413659277562598423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1671112824731254668766357 78333413659277562598423)
                  ·
                    rfl

theorem cell20_171623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_171623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171623 prefixEnd_171623 := by exact prefixLift 171623
  have htrace : WordTrace (prefixWord ++ tailWord_171623) baseStart_171623 baseEnd_171623 := by
    simpa [prefixWord, tailWord_171623, baseEnd_171623] using wordTrace_append hprefix tailTrace_171623
  have hstable : (prefixWord ++ tailWord_171623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171623).length < 2 ^ (prefixWord ++ tailWord_171623).sum := by decide
  have hdescent : baseEnd_171623 < baseStart_171623 := by decide
  rcases family_descends (prefixWord ++ tailWord_171623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171699 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_171699 : Nat := 118140960795 + 171699 * 2 ^ 59
def prefixEnd_171699 : Nat := 4983230072969 + 3 ^ 40 * 171699 * 2
def baseEnd_171699 : Nat := 78368102130159076064779

theorem tailTrace_171699 : CollatzResearch.WordTrace tailWord_171699 prefixEnd_171699 78368102130159076064779 := by
  unfold tailWord_171699
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262377004971321699718151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4174918003314214466478767 6262377004971321699718151)
  ·
    refine ⟨9393565507456982549577227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6262377004971321699718151 9393565507456982549577227)
    ·
      refine ⟨14090348261185473824365841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9393565507456982549577227 14090348261185473824365841)
      ·
        refine ⟨10567761195889105368274381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14090348261185473824365841 10567761195889105368274381)
        ·
          refine ⟨3962910448458414513102893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10567761195889105368274381 3962910448458414513102893)
          ·
            refine ⟨1486091418171905442413585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3962910448458414513102893 1486091418171905442413585)
            ·
              refine ⟨1114568563628929081810189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486091418171905442413585 1114568563628929081810189)
              ·
                refine ⟨417963211360848405678821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1114568563628929081810189 417963211360848405678821)
                ·
                  refine ⟨78368102130159076064779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417963211360848405678821 78368102130159076064779)
                  ·
                    rfl

theorem cell20_171699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_171699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171699 prefixEnd_171699 := by exact prefixLift 171699
  have htrace : WordTrace (prefixWord ++ tailWord_171699) baseStart_171699 baseEnd_171699 := by
    simpa [prefixWord, tailWord_171699, baseEnd_171699] using wordTrace_append hprefix tailTrace_171699
  have hstable : (prefixWord ++ tailWord_171699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171699).length < 2 ^ (prefixWord ++ tailWord_171699).sum := by decide
  have hdescent : baseEnd_171699 < baseStart_171699 := by decide
  rcases family_descends (prefixWord ++ tailWord_171699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171716 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_171716 : Nat := 118140960795 + 171716 * 2 ^ 59
def prefixEnd_171716 : Nat := 4983230072969 + 3 ^ 40 * 171716 * 2
def baseEnd_171716 : Nat := 78375861393382572498043

theorem tailTrace_171716 : CollatzResearch.WordTrace tailWord_171716 prefixEnd_171716 78375861393382572498043 := by
  unfold tailWord_171716
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131498522954866801543501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4175331363939822402058001 3131498522954866801543501)
  ·
    refine ⟨1174311946108075050578813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3131498522954866801543501 1174311946108075050578813)
    ·
      refine ⟨440366979790528143967055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1174311946108075050578813 440366979790528143967055)
      ·
        refine ⟨660550469685792215950583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440366979790528143967055 660550469685792215950583)
        ·
          refine ⟨990825704528688323925875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660550469685792215950583 990825704528688323925875)
          ·
            refine ⟨1486238556793032485888813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990825704528688323925875 1486238556793032485888813)
            ·
              refine ⟨557339458797387182208305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1486238556793032485888813 557339458797387182208305)
              ·
                refine ⟨418004594098040386656229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557339458797387182208305 418004594098040386656229)
                ·
                  refine ⟨78375861393382572498043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418004594098040386656229 78375861393382572498043)
                  ·
                    rfl

theorem cell20_171716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_171716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171716 prefixEnd_171716 := by exact prefixLift 171716
  have htrace : WordTrace (prefixWord ++ tailWord_171716) baseStart_171716 baseEnd_171716 := by
    simpa [prefixWord, tailWord_171716, baseEnd_171716] using wordTrace_append hprefix tailTrace_171716
  have hstable : (prefixWord ++ tailWord_171716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171716).length < 2 ^ (prefixWord ++ tailWord_171716).sum := by decide
  have hdescent : baseEnd_171716 < baseStart_171716 := by decide
  rcases family_descends (prefixWord ++ tailWord_171716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171740 : List Nat := [2, 2, 5, 1, 2, 1, 7]
def baseStart_171740 : Nat := 118140960795 + 171740 * 2 ^ 59
def prefixEnd_171740 : Nat := 4983230072969 + 3 ^ 40 * 171740 * 2
def baseEnd_171740 : Nat := 8709646183038350633105

theorem tailTrace_171740 : CollatzResearch.WordTrace tailWord_171740 prefixEnd_171740 8709646183038350633105 := by
  unfold tailWord_171740
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131936198911392850980337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4175914931881857134640449 3131936198911392850980337)
  ·
    refine ⟨2348952149183544638235253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3131936198911392850980337 2348952149183544638235253)
    ·
      refine ⟨220214263985957309834555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2348952149183544638235253 220214263985957309834555)
      ·
        refine ⟨330321395978935964751833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220214263985957309834555 330321395978935964751833)
        ·
          refine ⟨247741046984201973563875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330321395978935964751833 247741046984201973563875)
          ·
            refine ⟨371611570476302960345813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247741046984201973563875 371611570476302960345813)
            ·
              refine ⟨8709646183038350633105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 371611570476302960345813 8709646183038350633105)
              ·
                rfl

theorem cell20_171740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 7].length) (baseStart_171740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171740 prefixEnd_171740 := by exact prefixLift 171740
  have htrace : WordTrace (prefixWord ++ tailWord_171740) baseStart_171740 baseEnd_171740 := by
    simpa [prefixWord, tailWord_171740, baseEnd_171740] using wordTrace_append hprefix tailTrace_171740
  have hstable : (prefixWord ++ tailWord_171740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171740).length < 2 ^ (prefixWord ++ tailWord_171740).sum := by decide
  have hdescent : baseEnd_171740 < baseStart_171740 := by decide
  rcases family_descends (prefixWord ++ tailWord_171740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171747 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 5]
def baseStart_171747 : Nat := 118140960795 + 171747 * 2 ^ 59
def prefixEnd_171747 : Nat := 4983230072969 + 3 ^ 40 * 171747 * 2
def baseEnd_171747 : Nat := 78390010638084242464583

theorem tailTrace_171747 : CollatzResearch.WordTrace tailWord_171747 prefixEnd_171747 78390010638084242464583 := by
  unfold tailWord_171747
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264127708797425897465495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4176085139198283931643663 6264127708797425897465495)
  ·
    refine ⟨9396191563196138846198243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6264127708797425897465495 9396191563196138846198243)
    ·
      refine ⟨14094287344794208269297365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9396191563196138846198243 14094287344794208269297365)
      ·
        refine ⟨330334859643614256311657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14094287344794208269297365 330334859643614256311657)
        ·
          refine ⟨247751144732710692233743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330334859643614256311657 247751144732710692233743)
          ·
            refine ⟨371626717099066038350615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247751144732710692233743 371626717099066038350615)
            ·
              refine ⟨557440075648599057525923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371626717099066038350615 557440075648599057525923)
              ·
                refine ⟨836160113472898586288885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557440075648599057525923 836160113472898586288885)
                ·
                  refine ⟨78390010638084242464583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 836160113472898586288885 78390010638084242464583)
                  ·
                    rfl

theorem cell20_171747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 5].length) (baseStart_171747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171747 prefixEnd_171747 := by exact prefixLift 171747
  have htrace : WordTrace (prefixWord ++ tailWord_171747) baseStart_171747 baseEnd_171747 := by
    simpa [prefixWord, tailWord_171747, baseEnd_171747] using wordTrace_append hprefix tailTrace_171747
  have hstable : (prefixWord ++ tailWord_171747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171747).length < 2 ^ (prefixWord ++ tailWord_171747).sum := by decide
  have hdescent : baseEnd_171747 < baseStart_171747 := by decide
  rcases family_descends (prefixWord ++ tailWord_171747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171774 : List Nat := [4, 2, 2, 1, 4, 1, 2, 4]
def baseStart_171774 : Nat := 118140960795 + 171774 * 2 ^ 59
def prefixEnd_171774 : Nat := 4983230072969 + 3 ^ 40 * 171774 * 2
def baseEnd_171774 : Nat := 26134111391264049521491

theorem tailTrace_171774 : CollatzResearch.WordTrace tailWord_171774 prefixEnd_171774 26134111391264049521491 := by
  unfold tailWord_171774
  simp only [CollatzResearch.WordTrace]
  refine ⟨783139059962451188587297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4176741653133073005798917 783139059962451188587297)
  ·
    refine ⟨587354294971838391440473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 783139059962451188587297 587354294971838391440473)
    ·
      refine ⟨440515721228878793580355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 587354294971838391440473 440515721228878793580355)
      ·
        refine ⟨660773581843318190370533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440515721228878793580355 660773581843318190370533)
        ·
          refine ⟨123895046595622160694475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 660773581843318190370533 123895046595622160694475)
          ·
            refine ⟨185842569893433241041713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123895046595622160694475 185842569893433241041713)
            ·
              refine ⟨139381927420074930781285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185842569893433241041713 139381927420074930781285)
              ·
                refine ⟨26134111391264049521491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139381927420074930781285 26134111391264049521491)
                ·
                  rfl

theorem cell20_171774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_171774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171774 prefixEnd_171774 := by exact prefixLift 171774
  have htrace : WordTrace (prefixWord ++ tailWord_171774) baseStart_171774 baseEnd_171774 := by
    simpa [prefixWord, tailWord_171774, baseEnd_171774] using wordTrace_append hprefix tailTrace_171774
  have hstable : (prefixWord ++ tailWord_171774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171774).length < 2 ^ (prefixWord ++ tailWord_171774).sum := by decide
  have hdescent : baseEnd_171774 < baseStart_171774 := by decide
  rcases family_descends (prefixWord ++ tailWord_171774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171775 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_171775 : Nat := 118140960795 + 171775 * 2 ^ 59
def prefixEnd_171775 : Nat := 4983230072969 + 3 ^ 40 * 171775 * 2
def baseEnd_171775 : Nat := 78402790601040589531135

theorem tailTrace_171775 : CollatzResearch.WordTrace tailWord_171775 prefixEnd_171775 78402790601040589531135 := by
  unfold tailWord_171775
  simp only [CollatzResearch.WordTrace]
  refine ⟨6265148952695986679484779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4176765968463991119656519 6265148952695986679484779)
  ·
    refine ⟨9397723429043980019227169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6265148952695986679484779 9397723429043980019227169)
    ·
      refine ⟨7048292571782985014420377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9397723429043980019227169 7048292571782985014420377)
      ·
        refine ⟨5286219428837238760815283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7048292571782985014420377 5286219428837238760815283)
        ·
          refine ⟨7929329143255858141222925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5286219428837238760815283 7929329143255858141222925)
          ·
            refine ⟨2973498428720946802958597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7929329143255858141222925 2973498428720946802958597)
            ·
              refine ⟨557530955385177525554737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2973498428720946802958597 557530955385177525554737)
              ·
                refine ⟨418148216538883144166053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557530955385177525554737 418148216538883144166053)
                ·
                  refine ⟨78402790601040589531135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418148216538883144166053 78402790601040589531135)
                  ·
                    rfl

theorem cell20_171775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_171775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171775 prefixEnd_171775 := by exact prefixLift 171775
  have htrace : WordTrace (prefixWord ++ tailWord_171775) baseStart_171775 baseEnd_171775 := by
    simpa [prefixWord, tailWord_171775, baseEnd_171775] using wordTrace_append hprefix tailTrace_171775
  have hstable : (prefixWord ++ tailWord_171775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171775).length < 2 ^ (prefixWord ++ tailWord_171775).sum := by decide
  have hdescent : baseEnd_171775 < baseStart_171775 := by decide
  rcases family_descends (prefixWord ++ tailWord_171775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171799 : List Nat := [1, 1, 3, 4, 2, 3, 6]
def baseStart_171799 : Nat := 118140960795 + 171799 * 2 ^ 59
def prefixEnd_171799 : Nat := 4983230072969 + 3 ^ 40 * 171799 * 2
def baseEnd_171799 : Nat := 8712638317222574747893

theorem tailTrace_171799 : CollatzResearch.WordTrace tailWord_171799 prefixEnd_171799 8712638317222574747893 := by
  unfold tailWord_171799
  simp only [CollatzResearch.WordTrace]
  refine ⟨6266024304609038778358451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4177349536406025852238967 6266024304609038778358451)
  ·
    refine ⟨9399036456913558167537677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6266024304609038778358451 9399036456913558167537677)
    ·
      refine ⟨3524638671342584312826629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9399036456913558167537677 3524638671342584312826629)
      ·
        refine ⟨660869750876734558654993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3524638671342584312826629 660869750876734558654993)
        ·
          refine ⟨495652313157550918991245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 660869750876734558654993 495652313157550918991245)
          ·
            refine ⟨185869617434081594621717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 495652313157550918991245 185869617434081594621717)
            ·
              refine ⟨8712638317222574747893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185869617434081594621717 8712638317222574747893)
              ·
                rfl

theorem cell20_171799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 6].length) (baseStart_171799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171799 prefixEnd_171799 := by exact prefixLift 171799
  have htrace : WordTrace (prefixWord ++ tailWord_171799) baseStart_171799 baseEnd_171799 := by
    simpa [prefixWord, tailWord_171799, baseEnd_171799] using wordTrace_append hprefix tailTrace_171799
  have hstable : (prefixWord ++ tailWord_171799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171799).length < 2 ^ (prefixWord ++ tailWord_171799).sum := by decide
  have hdescent : baseEnd_171799 < baseStart_171799 := by decide
  rcases family_descends (prefixWord ++ tailWord_171799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171820 : List Nat := [2, 2, 1, 1, 1, 5, 1, 7]
def baseStart_171820 : Nat := 118140960795 + 171820 * 2 ^ 59
def prefixEnd_171820 : Nat := 4983230072969 + 3 ^ 40 * 171820 * 2
def baseEnd_171820 : Nat := 26141109942406811010317

theorem tailTrace_171820 : CollatzResearch.WordTrace tailWord_171820 prefixEnd_171820 26141109942406811010317 := by
  unfold tailWord_171820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3133395118766479682436457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4177860158355306243248609 3133395118766479682436457)
  ·
    refine ⟨2350046339074859761827343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3133395118766479682436457 2350046339074859761827343)
    ·
      refine ⟨3525069508612289642741015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2350046339074859761827343 3525069508612289642741015)
      ·
        refine ⟨5287604262918434464111523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3525069508612289642741015 5287604262918434464111523)
        ·
          refine ⟨7931406394377651696167285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5287604262918434464111523 7931406394377651696167285)
          ·
            refine ⟨743569349472904846515683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7931406394377651696167285 743569349472904846515683)
            ·
              refine ⟨1115354024209357269773525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743569349472904846515683 1115354024209357269773525)
              ·
                refine ⟨26141109942406811010317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1115354024209357269773525 26141109942406811010317)
                ·
                  rfl

theorem cell20_171820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_171820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171820 prefixEnd_171820 := by exact prefixLift 171820
  have htrace : WordTrace (prefixWord ++ tailWord_171820) baseStart_171820 baseEnd_171820 := by
    simpa [prefixWord, tailWord_171820, baseEnd_171820] using wordTrace_append hprefix tailTrace_171820
  have hstable : (prefixWord ++ tailWord_171820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171820).length < 2 ^ (prefixWord ++ tailWord_171820).sum := by decide
  have hdescent : baseEnd_171820 < baseStart_171820 := by decide
  rcases family_descends (prefixWord ++ tailWord_171820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171837 : List Nat := [1, 4, 1, 4, 1, 1, 2, 6]
def baseStart_171837 : Nat := 118140960795 + 171837 * 2 ^ 59
def prefixEnd_171837 : Nat := 4983230072969 + 3 ^ 40 * 171837 * 2
def baseEnd_171837 : Nat := 26143696363481309821405

theorem tailTrace_171837 : CollatzResearch.WordTrace tailWord_171837 prefixEnd_171837 26143696363481309821405 := by
  unfold tailWord_171837
  simp only [CollatzResearch.WordTrace]
  refine ⟨6267410278471371268241765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4178273518980914178827843 6267410278471371268241765)
  ·
    refine ⟨1175139427213382112795331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6267410278471371268241765 1175139427213382112795331)
    ·
      refine ⟨1762709140820073169192997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1175139427213382112795331 1762709140820073169192997)
      ·
        refine ⟨330507963903763719223687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1762709140820073169192997 330507963903763719223687)
        ·
          refine ⟨495761945855645578835531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330507963903763719223687 495761945855645578835531)
          ·
            refine ⟨743642918783468368253297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495761945855645578835531 743642918783468368253297)
            ·
              refine ⟨557732189087601276189973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743642918783468368253297 557732189087601276189973)
              ·
                refine ⟨26143696363481309821405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 557732189087601276189973 26143696363481309821405)
                ·
                  rfl

theorem cell20_171837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_171837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171837 prefixEnd_171837 := by exact prefixLift 171837
  have htrace : WordTrace (prefixWord ++ tailWord_171837) baseStart_171837 baseEnd_171837 := by
    simpa [prefixWord, tailWord_171837, baseEnd_171837] using wordTrace_append hprefix tailTrace_171837
  have hstable : (prefixWord ++ tailWord_171837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171837).length < 2 ^ (prefixWord ++ tailWord_171837).sum := by decide
  have hdescent : baseEnd_171837 < baseStart_171837 := by decide
  rcases family_descends (prefixWord ++ tailWord_171837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171858 : List Nat := [3, 2, 2, 1, 1, 11]
def baseStart_171858 : Nat := 118140960795 + 171858 * 2 ^ 59
def prefixEnd_171858 : Nat := 4983230072969 + 3 ^ 40 * 171858 * 2
def baseEnd_171858 : Nat := 2905210150468932954227

theorem tailTrace_171858 : CollatzResearch.WordTrace tailWord_171858 prefixEnd_171858 2905210150468932954227 := by
  unfold tailWord_171858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567044052848822963689057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4178784140930194569837485 1567044052848822963689057)
  ·
    refine ⟨1175283039636617222766793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1567044052848822963689057 1175283039636617222766793)
    ·
      refine ⟨881462279727462917075095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1175283039636617222766793 881462279727462917075095)
      ·
        refine ⟨1322193419591194375612643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881462279727462917075095 1322193419591194375612643)
        ·
          refine ⟨1983290129386791563418965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322193419591194375612643 1983290129386791563418965)
          ·
            refine ⟨2905210150468932954227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1983290129386791563418965 2905210150468932954227)
            ·
              rfl

theorem cell20_171858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 11].length) (baseStart_171858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171858 prefixEnd_171858 := by exact prefixLift 171858
  have htrace : WordTrace (prefixWord ++ tailWord_171858) baseStart_171858 baseEnd_171858 := by
    simpa [prefixWord, tailWord_171858, baseEnd_171858] using wordTrace_append hprefix tailTrace_171858
  have hstable : (prefixWord ++ tailWord_171858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171858).length < 2 ^ (prefixWord ++ tailWord_171858).sum := by decide
  have hdescent : baseEnd_171858 < baseStart_171858 := by decide
  rcases family_descends (prefixWord ++ tailWord_171858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171861 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 3]
def baseStart_171861 : Nat := 118140960795 + 171861 * 2 ^ 59
def prefixEnd_171861 : Nat := 4983230072969 + 3 ^ 40 * 171861 * 2
def baseEnd_171861 : Nat := 78442043344406512664117

theorem tailTrace_171861 : CollatzResearch.WordTrace tailWord_171861 prefixEnd_171861 78442043344406512664117 := by
  unfold tailWord_171861
  simp only [CollatzResearch.WordTrace]
  refine ⟨6268285630384423367115437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4178857086922948911410291 6268285630384423367115437)
  ·
    refine ⟨2350607111394158762668289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6268285630384423367115437 2350607111394158762668289)
    ·
      refine ⟨1762955333545619072001217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2350607111394158762668289 1762955333545619072001217)
      ·
        refine ⟨1322216500159214304000913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1762955333545619072001217 1322216500159214304000913)
        ·
          refine ⟨991662375119410728000685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1322216500159214304000913 991662375119410728000685)
          ·
            refine ⟨371873390669779023000257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 991662375119410728000685 371873390669779023000257)
            ·
              refine ⟨278905043002334267250193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371873390669779023000257 278905043002334267250193)
              ·
                refine ⟨209178782251750700437645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278905043002334267250193 209178782251750700437645)
                ·
                  refine ⟨78442043344406512664117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209178782251750700437645 78442043344406512664117)
                  ·
                    rfl

theorem cell20_171861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_171861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171861 prefixEnd_171861 := by exact prefixLift 171861
  have htrace : WordTrace (prefixWord ++ tailWord_171861) baseStart_171861 baseEnd_171861 := by
    simpa [prefixWord, tailWord_171861, baseEnd_171861] using wordTrace_append hprefix tailTrace_171861
  have hstable : (prefixWord ++ tailWord_171861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171861).length < 2 ^ (prefixWord ++ tailWord_171861).sum := by decide
  have hdescent : baseEnd_171861 < baseStart_171861 := by decide
  rcases family_descends (prefixWord ++ tailWord_171861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171889 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_171889 : Nat := 118140960795 + 171889 * 2 ^ 59
def prefixEnd_171889 : Nat := 4983230072969 + 3 ^ 40 * 171889 * 2
def baseEnd_171889 : Nat := 78454823307362859730669

theorem tailTrace_171889 : CollatzResearch.WordTrace tailWord_171889 prefixEnd_171889 78454823307362859730669 := by
  unfold tailWord_171889
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269306874282984149134721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4179537916188656099423147 6269306874282984149134721)
  ·
    refine ⟨4701980155712238111851041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6269306874282984149134721 4701980155712238111851041)
    ·
      refine ⟨3526485116784178583888281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4701980155712238111851041 3526485116784178583888281)
      ·
        refine ⟨2644863837588133937916211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3526485116784178583888281 2644863837588133937916211)
        ·
          refine ⟨3967295756382200906874317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644863837588133937916211 3967295756382200906874317)
          ·
            refine ⟨1487735908643325340077869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3967295756382200906874317 1487735908643325340077869)
            ·
              refine ⟨557900965741247002529201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1487735908643325340077869 557900965741247002529201)
              ·
                refine ⟨418425724305935251896901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557900965741247002529201 418425724305935251896901)
                ·
                  refine ⟨78454823307362859730669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418425724305935251896901 78454823307362859730669)
                  ·
                    rfl

theorem cell20_171889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_171889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171889 prefixEnd_171889 := by exact prefixLift 171889
  have htrace : WordTrace (prefixWord ++ tailWord_171889) baseStart_171889 baseEnd_171889 := by
    simpa [prefixWord, tailWord_171889, baseEnd_171889] using wordTrace_append hprefix tailTrace_171889
  have hstable : (prefixWord ++ tailWord_171889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171889).length < 2 ^ (prefixWord ++ tailWord_171889).sum := by decide
  have hdescent : baseEnd_171889 < baseStart_171889 := by decide
  rcases family_descends (prefixWord ++ tailWord_171889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171902 : List Nat := [4, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_171902 : Nat := 118140960795 + 171902 * 2 ^ 59
def prefixEnd_171902 : Nat := 4983230072969 + 3 ^ 40 * 171902 * 2
def baseEnd_171902 : Nat := 78460756861592592297283

theorem tailTrace_171902 : CollatzResearch.WordTrace tailWord_171902 prefixEnd_171902 78460756861592592297283 := by
  unfold tailWord_171902
  simp only [CollatzResearch.WordTrace]
  refine ⟨783722627904485921169745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4179854015490591579571973 783722627904485921169745)
  ·
    refine ⟨587791970928364440877309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 783722627904485921169745 587791970928364440877309)
    ·
      refine ⟨220421989098136665328991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 587791970928364440877309 220421989098136665328991)
      ·
        refine ⟨330632983647204997993487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220421989098136665328991 330632983647204997993487)
        ·
          refine ⟨495949475470807496990231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330632983647204997993487 495949475470807496990231)
          ·
            refine ⟨743924213206211245485347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495949475470807496990231 743924213206211245485347)
            ·
              refine ⟨1115886319809316868228021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743924213206211245485347 1115886319809316868228021)
              ·
                refine ⟨104614342482123456396377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1115886319809316868228021 104614342482123456396377)
                ·
                  refine ⟨78460756861592592297283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104614342482123456396377 78460756861592592297283)
                  ·
                    rfl

theorem cell20_171902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_171902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171902 prefixEnd_171902 := by exact prefixLift 171902
  have htrace : WordTrace (prefixWord ++ tailWord_171902) baseStart_171902 baseEnd_171902 := by
    simpa [prefixWord, tailWord_171902, baseEnd_171902] using wordTrace_append hprefix tailTrace_171902
  have hstable : (prefixWord ++ tailWord_171902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171902).length < 2 ^ (prefixWord ++ tailWord_171902).sum := by decide
  have hdescent : baseEnd_171902 < baseStart_171902 := by decide
  rcases family_descends (prefixWord ++ tailWord_171902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171903 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_171903 : Nat := 118140960795 + 171903 * 2 ^ 59
def prefixEnd_171903 : Nat := 4983230072969 + 3 ^ 40 * 171903 * 2
def baseEnd_171903 : Nat := 78461213288841033263945

theorem tailTrace_171903 : CollatzResearch.WordTrace tailWord_171903 prefixEnd_171903 78461213288841033263945 := by
  unfold tailWord_171903
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269817496232264540144363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4179878330821509693429575 6269817496232264540144363)
  ·
    refine ⟨9404726244348396810216545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6269817496232264540144363 9404726244348396810216545)
    ·
      refine ⟨7053544683261297607662409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9404726244348396810216545 7053544683261297607662409)
      ·
        refine ⟨5290158512445973205746807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7053544683261297607662409 5290158512445973205746807)
        ·
          refine ⟨7935237768668959808620211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5290158512445973205746807 7935237768668959808620211)
          ·
            refine ⟨11902856653003439712930317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7935237768668959808620211 11902856653003439712930317)
            ·
              refine ⟨4463571244876289892348869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11902856653003439712930317 4463571244876289892348869)
              ·
                refine ⟨836919608414304354815413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4463571244876289892348869 836919608414304354815413)
                ·
                  refine ⟨78461213288841033263945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 836919608414304354815413 78461213288841033263945)
                  ·
                    rfl

theorem cell20_171903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_171903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171903 prefixEnd_171903 := by exact prefixLift 171903
  have htrace : WordTrace (prefixWord ++ tailWord_171903) baseStart_171903 baseEnd_171903 := by
    simpa [prefixWord, tailWord_171903, baseEnd_171903] using wordTrace_append hprefix tailTrace_171903
  have hstable : (prefixWord ++ tailWord_171903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171903).length < 2 ^ (prefixWord ++ tailWord_171903).sum := by decide
  have hdescent : baseEnd_171903 < baseStart_171903 := by decide
  rcases family_descends (prefixWord ++ tailWord_171903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171927 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_171927 : Nat := 118140960795 + 171927 * 2 ^ 59
def prefixEnd_171927 : Nat := 4983230072969 + 3 ^ 40 * 171927 * 2
def baseEnd_171927 : Nat := 78472167542803616463847

theorem tailTrace_171927 : CollatzResearch.WordTrace tailWord_171927 prefixEnd_171927 78472167542803616463847 := by
  unfold tailWord_171927
  simp only [CollatzResearch.WordTrace]
  refine ⟨6270692848145316639018035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4180461898763544426012023 6270692848145316639018035)
  ·
    refine ⟨9406039272217974958527053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6270692848145316639018035 9406039272217974958527053)
    ·
      refine ⟨3527264727081740609447645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9406039272217974958527053 3527264727081740609447645)
      ·
        refine ⟨1322724272655652728542867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3527264727081740609447645 1322724272655652728542867)
        ·
          refine ⟨1984086408983479092814301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322724272655652728542867 1984086408983479092814301)
          ·
            refine ⟨744032403368804659805363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1984086408983479092814301 744032403368804659805363)
            ·
              refine ⟨1116048605053206989708045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744032403368804659805363 1116048605053206989708045)
              ·
                refine ⟨418518226894952621140517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1116048605053206989708045 418518226894952621140517)
                ·
                  refine ⟨78472167542803616463847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418518226894952621140517 78472167542803616463847)
                  ·
                    rfl

theorem cell20_171927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_171927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171927 prefixEnd_171927 := by exact prefixLift 171927
  have htrace : WordTrace (prefixWord ++ tailWord_171927) baseStart_171927 baseEnd_171927 := by
    simpa [prefixWord, tailWord_171927, baseEnd_171927] using wordTrace_append hprefix tailTrace_171927
  have hstable : (prefixWord ++ tailWord_171927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171927).length < 2 ^ (prefixWord ++ tailWord_171927).sum := by decide
  have hdescent : baseEnd_171927 < baseStart_171927 := by decide
  rcases family_descends (prefixWord ++ tailWord_171927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171979 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_171979 : Nat := 118140960795 + 171979 * 2 ^ 59
def prefixEnd_171979 : Nat := 4983230072969 + 3 ^ 40 * 171979 * 2
def baseEnd_171979 : Nat := 78495901759722546730301

theorem tailTrace_171979 : CollatzResearch.WordTrace tailWord_171979 prefixEnd_171979 78495901759722546730301 := by
  unfold tailWord_171979
  simp only [CollatzResearch.WordTrace]
  refine ⟨6272589443956929519910991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4181726295971286346607327 6272589443956929519910991)
  ·
    refine ⟨9408884165935394279866487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6272589443956929519910991 9408884165935394279866487)
    ·
      refine ⟨14113326248903091419799731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9408884165935394279866487 14113326248903091419799731)
      ·
        refine ⟨21169989373354637129699597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14113326248903091419799731 21169989373354637129699597)
        ·
          refine ⟨7938746015007988923637349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21169989373354637129699597 7938746015007988923637349)
          ·
            refine ⟨1488514877813997923182003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7938746015007988923637349 1488514877813997923182003)
            ·
              refine ⟨2232772316720996884773005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488514877813997923182003 2232772316720996884773005)
              ·
                refine ⟨837289618770373831789877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2232772316720996884773005 837289618770373831789877)
                ·
                  refine ⟨78495901759722546730301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 837289618770373831789877 78495901759722546730301)
                  ·
                    rfl

theorem cell20_171979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_171979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171979 prefixEnd_171979 := by exact prefixLift 171979
  have htrace : WordTrace (prefixWord ++ tailWord_171979) baseStart_171979 baseEnd_171979 := by
    simpa [prefixWord, tailWord_171979, baseEnd_171979] using wordTrace_append hprefix tailTrace_171979
  have hstable : (prefixWord ++ tailWord_171979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171979).length < 2 ^ (prefixWord ++ tailWord_171979).sum := by decide
  have hdescent : baseEnd_171979 < baseStart_171979 := by decide
  rcases family_descends (prefixWord ++ tailWord_171979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171989 : List Nat := [1, 3, 2, 3, 2, 2, 2, 5]
def baseStart_171989 : Nat := 118140960795 + 171989 * 2 ^ 59
def prefixEnd_171989 : Nat := 4983230072969 + 3 ^ 40 * 171989 * 2
def baseEnd_171989 : Nat := 26166822010735652132309

theorem tailTrace_171989 : CollatzResearch.WordTrace tailWord_171989 prefixEnd_171989 26166822010735652132309 := by
  unfold tailWord_171989
  simp only [CollatzResearch.WordTrace]
  refine ⟨6272954173920701227775021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4181969449280467485183347 6272954173920701227775021)
  ·
    refine ⟨2352357815220262960415633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6272954173920701227775021 2352357815220262960415633)
    ·
      refine ⟨1764268361415197220311725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2352357815220262960415633 1764268361415197220311725)
      ·
        refine ⟨661600635530698957616897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1764268361415197220311725 661600635530698957616897)
        ·
          refine ⟨496200476648024218212673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661600635530698957616897 496200476648024218212673)
          ·
            refine ⟨372150357486018163659505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496200476648024218212673 372150357486018163659505)
            ·
              refine ⟨279112768114513622744629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372150357486018163659505 279112768114513622744629)
              ·
                refine ⟨26166822010735652132309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 279112768114513622744629 26166822010735652132309)
                ·
                  rfl

theorem cell20_171989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_171989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_171989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_171989 prefixEnd_171989 := by exact prefixLift 171989
  have htrace : WordTrace (prefixWord ++ tailWord_171989) baseStart_171989 baseEnd_171989 := by
    simpa [prefixWord, tailWord_171989, baseEnd_171989] using wordTrace_append hprefix tailTrace_171989
  have hstable : (prefixWord ++ tailWord_171989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171989).length < 2 ^ (prefixWord ++ tailWord_171989).sum := by decide
  have hdescent : baseEnd_171989 < baseStart_171989 := by decide
  rcases family_descends (prefixWord ++ tailWord_171989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172010 : List Nat := [3, 1, 3, 1, 2, 1, 1, 8]
def baseStart_172010 : Nat := 118140960795 + 172010 * 2 ^ 59
def prefixEnd_172010 : Nat := 4983230072969 + 3 ^ 40 * 172010 * 2
def baseEnd_172010 : Nat := 26170017001474738898947

theorem tailTrace_172010 : CollatzResearch.WordTrace tailWord_172010 prefixEnd_172010 26170017001474738898947 := by
  unfold tailWord_172010
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568430026711155453572371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4182480071229747876192989 1568430026711155453572371)
  ·
    refine ⟨2352645040066733180358557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1568430026711155453572371 2352645040066733180358557)
    ·
      refine ⟨882241890025024942634459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2352645040066733180358557 882241890025024942634459)
      ·
        refine ⟨1323362835037537413951689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882241890025024942634459 1323362835037537413951689)
        ·
          refine ⟨992522126278153060463767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1323362835037537413951689 992522126278153060463767)
          ·
            refine ⟨1488783189417229590695651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992522126278153060463767 1488783189417229590695651)
            ·
              refine ⟨2233174784125844386043477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488783189417229590695651 2233174784125844386043477)
              ·
                refine ⟨26170017001474738898947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2233174784125844386043477 26170017001474738898947)
                ·
                  rfl

theorem cell20_172010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_172010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172010 prefixEnd_172010 := by exact prefixLift 172010
  have htrace : WordTrace (prefixWord ++ tailWord_172010) baseStart_172010 baseEnd_172010 := by
    simpa [prefixWord, tailWord_172010, baseEnd_172010] using wordTrace_append hprefix tailTrace_172010
  have hstable : (prefixWord ++ tailWord_172010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172010).length < 2 ^ (prefixWord ++ tailWord_172010).sum := by decide
  have hdescent : baseEnd_172010 < baseStart_172010 := by decide
  rcases family_descends (prefixWord ++ tailWord_172010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172030 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_172030 : Nat := 118140960795 + 172030 * 2 ^ 59
def prefixEnd_172030 : Nat := 4983230072969 + 3 ^ 40 * 172030 * 2
def baseEnd_172030 : Nat := 78519179549393036030093

theorem tailTrace_172030 : CollatzResearch.WordTrace tailWord_172030 prefixEnd_172030 78519179549393036030093 := by
  unfold tailWord_172030
  simp only [CollatzResearch.WordTrace]
  refine ⟨784306195846520653752193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4182966377848110153345029 784306195846520653752193)
  ·
    refine ⟨588229646884890490314145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 784306195846520653752193 588229646884890490314145)
    ·
      refine ⟨441172235163667867735609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 588229646884890490314145 441172235163667867735609)
      ·
        refine ⟨330879176372750900801707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441172235163667867735609 330879176372750900801707)
        ·
          refine ⟨496318764559126351202561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330879176372750900801707 496318764559126351202561)
          ·
            refine ⟨372239073419344763401921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496318764559126351202561 372239073419344763401921)
            ·
              refine ⟨279179305064508572551441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372239073419344763401921 279179305064508572551441)
              ·
                refine ⟨209384478798381429413581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279179305064508572551441 209384478798381429413581)
                ·
                  refine ⟨78519179549393036030093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209384478798381429413581 78519179549393036030093)
                  ·
                    rfl

theorem cell20_172030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_172030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172030 prefixEnd_172030 := by exact prefixLift 172030
  have htrace : WordTrace (prefixWord ++ tailWord_172030) baseStart_172030 baseEnd_172030 := by
    simpa [prefixWord, tailWord_172030, baseEnd_172030] using wordTrace_append hprefix tailTrace_172030
  have hstable : (prefixWord ++ tailWord_172030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172030).length < 2 ^ (prefixWord ++ tailWord_172030).sum := by decide
  have hdescent : baseEnd_172030 < baseStart_172030 := by decide
  rcases family_descends (prefixWord ++ tailWord_172030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172037 : List Nat := [1, 3, 1, 1, 2, 4, 4, 2, 2]
def baseStart_172037 : Nat := 118140960795 + 172037 * 2 ^ 59
def prefixEnd_172037 : Nat := 4983230072969 + 3 ^ 40 * 172037 * 2
def baseEnd_172037 : Nat := 78522374540132122796731

theorem tailTrace_172037 : CollatzResearch.WordTrace tailWord_172037 prefixEnd_172037 78522374540132122796731 := by
  unfold tailWord_172037
  simp only [CollatzResearch.WordTrace]
  refine ⟨6274704877746805425522365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4183136585164536950348243 6274704877746805425522365)
  ·
    refine ⟨2353014329155052034570887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6274704877746805425522365 2353014329155052034570887)
    ·
      refine ⟨3529521493732578051856331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2353014329155052034570887 3529521493732578051856331)
      ·
        refine ⟨5294282240598867077784497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3529521493732578051856331 5294282240598867077784497)
        ·
          refine ⟨3970711680449150308338373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5294282240598867077784497 3970711680449150308338373)
          ·
            refine ⟨744508440084215682813445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3970711680449150308338373 744508440084215682813445)
            ·
              refine ⟨139595332515790440527521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 744508440084215682813445 139595332515790440527521)
              ·
                refine ⟨104696499386842830395641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139595332515790440527521 104696499386842830395641)
                ·
                  refine ⟨78522374540132122796731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104696499386842830395641 78522374540132122796731)
                  ·
                    rfl

theorem cell20_172037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_172037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172037 prefixEnd_172037 := by exact prefixLift 172037
  have htrace : WordTrace (prefixWord ++ tailWord_172037) baseStart_172037 baseEnd_172037 := by
    simpa [prefixWord, tailWord_172037, baseEnd_172037] using wordTrace_append hprefix tailTrace_172037
  have hstable : (prefixWord ++ tailWord_172037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172037).length < 2 ^ (prefixWord ++ tailWord_172037).sum := by decide
  have hdescent : baseEnd_172037 < baseStart_172037 := by decide
  rcases family_descends (prefixWord ++ tailWord_172037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172096 : List Nat := [2, 1, 1, 2, 2, 4, 2, 4, 2]
def baseStart_172096 : Nat := 118140960795 + 172096 * 2 ^ 59
def prefixEnd_172096 : Nat := 4983230072969 + 3 ^ 40 * 172096 * 2
def baseEnd_172096 : Nat := 78549303747790139829823

theorem tailTrace_172096 : CollatzResearch.WordTrace tailWord_172096 prefixEnd_172096 78549303747790139829823 := by
  unfold tailWord_172096
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138428392266529250960071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4184571189688705667946761 3138428392266529250960071)
  ·
    refine ⟨4707642588399793876440107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3138428392266529250960071 4707642588399793876440107)
    ·
      refine ⟨7061463882599690814660161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4707642588399793876440107 7061463882599690814660161)
      ·
        refine ⟨5296097911949768110995121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7061463882599690814660161 5296097911949768110995121)
        ·
          refine ⟨3972073433962326083246341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5296097911949768110995121 3972073433962326083246341)
          ·
            refine ⟨744763768867936140608689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3972073433962326083246341 744763768867936140608689)
            ·
              refine ⟨558572826650952105456517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744763768867936140608689 558572826650952105456517)
              ·
                refine ⟨104732404997053519773097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 558572826650952105456517 104732404997053519773097)
                ·
                  refine ⟨78549303747790139829823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104732404997053519773097 78549303747790139829823)
                  ·
                    rfl

theorem cell20_172096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_172096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172096 prefixEnd_172096 := by exact prefixLift 172096
  have htrace : WordTrace (prefixWord ++ tailWord_172096) baseStart_172096 baseEnd_172096 := by
    simpa [prefixWord, tailWord_172096, baseEnd_172096] using wordTrace_append hprefix tailTrace_172096
  have hstable : (prefixWord ++ tailWord_172096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172096).length < 2 ^ (prefixWord ++ tailWord_172096).sum := by decide
  have hdescent : baseEnd_172096 < baseStart_172096 := by decide
  rcases family_descends (prefixWord ++ tailWord_172096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172117 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_172117 : Nat := 118140960795 + 172117 * 2 ^ 59
def prefixEnd_172117 : Nat := 4983230072969 + 3 ^ 40 * 172117 * 2
def baseEnd_172117 : Nat := 78558888720007400129737

theorem tailTrace_172117 : CollatzResearch.WordTrace tailWord_172117 prefixEnd_172117 78558888720007400129737 := by
  unfold tailWord_172117
  simp only [CollatzResearch.WordTrace]
  refine ⟨6277622717456979088434605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4185081811637986058956403 6277622717456979088434605)
  ·
    refine ⟨2354108519046367158162977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6277622717456979088434605 2354108519046367158162977)
    ·
      refine ⟨1765581389284775368622233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2354108519046367158162977 1765581389284775368622233)
      ·
        refine ⟨1324186041963581526466675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1765581389284775368622233 1324186041963581526466675)
        ·
          refine ⟨1986279062945372289700013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1324186041963581526466675 1986279062945372289700013)
          ·
            refine ⟨744854648604514608637505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1986279062945372289700013 744854648604514608637505)
            ·
              refine ⟨558640986453385956478129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744854648604514608637505 558640986453385956478129)
              ·
                refine ⟨418980739840039467358597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558640986453385956478129 418980739840039467358597)
                ·
                  refine ⟨78558888720007400129737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418980739840039467358597 78558888720007400129737)
                  ·
                    rfl

theorem cell20_172117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_172117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172117 prefixEnd_172117 := by exact prefixLift 172117
  have htrace : WordTrace (prefixWord ++ tailWord_172117) baseStart_172117 baseEnd_172117 := by
    simpa [prefixWord, tailWord_172117, baseEnd_172117] using wordTrace_append hprefix tailTrace_172117
  have hstable : (prefixWord ++ tailWord_172117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172117).length < 2 ^ (prefixWord ++ tailWord_172117).sum := by decide
  have hdescent : baseEnd_172117 < baseStart_172117 := by decide
  rcases family_descends (prefixWord ++ tailWord_172117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172126 : List Nat := [4, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_172126 : Nat := 118140960795 + 172126 * 2 ^ 59
def prefixEnd_172126 : Nat := 4983230072969 + 3 ^ 40 * 172126 * 2
def baseEnd_172126 : Nat := 78562996565243368829701

theorem tailTrace_172126 : CollatzResearch.WordTrace tailWord_172126 prefixEnd_172126 78562996565243368829701 := by
  unfold tailWord_172126
  simp only [CollatzResearch.WordTrace]
  refine ⟨784743871803046703189029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4185300649616249083674821 784743871803046703189029)
  ·
    refine ⟨147139475963071256847943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 784743871803046703189029 147139475963071256847943)
    ·
      refine ⟨220709213944606885271915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147139475963071256847943 220709213944606885271915)
      ·
        refine ⟨331063820916910327907873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220709213944606885271915 331063820916910327907873)
        ·
          refine ⟨248297865687682745930905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331063820916910327907873 248297865687682745930905)
          ·
            refine ⟨186223399265762059448179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248297865687682745930905 186223399265762059448179)
            ·
              refine ⟨279335098898643089172269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186223399265762059448179 279335098898643089172269)
              ·
                refine ⟨104750662086991158439601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279335098898643089172269 104750662086991158439601)
                ·
                  refine ⟨78562996565243368829701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104750662086991158439601 78562996565243368829701)
                  ·
                    rfl

theorem cell20_172126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_172126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172126 prefixEnd_172126 := by exact prefixLift 172126
  have htrace : WordTrace (prefixWord ++ tailWord_172126) baseStart_172126 baseEnd_172126 := by
    simpa [prefixWord, tailWord_172126, baseEnd_172126] using wordTrace_append hprefix tailTrace_172126
  have hstable : (prefixWord ++ tailWord_172126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172126).length < 2 ^ (prefixWord ++ tailWord_172126).sum := by decide
  have hdescent : baseEnd_172126 < baseStart_172126 := by decide
  rcases family_descends (prefixWord ++ tailWord_172126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172131 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_172131 : Nat := 118140960795 + 172131 * 2 ^ 59
def prefixEnd_172131 : Nat := 4983230072969 + 3 ^ 40 * 172131 * 2
def baseEnd_172131 : Nat := 78565278701485573663013

theorem tailTrace_172131 : CollatzResearch.WordTrace tailWord_172131 prefixEnd_172131 78565278701485573663013 := by
  unfold tailWord_172131
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278133339406259479444247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4185422226270839652962831 6278133339406259479444247)
  ·
    refine ⟨9417200009109389219166371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6278133339406259479444247 9417200009109389219166371)
    ·
      refine ⟨14125800013664083828749557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9417200009109389219166371 14125800013664083828749557)
      ·
        refine ⟨1324293751281007858945271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14125800013664083828749557 1324293751281007858945271)
        ·
          refine ⟨1986440626921511788417907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1324293751281007858945271 1986440626921511788417907)
          ·
            refine ⟨2979660940382267682626861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1986440626921511788417907 2979660940382267682626861)
            ·
              refine ⟨1117372852643350380985073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2979660940382267682626861 1117372852643350380985073)
              ·
                refine ⟨838029639482512785738805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117372852643350380985073 838029639482512785738805)
                ·
                  refine ⟨78565278701485573663013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 838029639482512785738805 78565278701485573663013)
                  ·
                    rfl

theorem cell20_172131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_172131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172131 prefixEnd_172131 := by exact prefixLift 172131
  have htrace : WordTrace (prefixWord ++ tailWord_172131) baseStart_172131 baseEnd_172131 := by
    simpa [prefixWord, tailWord_172131, baseEnd_172131] using wordTrace_append hprefix tailTrace_172131
  have hstable : (prefixWord ++ tailWord_172131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172131).length < 2 ^ (prefixWord ++ tailWord_172131).sum := by decide
  have hdescent : baseEnd_172131 < baseStart_172131 := by decide
  rcases family_descends (prefixWord ++ tailWord_172131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172151 : List Nat := [1, 1, 3, 1, 1, 6, 3, 2, 2]
def baseStart_172151 : Nat := 118140960795 + 172151 * 2 ^ 59
def prefixEnd_172151 : Nat := 4983230072969 + 3 ^ 40 * 172151 * 2
def baseEnd_172151 : Nat := 78574407246454392996265

theorem tailTrace_172151 : CollatzResearch.WordTrace tailWord_172151 prefixEnd_172151 78574407246454392996265 := by
  unfold tailWord_172151
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278862799333802895172307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4185908532889201930114871 6278862799333802895172307)
  ·
    refine ⟨9418294199000704342758461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6278862799333802895172307 9418294199000704342758461)
    ·
      refine ⟨3531860324625264128534423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9418294199000704342758461 3531860324625264128534423)
      ·
        refine ⟨5297790486937896192801635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531860324625264128534423 5297790486937896192801635)
        ·
          refine ⟨7946685730406844289202453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5297790486937896192801635 7946685730406844289202453)
          ·
            refine ⟨372500893612820826056365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7946685730406844289202453 372500893612820826056365)
            ·
              refine ⟨139687835104807809771137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372500893612820826056365 139687835104807809771137)
              ·
                refine ⟨104765876328605857328353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139687835104807809771137 104765876328605857328353)
                ·
                  refine ⟨78574407246454392996265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104765876328605857328353 78574407246454392996265)
                  ·
                    rfl

theorem cell20_172151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 2].length) (baseStart_172151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172151 prefixEnd_172151 := by exact prefixLift 172151
  have htrace : WordTrace (prefixWord ++ tailWord_172151) baseStart_172151 baseEnd_172151 := by
    simpa [prefixWord, tailWord_172151, baseEnd_172151] using wordTrace_append hprefix tailTrace_172151
  have hstable : (prefixWord ++ tailWord_172151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172151).length < 2 ^ (prefixWord ++ tailWord_172151).sum := by decide
  have hdescent : baseEnd_172151 < baseStart_172151 := by decide
  rcases family_descends (prefixWord ++ tailWord_172151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172161 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 3]
def baseStart_172161 : Nat := 118140960795 + 172161 * 2 ^ 59
def prefixEnd_172161 : Nat := 4983230072969 + 3 ^ 40 * 172161 * 2
def baseEnd_172161 : Nat := 78578971518938802662891

theorem tailTrace_172161 : CollatzResearch.WordTrace tailWord_172161 prefixEnd_172161 78578971518938802662891 := by
  unfold tailWord_172161
  simp only [CollatzResearch.WordTrace]
  refine ⟨6279227529297574603036337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4186151686198383068690891 6279227529297574603036337)
  ·
    refine ⟨4709420646973180952277253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6279227529297574603036337 4709420646973180952277253)
    ·
      refine ⟨883016371307471428551985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4709420646973180952277253 883016371307471428551985)
      ·
        refine ⟨662262278480603571413989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 883016371307471428551985 662262278480603571413989)
        ·
          refine ⟨124174177215113169640123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 662262278480603571413989 124174177215113169640123)
          ·
            refine ⟨186261265822669754460185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124174177215113169640123 186261265822669754460185)
            ·
              refine ⟨139695949367002315845139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186261265822669754460185 139695949367002315845139)
              ·
                refine ⟨209543924050503473767709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139695949367002315845139 209543924050503473767709)
                ·
                  refine ⟨78578971518938802662891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209543924050503473767709 78578971518938802662891)
                  ·
                    rfl

theorem cell20_172161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_172161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172161 prefixEnd_172161 := by exact prefixLift 172161
  have htrace : WordTrace (prefixWord ++ tailWord_172161) baseStart_172161 baseEnd_172161 := by
    simpa [prefixWord, tailWord_172161, baseEnd_172161] using wordTrace_append hprefix tailTrace_172161
  have hstable : (prefixWord ++ tailWord_172161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172161).length < 2 ^ (prefixWord ++ tailWord_172161).sum := by decide
  have hdescent : baseEnd_172161 < baseStart_172161 := by decide
  rcases family_descends (prefixWord ++ tailWord_172161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172165 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 3]
def baseStart_172165 : Nat := 118140960795 + 172165 * 2 ^ 59
def prefixEnd_172165 : Nat := 4983230072969 + 3 ^ 40 * 172165 * 2
def baseEnd_172165 : Nat := 78580797227932566529541

theorem tailTrace_172165 : CollatzResearch.WordTrace tailWord_172165 prefixEnd_172165 78580797227932566529541 := by
  unfold tailWord_172165
  simp only [CollatzResearch.WordTrace]
  refine ⟨6279373421283083286181949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4186248947522055524121299 6279373421283083286181949)
  ·
    refine ⟨2354765032981156232318231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6279373421283083286181949 2354765032981156232318231)
    ·
      refine ⟨3532147549471734348477347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354765032981156232318231 3532147549471734348477347)
      ·
        refine ⟨5298221324207601522716021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3532147549471734348477347 5298221324207601522716021)
        ·
          refine ⟨496708249144462642754627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5298221324207601522716021 496708249144462642754627)
          ·
            refine ⟨745062373716693964131941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496708249144462642754627 745062373716693964131941)
            ·
              refine ⟨139699195071880118274739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 745062373716693964131941 139699195071880118274739)
              ·
                refine ⟨209548792607820177412109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139699195071880118274739 209548792607820177412109)
                ·
                  refine ⟨78580797227932566529541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209548792607820177412109 78580797227932566529541)
                  ·
                    rfl

theorem cell20_172165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_172165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172165 prefixEnd_172165 := by exact prefixLift 172165
  have htrace : WordTrace (prefixWord ++ tailWord_172165) baseStart_172165 baseEnd_172165 := by
    simpa [prefixWord, tailWord_172165, baseEnd_172165] using wordTrace_append hprefix tailTrace_172165
  have hstable : (prefixWord ++ tailWord_172165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172165).length < 2 ^ (prefixWord ++ tailWord_172165).sum := by decide
  have hdescent : baseEnd_172165 < baseStart_172165 := by decide
  rcases family_descends (prefixWord ++ tailWord_172165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172176 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_172176 : Nat := 118140960795 + 172176 * 2 ^ 59
def prefixEnd_172176 : Nat := 4983230072969 + 3 ^ 40 * 172176 * 2
def baseEnd_172176 : Nat := 78585817927665417162829

theorem tailTrace_172176 : CollatzResearch.WordTrace tailWord_172176 prefixEnd_172176 78585817927665417162829 := by
  unfold tailWord_172176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3139887312121616082416191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4186516416162154776554921 3139887312121616082416191)
  ·
    refine ⟨4709830968182424123624287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3139887312121616082416191 4709830968182424123624287)
    ·
      refine ⟨7064746452273636185436431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4709830968182424123624287 7064746452273636185436431)
      ·
        refine ⟨10597119678410454278154647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7064746452273636185436431 10597119678410454278154647)
        ·
          refine ⟨15895679517615681417231971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10597119678410454278154647 15895679517615681417231971)
          ·
            refine ⟨23843519276423522125847957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15895679517615681417231971 23843519276423522125847957)
            ·
              refine ⟨1117664966082352599649123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23843519276423522125847957 1117664966082352599649123)
              ·
                refine ⟨1676497449123528899473685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117664966082352599649123 1676497449123528899473685)
                ·
                  refine ⟨78585817927665417162829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1676497449123528899473685 78585817927665417162829)
                  ·
                    rfl

theorem cell20_172176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_172176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172176 prefixEnd_172176 := by exact prefixLift 172176
  have htrace : WordTrace (prefixWord ++ tailWord_172176) baseStart_172176 baseEnd_172176 := by
    simpa [prefixWord, tailWord_172176, baseEnd_172176] using wordTrace_append hprefix tailTrace_172176
  have hstable : (prefixWord ++ tailWord_172176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172176).length < 2 ^ (prefixWord ++ tailWord_172176).sum := by decide
  have hdescent : baseEnd_172176 < baseStart_172176 := by decide
  rcases family_descends (prefixWord ++ tailWord_172176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172202 : List Nat := [3, 1, 5, 1, 3, 1, 2, 2, 2]
def baseStart_172202 : Nat := 118140960795 + 172202 * 2 ^ 59
def prefixEnd_172202 : Nat := 4983230072969 + 3 ^ 40 * 172202 * 2
def baseEnd_172202 : Nat := 78597685036124882296057

theorem tailTrace_172202 : CollatzResearch.WordTrace tailWord_172202 prefixEnd_172202 78597685036124882296057 := by
  unfold tailWord_172202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570180730537259651319715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4187148614766025736852573 1570180730537259651319715)
  ·
    refine ⟨2355271095805889476979573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1570180730537259651319715 2355271095805889476979573)
    ·
      refine ⟨220806665231802138466835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2355271095805889476979573 220806665231802138466835)
      ·
        refine ⟨331209997847703207700253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220806665231802138466835 331209997847703207700253)
        ·
          refine ⟨124203749192888702887595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331209997847703207700253 124203749192888702887595)
          ·
            refine ⟨186305623789333054331393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124203749192888702887595 186305623789333054331393)
            ·
              refine ⟨139729217841999790748545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186305623789333054331393 139729217841999790748545)
              ·
                refine ⟨104796913381499843061409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139729217841999790748545 104796913381499843061409)
                ·
                  refine ⟨78597685036124882296057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104796913381499843061409 78597685036124882296057)
                  ·
                    rfl

theorem cell20_172202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_172202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172202 prefixEnd_172202 := by exact prefixLift 172202
  have htrace : WordTrace (prefixWord ++ tailWord_172202) baseStart_172202 baseEnd_172202 := by
    simpa [prefixWord, tailWord_172202, baseEnd_172202] using wordTrace_append hprefix tailTrace_172202
  have hstable : (prefixWord ++ tailWord_172202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172202).length < 2 ^ (prefixWord ++ tailWord_172202).sum := by decide
  have hdescent : baseEnd_172202 < baseStart_172202 := by decide
  rcases family_descends (prefixWord ++ tailWord_172202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172210 : List Nat := [3, 2, 1, 1, 1, 3, 3, 4, 2]
def baseStart_172210 : Nat := 118140960795 + 172210 * 2 ^ 59
def prefixEnd_172210 : Nat := 4983230072969 + 3 ^ 40 * 172210 * 2
def baseEnd_172210 : Nat := 78601336454112410029357

theorem tailTrace_172210 : CollatzResearch.WordTrace tailWord_172210 prefixEnd_172210 78601336454112410029357 := by
  unfold tailWord_172210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570253676530013992892521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4187343137413370647713389 1570253676530013992892521)
  ·
    refine ⟨1177690257397510494669391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1570253676530013992892521 1177690257397510494669391)
    ·
      refine ⟨1766535386096265742004087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177690257397510494669391 1766535386096265742004087)
      ·
        refine ⟨2649803079144398613006131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766535386096265742004087 2649803079144398613006131)
        ·
          refine ⟨3974704618716597919509197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649803079144398613006131 3974704618716597919509197)
          ·
            refine ⟨1490514232018724219815949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3974704618716597919509197 1490514232018724219815949)
            ·
              refine ⟨558942837007021582430981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1490514232018724219815949 558942837007021582430981)
              ·
                refine ⟨104801781938816546705809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 558942837007021582430981 104801781938816546705809)
                ·
                  refine ⟨78601336454112410029357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104801781938816546705809 78601336454112410029357)
                  ·
                    rfl

theorem cell20_172210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_172210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172210 prefixEnd_172210 := by exact prefixLift 172210
  have htrace : WordTrace (prefixWord ++ tailWord_172210) baseStart_172210 baseEnd_172210 := by
    simpa [prefixWord, tailWord_172210, baseEnd_172210] using wordTrace_append hprefix tailTrace_172210
  have hstable : (prefixWord ++ tailWord_172210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172210).length < 2 ^ (prefixWord ++ tailWord_172210).sum := by decide
  have hdescent : baseEnd_172210 < baseStart_172210 := by decide
  rcases family_descends (prefixWord ++ tailWord_172210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172213 : List Nat := [1, 3, 3, 4, 2, 1, 1, 5]
def baseStart_172213 : Nat := 118140960795 + 172213 * 2 ^ 59
def prefixEnd_172213 : Nat := 4983230072969 + 3 ^ 40 * 172213 * 2
def baseEnd_172213 : Nat := 26200901911952577643115

theorem tailTrace_172213 : CollatzResearch.WordTrace tailWord_172213 prefixEnd_172213 26200901911952577643115 := by
  unfold tailWord_172213
  simp only [CollatzResearch.WordTrace]
  refine ⟨6281124125109187483929293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4187416083406124989286195 6281124125109187483929293)
  ·
    refine ⟨2355421546915945306473485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6281124125109187483929293 2355421546915945306473485)
    ·
      refine ⟨883283080093479489927557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2355421546915945306473485 883283080093479489927557)
      ·
        refine ⟨165615577517527404361417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 883283080093479489927557 165615577517527404361417)
        ·
          refine ⟨124211683138145553271063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165615577517527404361417 124211683138145553271063)
          ·
            refine ⟨186317524707218329906595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124211683138145553271063 186317524707218329906595)
            ·
              refine ⟨279476287060827494859893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186317524707218329906595 279476287060827494859893)
              ·
                refine ⟨26200901911952577643115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 279476287060827494859893 26200901911952577643115)
                ·
                  rfl

theorem cell20_172213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 5].length) (baseStart_172213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172213 prefixEnd_172213 := by exact prefixLift 172213
  have htrace : WordTrace (prefixWord ++ tailWord_172213) baseStart_172213 baseEnd_172213 := by
    simpa [prefixWord, tailWord_172213, baseEnd_172213] using wordTrace_append hprefix tailTrace_172213
  have hstable : (prefixWord ++ tailWord_172213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172213).length < 2 ^ (prefixWord ++ tailWord_172213).sum := by decide
  have hdescent : baseEnd_172213 < baseStart_172213 := by decide
  rcases family_descends (prefixWord ++ tailWord_172213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172224 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 3]
def baseStart_172224 : Nat := 118140960795 + 172224 * 2 ^ 59
def prefixEnd_172224 : Nat := 4983230072969 + 3 ^ 40 * 172224 * 2
def baseEnd_172224 : Nat := 78607726435590583562633

theorem tailTrace_172224 : CollatzResearch.WordTrace tailWord_172224 prefixEnd_172224 78607726435590583562633 := by
  unfold tailWord_172224
  simp only [CollatzResearch.WordTrace]
  refine ⟨3140762664034668181289863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4187683552046224241719817 3140762664034668181289863)
  ·
    refine ⟨4711143996052002271934795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3140762664034668181289863 4711143996052002271934795)
    ·
      refine ⟨7066715994078003407902193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4711143996052002271934795 7066715994078003407902193)
      ·
        refine ⟨5300036995558502555926645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7066715994078003407902193 5300036995558502555926645)
        ·
          refine ⟨496878468333609614618123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5300036995558502555926645 496878468333609614618123)
          ·
            refine ⟨745317702500414421927185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496878468333609614618123 745317702500414421927185)
            ·
              refine ⟨558988276875310816445389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745317702500414421927185 558988276875310816445389)
              ·
                refine ⟨209620603828241556167021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 558988276875310816445389 209620603828241556167021)
                ·
                  refine ⟨78607726435590583562633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209620603828241556167021 78607726435590583562633)
                  ·
                    rfl

theorem cell20_172224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_172224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172224 prefixEnd_172224 := by exact prefixLift 172224
  have htrace : WordTrace (prefixWord ++ tailWord_172224) baseStart_172224 baseEnd_172224 := by
    simpa [prefixWord, tailWord_172224, baseEnd_172224] using wordTrace_append hprefix tailTrace_172224
  have hstable : (prefixWord ++ tailWord_172224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172224).length < 2 ^ (prefixWord ++ tailWord_172224).sum := by decide
  have hdescent : baseEnd_172224 < baseStart_172224 := by decide
  rcases family_descends (prefixWord ++ tailWord_172224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172248 : List Nat := [2, 1, 2, 2, 4, 1, 1, 5, 2]
def baseStart_172248 : Nat := 118140960795 + 172248 * 2 ^ 59
def prefixEnd_172248 : Nat := 4983230072969 + 3 ^ 40 * 172248 * 2
def baseEnd_172248 : Nat := 78618680689553166762535

theorem tailTrace_172248 : CollatzResearch.WordTrace tailWord_172248 prefixEnd_172248 78618680689553166762535 := by
  unfold tailWord_172248
  simp only [CollatzResearch.WordTrace]
  refine ⟨3141200339991194230726699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4188267119988258974302265 3141200339991194230726699)
  ·
    refine ⟨4711800509986791346090049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3141200339991194230726699 4711800509986791346090049)
    ·
      refine ⟨3533850382490093509567537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4711800509986791346090049 3533850382490093509567537)
      ·
        refine ⟨2650387786867570132175653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3533850382490093509567537 2650387786867570132175653)
        ·
          refine ⟨496947710037669399782935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2650387786867570132175653 496947710037669399782935)
          ·
            refine ⟨745421565056504099674403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496947710037669399782935 745421565056504099674403)
            ·
              refine ⟨1118132347584756149511605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745421565056504099674403 1118132347584756149511605)
              ·
                refine ⟨104824907586070889016713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1118132347584756149511605 104824907586070889016713)
                ·
                  refine ⟨78618680689553166762535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104824907586070889016713 78618680689553166762535)
                  ·
                    rfl

theorem cell20_172248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_172248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172248 prefixEnd_172248 := by exact prefixLift 172248
  have htrace : WordTrace (prefixWord ++ tailWord_172248) baseStart_172248 baseEnd_172248 := by
    simpa [prefixWord, tailWord_172248, baseEnd_172248] using wordTrace_append hprefix tailTrace_172248
  have hstable : (prefixWord ++ tailWord_172248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172248).length < 2 ^ (prefixWord ++ tailWord_172248).sum := by decide
  have hdescent : baseEnd_172248 < baseStart_172248 := by decide
  rcases family_descends (prefixWord ++ tailWord_172248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172321 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_172321 : Nat := 118140960795 + 172321 * 2 ^ 59
def prefixEnd_172321 : Nat := 4983230072969 + 3 ^ 40 * 172321 * 2
def baseEnd_172321 : Nat := 78651999878689357328903

theorem tailTrace_172321 : CollatzResearch.WordTrace tailWord_172321 prefixEnd_172321 78651999878689357328903 := by
  unfold tailWord_172321
  simp only [CollatzResearch.WordTrace]
  refine ⟨6285063208717921928860817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4190042139145281285907211 6285063208717921928860817)
  ·
    refine ⟨4713797406538441446645613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6285063208717921928860817 4713797406538441446645613)
    ·
      refine ⟨1767674027451915542492105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4713797406538441446645613 1767674027451915542492105)
      ·
        refine ⟨1325755520588936656869079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1767674027451915542492105 1325755520588936656869079)
        ·
          refine ⟨1988633280883404985303619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325755520588936656869079 1988633280883404985303619)
          ·
            refine ⟨2982949921325107477955429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988633280883404985303619 2982949921325107477955429)
            ·
              refine ⟨559303110248457652116643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2982949921325107477955429 559303110248457652116643)
              ·
                refine ⟨838954665372686478174965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559303110248457652116643 838954665372686478174965)
                ·
                  refine ⟨78651999878689357328903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 838954665372686478174965 78651999878689357328903)
                  ·
                    rfl

theorem cell20_172321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_172321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172321 prefixEnd_172321 := by exact prefixLift 172321
  have htrace : WordTrace (prefixWord ++ tailWord_172321) baseStart_172321 baseEnd_172321 := by
    simpa [prefixWord, tailWord_172321, baseEnd_172321] using wordTrace_append hprefix tailTrace_172321
  have hstable : (prefixWord ++ tailWord_172321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172321).length < 2 ^ (prefixWord ++ tailWord_172321).sum := by decide
  have hdescent : baseEnd_172321 < baseStart_172321 := by decide
  rcases family_descends (prefixWord ++ tailWord_172321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172324 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 4]
def baseStart_172324 : Nat := 118140960795 + 172324 * 2 ^ 59
def prefixEnd_172324 : Nat := 4983230072969 + 3 ^ 40 * 172324 * 2
def baseEnd_172324 : Nat := 78653369160434680228891

theorem tailTrace_172324 : CollatzResearch.WordTrace tailWord_172324 prefixEnd_172324 78653369160434680228891 := by
  unfold tailWord_172324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3142586313853526720610013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4190115085138035627480017 3142586313853526720610013)
  ·
    refine ⟨1178469867695072520228755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3142586313853526720610013 1178469867695072520228755)
    ·
      refine ⟨1767704801542608780343133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1178469867695072520228755 1767704801542608780343133)
      ·
        refine ⟨662889300578478292628675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1767704801542608780343133 662889300578478292628675)
        ·
          refine ⟨994333950867717438943013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662889300578478292628675 994333950867717438943013)
          ·
            refine ⟨186437615787697019801815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 994333950867717438943013 186437615787697019801815)
            ·
              refine ⟨279656423681545529702723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186437615787697019801815 279656423681545529702723)
              ·
                refine ⟨419484635522318294554085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279656423681545529702723 419484635522318294554085)
                ·
                  refine ⟨78653369160434680228891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 419484635522318294554085 78653369160434680228891)
                  ·
                    rfl

theorem cell20_172324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_172324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172324 prefixEnd_172324 := by exact prefixLift 172324
  have htrace : WordTrace (prefixWord ++ tailWord_172324) baseStart_172324 baseEnd_172324 := by
    simpa [prefixWord, tailWord_172324, baseEnd_172324] using wordTrace_append hprefix tailTrace_172324
  have hstable : (prefixWord ++ tailWord_172324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172324).length < 2 ^ (prefixWord ++ tailWord_172324).sum := by decide
  have hdescent : baseEnd_172324 < baseStart_172324 := by decide
  rcases family_descends (prefixWord ++ tailWord_172324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172327 : List Nat := [1, 1, 8, 1, 1, 1, 2, 5]
def baseStart_172327 : Nat := 118140960795 + 172327 * 2 ^ 59
def prefixEnd_172327 : Nat := 4983230072969 + 3 ^ 40 * 172327 * 2
def baseEnd_172327 : Nat := 26218246147393334376293

theorem tailTrace_172327 : CollatzResearch.WordTrace tailWord_172327 prefixEnd_172327 26218246147393334376293 := by
  unfold tailWord_172327
  simp only [CollatzResearch.WordTrace]
  refine ⟨6285282046696184953579235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4190188031130789969052823 6285282046696184953579235)
  ·
    refine ⟨9427923070044277430368853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6285282046696184953579235 9427923070044277430368853)
    ·
      refine ⟨110483473477081376137135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 9427923070044277430368853 110483473477081376137135)
      ·
        refine ⟨165725210215622064205703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110483473477081376137135 165725210215622064205703)
        ·
          refine ⟨248587815323433096308555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165725210215622064205703 248587815323433096308555)
          ·
            refine ⟨372881722985149644462833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248587815323433096308555 372881722985149644462833)
            ·
              refine ⟨279661292238862233347125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372881722985149644462833 279661292238862233347125)
              ·
                refine ⟨26218246147393334376293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 279661292238862233347125 26218246147393334376293)
                ·
                  rfl

theorem cell20_172327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 5].length) (baseStart_172327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172327 prefixEnd_172327 := by exact prefixLift 172327
  have htrace : WordTrace (prefixWord ++ tailWord_172327) baseStart_172327 baseEnd_172327 := by
    simpa [prefixWord, tailWord_172327, baseEnd_172327] using wordTrace_append hprefix tailTrace_172327
  have hstable : (prefixWord ++ tailWord_172327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172327).length < 2 ^ (prefixWord ++ tailWord_172327).sum := by decide
  have hdescent : baseEnd_172327 < baseStart_172327 := by decide
  rcases family_descends (prefixWord ++ tailWord_172327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172334 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_172334 : Nat := 118140960795 + 172334 * 2 ^ 59
def prefixEnd_172334 : Nat := 4983230072969 + 3 ^ 40 * 172334 * 2
def baseEnd_172334 : Nat := 78657933432919089895517

theorem tailTrace_172334 : CollatzResearch.WordTrace tailWord_172334 prefixEnd_172334 78657933432919089895517 := by
  unfold tailWord_172334
  simp only [CollatzResearch.WordTrace]
  refine ⟨785692169708853143635507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4190358238447216766056037 785692169708853143635507)
  ·
    refine ⟨1178538254563279715453261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 785692169708853143635507 1178538254563279715453261)
    ·
      refine ⟨441951845461229893294973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1178538254563279715453261 441951845461229893294973)
      ·
        refine ⟨165731942047961209985615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 441951845461229893294973 165731942047961209985615)
        ·
          refine ⟨248597913071941814978423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165731942047961209985615 248597913071941814978423)
          ·
            refine ⟨372896869607912722467635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248597913071941814978423 372896869607912722467635)
            ·
              refine ⟨559345304411869083701453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372896869607912722467635 559345304411869083701453)
              ·
                refine ⟨209754489154450906388045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559345304411869083701453 209754489154450906388045)
                ·
                  refine ⟨78657933432919089895517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209754489154450906388045 78657933432919089895517)
                  ·
                    rfl

theorem cell20_172334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_172334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172334 prefixEnd_172334 := by exact prefixLift 172334
  have htrace : WordTrace (prefixWord ++ tailWord_172334) baseStart_172334 baseEnd_172334 := by
    simpa [prefixWord, tailWord_172334, baseEnd_172334] using wordTrace_append hprefix tailTrace_172334
  have hstable : (prefixWord ++ tailWord_172334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172334).length < 2 ^ (prefixWord ++ tailWord_172334).sum := by decide
  have hdescent : baseEnd_172334 < baseStart_172334 := by decide
  rcases family_descends (prefixWord ++ tailWord_172334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172335 : List Nat := [1, 1, 2, 1, 2, 1, 5, 7]
def baseStart_172335 : Nat := 118140960795 + 172335 * 2 ^ 59
def prefixEnd_172335 : Nat := 4983230072969 + 3 ^ 40 * 172335 * 2
def baseEnd_172335 : Nat := 26219463286722510287393

theorem tailTrace_172335 : CollatzResearch.WordTrace tailWord_172335 prefixEnd_172335 26219463286722510287393 := by
  unfold tailWord_172335
  simp only [CollatzResearch.WordTrace]
  refine ⟨6285573830667202319870459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4190382553778134879913639 6285573830667202319870459)
  ·
    refine ⟨9428360746000803479805689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6285573830667202319870459 9428360746000803479805689)
    ·
      refine ⟨7071270559500602609854267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9428360746000803479805689 7071270559500602609854267)
      ·
        refine ⟨10606905839250903914781401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7071270559500602609854267 10606905839250903914781401)
        ·
          refine ⟨7955179379438177936086051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10606905839250903914781401 7955179379438177936086051)
          ·
            refine ⟨11932769069157266904129077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7955179379438177936086051 11932769069157266904129077)
            ·
              refine ⟨1118697100233493772262101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11932769069157266904129077 1118697100233493772262101)
              ·
                refine ⟨26219463286722510287393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1118697100233493772262101 26219463286722510287393)
                ·
                  rfl

theorem cell20_172335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_172335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172335 prefixEnd_172335 := by exact prefixLift 172335
  have htrace : WordTrace (prefixWord ++ tailWord_172335) baseStart_172335 baseEnd_172335 := by
    simpa [prefixWord, tailWord_172335, baseEnd_172335] using wordTrace_append hprefix tailTrace_172335
  have hstable : (prefixWord ++ tailWord_172335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172335).length < 2 ^ (prefixWord ++ tailWord_172335).sum := by decide
  have hdescent : baseEnd_172335 < baseStart_172335 := by decide
  rcases family_descends (prefixWord ++ tailWord_172335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172366 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_172366 : Nat := 118140960795 + 172366 * 2 ^ 59
def prefixEnd_172366 : Nat := 4983230072969 + 3 ^ 40 * 172366 * 2
def baseEnd_172366 : Nat := 78672539104869200828719

theorem tailTrace_172366 : CollatzResearch.WordTrace tailWord_172366 prefixEnd_172366 78672539104869200828719 := by
  unfold tailWord_172366
  simp only [CollatzResearch.WordTrace]
  refine ⟨785838061694361826781119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4191136329036596409499301 785838061694361826781119)
  ·
    refine ⟨1178757092541542740171679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 785838061694361826781119 1178757092541542740171679)
    ·
      refine ⟨1768135638812314110257519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1178757092541542740171679 1768135638812314110257519)
      ·
        refine ⟨2652203458218471165386279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768135638812314110257519 2652203458218471165386279)
        ·
          refine ⟨3978305187327706748079419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652203458218471165386279 3978305187327706748079419)
          ·
            refine ⟨5967457780991560122119129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978305187327706748079419 5967457780991560122119129)
            ·
              refine ⟨4475593335743670091589347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5967457780991560122119129 4475593335743670091589347)
              ·
                refine ⟨6713390003615505137384021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475593335743670091589347 6713390003615505137384021)
                ·
                  refine ⟨78672539104869200828719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6713390003615505137384021 78672539104869200828719)
                  ·
                    rfl

theorem cell20_172366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_172366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172366 prefixEnd_172366 := by exact prefixLift 172366
  have htrace : WordTrace (prefixWord ++ tailWord_172366) baseStart_172366 baseEnd_172366 := by
    simpa [prefixWord, tailWord_172366, baseEnd_172366] using wordTrace_append hprefix tailTrace_172366
  have hstable : (prefixWord ++ tailWord_172366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172366).length < 2 ^ (prefixWord ++ tailWord_172366).sum := by decide
  have hdescent : baseEnd_172366 < baseStart_172366 := by decide
  rcases family_descends (prefixWord ++ tailWord_172366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172373 : List Nat := [1, 3, 2, 2, 12]
def baseStart_172373 : Nat := 118140960795 + 172373 * 2 ^ 59
def prefixEnd_172373 : Nat := 4983230072969 + 3 ^ 40 * 172373 * 2
def baseEnd_172373 : Nat := 971305359205040587597

theorem tailTrace_172373 : CollatzResearch.WordTrace tailWord_172373 prefixEnd_172373 971305359205040587597 := by
  unfold tailWord_172373
  simp only [CollatzResearch.WordTrace]
  refine ⟨6286959804529534809753773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4191306536353023206502515 6286959804529534809753773)
  ·
    refine ⟨2357609926698575553657665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6286959804529534809753773 2357609926698575553657665)
    ·
      refine ⟨1768207445023931665243249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2357609926698575553657665 1768207445023931665243249)
      ·
        refine ⟨1326155583767948748932437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1768207445023931665243249 1326155583767948748932437)
        ·
          refine ⟨971305359205040587597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1326155583767948748932437 971305359205040587597)
          ·
            rfl

theorem cell20_172373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 12].length) (baseStart_172373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172373 prefixEnd_172373 := by exact prefixLift 172373
  have htrace : WordTrace (prefixWord ++ tailWord_172373) baseStart_172373 baseEnd_172373 := by
    simpa [prefixWord, tailWord_172373, baseEnd_172373] using wordTrace_append hprefix tailTrace_172373
  have hstable : (prefixWord ++ tailWord_172373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172373).length < 2 ^ (prefixWord ++ tailWord_172373).sum := by decide
  have hdescent : baseEnd_172373 < baseStart_172373 := by decide
  rcases family_descends (prefixWord ++ tailWord_172373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172417 : List Nat := [1, 2, 4, 3, 1, 2, 2, 3, 2]
def baseStart_172417 : Nat := 118140960795 + 172417 * 2 ^ 59
def prefixEnd_172417 : Nat := 4983230072969 + 3 ^ 40 * 172417 * 2
def baseEnd_172417 : Nat := 78695816894539690128511

theorem tailTrace_172417 : CollatzResearch.WordTrace tailWord_172417 prefixEnd_172417 78695816894539690128511 := by
  unfold tailWord_172417
  simp only [CollatzResearch.WordTrace]
  refine ⟨6288564616370130324355505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4192376410913420216237003 6288564616370130324355505)
  ·
    refine ⟨4716423462277597743266629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6288564616370130324355505 4716423462277597743266629)
    ·
      refine ⟨884329399177049576862493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4716423462277597743266629 884329399177049576862493)
      ·
        refine ⟨331623524691393591323435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 884329399177049576862493 331623524691393591323435)
        ·
          refine ⟨497435287037090386985153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331623524691393591323435 497435287037090386985153)
          ·
            refine ⟨373076465277817790238865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497435287037090386985153 373076465277817790238865)
            ·
              refine ⟨279807348958363342679149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373076465277817790238865 279807348958363342679149)
              ·
                refine ⟨104927755859386253504681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279807348958363342679149 104927755859386253504681)
                ·
                  refine ⟨78695816894539690128511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104927755859386253504681 78695816894539690128511)
                  ·
                    rfl

theorem cell20_172417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_172417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172417 prefixEnd_172417 := by exact prefixLift 172417
  have htrace : WordTrace (prefixWord ++ tailWord_172417) baseStart_172417 baseEnd_172417 := by
    simpa [prefixWord, tailWord_172417, baseEnd_172417] using wordTrace_append hprefix tailTrace_172417
  have hstable : (prefixWord ++ tailWord_172417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172417).length < 2 ^ (prefixWord ++ tailWord_172417).sum := by decide
  have hdescent : baseEnd_172417 < baseStart_172417 := by decide
  rcases family_descends (prefixWord ++ tailWord_172417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172458 : List Nat := [3, 1, 6, 1, 1, 2, 2, 4]
def baseStart_172458 : Nat := 118140960795 + 172458 * 2 ^ 59
def prefixEnd_172458 : Nat := 4983230072969 + 3 ^ 40 * 172458 * 2
def baseEnd_172458 : Nat := 26238176803908589920559

theorem tailTrace_172458 : CollatzResearch.WordTrace tailWord_172458 prefixEnd_172458 26238176803908589920559 := by
  unfold tailWord_172458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572515002305398581649507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4193373339481062884398685 1572515002305398581649507)
  ·
    refine ⟨2358772503458097872474261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1572515002305398581649507 2358772503458097872474261)
    ·
      refine ⟨110567461099598337772231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2358772503458097872474261 110567461099598337772231)
      ·
        refine ⟨165851191649397506658347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110567461099598337772231 165851191649397506658347)
        ·
          refine ⟨248776787474096259987521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165851191649397506658347 248776787474096259987521)
          ·
            refine ⟨186582590605572194990641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248776787474096259987521 186582590605572194990641)
            ·
              refine ⟨139936942954179146242981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186582590605572194990641 139936942954179146242981)
              ·
                refine ⟨26238176803908589920559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139936942954179146242981 26238176803908589920559)
                ·
                  rfl

theorem cell20_172458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_172458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172458 prefixEnd_172458 := by exact prefixLift 172458
  have htrace : WordTrace (prefixWord ++ tailWord_172458) baseStart_172458 baseEnd_172458 := by
    simpa [prefixWord, tailWord_172458, baseEnd_172458] using wordTrace_append hprefix tailTrace_172458
  have hstable : (prefixWord ++ tailWord_172458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172458).length < 2 ^ (prefixWord ++ tailWord_172458).sum := by decide
  have hdescent : baseEnd_172458 < baseStart_172458 := by decide
  rcases family_descends (prefixWord ++ tailWord_172458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172468 : List Nat := [2, 5, 2, 2, 2, 1, 1, 3, 2]
def baseStart_172468 : Nat := 118140960795 + 172468 * 2 ^ 59
def prefixEnd_172468 : Nat := 4983230072969 + 3 ^ 40 * 172468 * 2
def baseEnd_172468 : Nat := 78719094684210179428303

theorem tailTrace_172468 : CollatzResearch.WordTrace tailWord_172468 prefixEnd_172468 78719094684210179428303 := by
  unfold tailWord_172468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3145212369592683017231029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4193616492790244022974705 3145212369592683017231029)
  ·
    refine ⟨294863659649314032865409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3145212369592683017231029 294863659649314032865409)
    ·
      refine ⟨221147744736985524649057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294863659649314032865409 221147744736985524649057)
      ·
        refine ⟨165860808552739143486793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221147744736985524649057 165860808552739143486793)
        ·
          refine ⟨124395606414554357615095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165860808552739143486793 124395606414554357615095)
          ·
            refine ⟨186593409621831536422643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124395606414554357615095 186593409621831536422643)
            ·
              refine ⟨279890114432747304633965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186593409621831536422643 279890114432747304633965)
              ·
                refine ⟨104958792912280239237737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279890114432747304633965 104958792912280239237737)
                ·
                  refine ⟨78719094684210179428303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104958792912280239237737 78719094684210179428303)
                  ·
                    rfl

theorem cell20_172468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_172468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172468 prefixEnd_172468 := by exact prefixLift 172468
  have htrace : WordTrace (prefixWord ++ tailWord_172468) baseStart_172468 baseEnd_172468 := by
    simpa [prefixWord, tailWord_172468, baseEnd_172468] using wordTrace_append hprefix tailTrace_172468
  have hstable : (prefixWord ++ tailWord_172468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172468).length < 2 ^ (prefixWord ++ tailWord_172468).sum := by decide
  have hdescent : baseEnd_172468 < baseStart_172468 := by decide
  rcases family_descends (prefixWord ++ tailWord_172468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172473 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_172473 : Nat := 118140960795 + 172473 * 2 ^ 59
def prefixEnd_172473 : Nat := 4983230072969 + 3 ^ 40 * 172473 * 2
def baseEnd_172473 : Nat := 78721376820452384261615

theorem tailTrace_172473 : CollatzResearch.WordTrace tailWord_172473 prefixEnd_172473 78721376820452384261615 := by
  unfold tailWord_172473
  simp only [CollatzResearch.WordTrace]
  refine ⟨6290607104167251888394073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4193738069444834592262715 6290607104167251888394073)
  ·
    refine ⟨4717955328125438916295555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6290607104167251888394073 4717955328125438916295555)
    ·
      refine ⟨7076932992188158374443333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4717955328125438916295555 7076932992188158374443333)
      ·
        refine ⟨1326924936035279695208125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7076932992188158374443333 1326924936035279695208125)
        ·
          refine ⟨497596851013229885703047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1326924936035279695208125 497596851013229885703047)
          ·
            refine ⟨746395276519844828554571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497596851013229885703047 746395276519844828554571)
            ·
              refine ⟨1119592914779767242831857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746395276519844828554571 1119592914779767242831857)
              ·
                refine ⟨839694686084825432123893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1119592914779767242831857 839694686084825432123893)
                ·
                  refine ⟨78721376820452384261615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 839694686084825432123893 78721376820452384261615)
                  ·
                    rfl

theorem cell20_172473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_172473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172473 prefixEnd_172473 := by exact prefixLift 172473
  have htrace : WordTrace (prefixWord ++ tailWord_172473) baseStart_172473 baseEnd_172473 := by
    simpa [prefixWord, tailWord_172473, baseEnd_172473] using wordTrace_append hprefix tailTrace_172473
  have hstable : (prefixWord ++ tailWord_172473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172473).length < 2 ^ (prefixWord ++ tailWord_172473).sum := by decide
  have hdescent : baseEnd_172473 < baseStart_172473 := by decide
  rcases family_descends (prefixWord ++ tailWord_172473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172487 : List Nat := [1, 1, 4, 1, 1, 4, 8]
def baseStart_172487 : Nat := 118140960795 + 172487 * 2 ^ 59
def prefixEnd_172487 : Nat := 4983230072969 + 3 ^ 40 * 172487 * 2
def baseEnd_172487 : Nat := 8747529644658950866099

theorem tailTrace_172487 : CollatzResearch.WordTrace tailWord_172487 prefixEnd_172487 8747529644658950866099 := by
  unfold tailWord_172487
  simp only [CollatzResearch.WordTrace]
  refine ⟨6291117726116532279403715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4194078484077688186269143 6291117726116532279403715)
  ·
    refine ⟨9436676589174798419105573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6291117726116532279403715 9436676589174798419105573)
    ·
      refine ⟨1769376860470274703582295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9436676589174798419105573 1769376860470274703582295)
      ·
        refine ⟨2654065290705412055373443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769376860470274703582295 2654065290705412055373443)
        ·
          refine ⟨3981097936058118083060165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2654065290705412055373443 3981097936058118083060165)
          ·
            refine ⟨746455863010897140573781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3981097936058118083060165 746455863010897140573781)
            ·
              refine ⟨8747529644658950866099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 746455863010897140573781 8747529644658950866099)
              ·
                rfl

theorem cell20_172487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 8].length) (baseStart_172487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172487 prefixEnd_172487 := by exact prefixLift 172487
  have htrace : WordTrace (prefixWord ++ tailWord_172487) baseStart_172487 baseEnd_172487 := by
    simpa [prefixWord, tailWord_172487, baseEnd_172487] using wordTrace_append hprefix tailTrace_172487
  have hstable : (prefixWord ++ tailWord_172487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172487).length < 2 ^ (prefixWord ++ tailWord_172487).sum := by decide
  have hdescent : baseEnd_172487 < baseStart_172487 := by decide
  rcases family_descends (prefixWord ++ tailWord_172487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172497 : List Nat := [1, 2, 2, 1, 2, 1, 1, 8, 2]
def baseStart_172497 : Nat := 118140960795 + 172497 * 2 ^ 59
def prefixEnd_172497 : Nat := 4983230072969 + 3 ^ 40 * 172497 * 2
def baseEnd_172497 : Nat := 78732331074414967461517

theorem tailTrace_172497 : CollatzResearch.WordTrace tailWord_172497 prefixEnd_172497 78732331074414967461517 := by
  unfold tailWord_172497
  simp only [CollatzResearch.WordTrace]
  refine ⟨6291482456080303987267745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4194321637386869324845163 6291482456080303987267745)
  ·
    refine ⟨4718611842060227990450809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6291482456080303987267745 4718611842060227990450809)
    ·
      refine ⟨3538958881545170992838107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4718611842060227990450809 3538958881545170992838107)
      ·
        refine ⟨5308438322317756489257161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3538958881545170992838107 5308438322317756489257161)
        ·
          refine ⟨3981328741738317366942871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5308438322317756489257161 3981328741738317366942871)
          ·
            refine ⟨5971993112607476050414307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3981328741738317366942871 5971993112607476050414307)
            ·
              refine ⟨8957989668911214075621461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5971993112607476050414307 8957989668911214075621461)
              ·
                refine ⟨104976441432553289948689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8957989668911214075621461 104976441432553289948689)
                ·
                  refine ⟨78732331074414967461517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104976441432553289948689 78732331074414967461517)
                  ·
                    rfl

theorem cell20_172497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_172497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172497 prefixEnd_172497 := by exact prefixLift 172497
  have htrace : WordTrace (prefixWord ++ tailWord_172497) baseStart_172497 baseEnd_172497 := by
    simpa [prefixWord, tailWord_172497, baseEnd_172497] using wordTrace_append hprefix tailTrace_172497
  have hstable : (prefixWord ++ tailWord_172497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172497).length < 2 ^ (prefixWord ++ tailWord_172497).sum := by decide
  have hdescent : baseEnd_172497 < baseStart_172497 := by decide
  rcases family_descends (prefixWord ++ tailWord_172497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172548 : List Nat := [2, 3, 2, 3, 1, 3, 2, 2, 2]
def baseStart_172548 : Nat := 118140960795 + 172548 * 2 ^ 59
def prefixEnd_172548 : Nat := 4983230072969 + 3 ^ 40 * 172548 * 2
def baseEnd_172548 : Nat := 78755608864085456761309

theorem tailTrace_172548 : CollatzResearch.WordTrace tailWord_172548 prefixEnd_172548 78755608864085456761309 := by
  unfold tailWord_172548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146671289447769848687149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4195561719263693131582865 3146671289447769848687149)
  ·
    refine ⟨1180001733542913693257681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3146671289447769848687149 1180001733542913693257681)
    ·
      refine ⟨885001300157185269943261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1180001733542913693257681 885001300157185269943261)
      ·
        refine ⟨331875487558944476228723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 885001300157185269943261 331875487558944476228723)
        ·
          refine ⟨497813231338416714343085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331875487558944476228723 497813231338416714343085)
          ·
            refine ⟨186679961751906267878657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 497813231338416714343085 186679961751906267878657)
            ·
              refine ⟨140009971313929700908993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186679961751906267878657 140009971313929700908993)
              ·
                refine ⟨105007478485447275681745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140009971313929700908993 105007478485447275681745)
                ·
                  refine ⟨78755608864085456761309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105007478485447275681745 78755608864085456761309)
                  ·
                    rfl

theorem cell20_172548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_172548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172548 prefixEnd_172548 := by exact prefixLift 172548
  have htrace : WordTrace (prefixWord ++ tailWord_172548) baseStart_172548 baseEnd_172548 := by
    simpa [prefixWord, tailWord_172548, baseEnd_172548] using wordTrace_append hprefix tailTrace_172548
  have hstable : (prefixWord ++ tailWord_172548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172548).length < 2 ^ (prefixWord ++ tailWord_172548).sum := by decide
  have hdescent : baseEnd_172548 < baseStart_172548 := by decide
  rcases family_descends (prefixWord ++ tailWord_172548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172549 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 3]
def baseStart_172549 : Nat := 118140960795 + 172549 * 2 ^ 59
def prefixEnd_172549 : Nat := 4983230072969 + 3 ^ 40 * 172549 * 2
def baseEnd_172549 : Nat := 78756065291333897727971

theorem tailTrace_172549 : CollatzResearch.WordTrace tailWord_172549 prefixEnd_172549 78756065291333897727971 := by
  unfold tailWord_172549
  simp only [CollatzResearch.WordTrace]
  refine ⟨6293379051891916868160701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4195586034594611245440467 6293379051891916868160701)
  ·
    refine ⟨2360017144459468825560263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6293379051891916868160701 2360017144459468825560263)
    ·
      refine ⟨3540025716689203238340395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360017144459468825560263 3540025716689203238340395)
      ·
        refine ⟨5310038575033804857510593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3540025716689203238340395 5310038575033804857510593)
        ·
          refine ⟨3982528931275353643132945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5310038575033804857510593 3982528931275353643132945)
          ·
            refine ⟨2986896698456515232349709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3982528931275353643132945 2986896698456515232349709)
            ·
              refine ⟨1120086261921193212131141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2986896698456515232349709 1120086261921193212131141)
              ·
                refine ⟨210016174110223727274589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1120086261921193212131141 210016174110223727274589)
                ·
                  refine ⟨78756065291333897727971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210016174110223727274589 78756065291333897727971)
                  ·
                    rfl

theorem cell20_172549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_172549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172549 prefixEnd_172549 := by exact prefixLift 172549
  have htrace : WordTrace (prefixWord ++ tailWord_172549) baseStart_172549 baseEnd_172549 := by
    simpa [prefixWord, tailWord_172549, baseEnd_172549] using wordTrace_append hprefix tailTrace_172549
  have hstable : (prefixWord ++ tailWord_172549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172549).length < 2 ^ (prefixWord ++ tailWord_172549).sum := by decide
  have hdescent : baseEnd_172549 < baseStart_172549 := by decide
  rcases family_descends (prefixWord ++ tailWord_172549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172573 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 4]
def baseStart_172573 : Nat := 118140960795 + 172573 * 2 ^ 59
def prefixEnd_172573 : Nat := 4983230072969 + 3 ^ 40 * 172573 * 2
def baseEnd_172573 : Nat := 78767019545296480927873

theorem tailTrace_172573 : CollatzResearch.WordTrace tailWord_172573 prefixEnd_172573 78767019545296480927873 := by
  unfold tailWord_172573
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294254403804968967034373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4196169602536645978022915 6294254403804968967034373)
  ·
    refine ⟨1180172700713431681318945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6294254403804968967034373 1180172700713431681318945)
    ·
      refine ⟨885129525535073760989209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1180172700713431681318945 885129525535073760989209)
      ·
        refine ⟨663847144151305320741907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 885129525535073760989209 663847144151305320741907)
        ·
          refine ⟨995770716226957981112861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663847144151305320741907 995770716226957981112861)
          ·
            refine ⟨373414018585109242917323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 995770716226957981112861 373414018585109242917323)
            ·
              refine ⟨560121027877663864375985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373414018585109242917323 560121027877663864375985)
              ·
                refine ⟨420090770908247898281989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560121027877663864375985 420090770908247898281989)
                ·
                  refine ⟨78767019545296480927873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 420090770908247898281989 78767019545296480927873)
                  ·
                    rfl

theorem cell20_172573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_172573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172573 prefixEnd_172573 := by exact prefixLift 172573
  have htrace : WordTrace (prefixWord ++ tailWord_172573) baseStart_172573 baseEnd_172573 := by
    simpa [prefixWord, tailWord_172573, baseEnd_172573] using wordTrace_append hprefix tailTrace_172573
  have hstable : (prefixWord ++ tailWord_172573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172573).length < 2 ^ (prefixWord ++ tailWord_172573).sum := by decide
  have hdescent : baseEnd_172573 < baseStart_172573 := by decide
  rcases family_descends (prefixWord ++ tailWord_172573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172601 : List Nat := [1, 2, 1, 5, 1, 1, 9]
def baseStart_172601 : Nat := 118140960795 + 172601 * 2 ^ 59
def prefixEnd_172601 : Nat := 4983230072969 + 3 ^ 40 * 172601 * 2
def baseEnd_172601 : Nat := 8753311056472536443825

theorem tailTrace_172601 : CollatzResearch.WordTrace tailWord_172601 prefixEnd_172601 8753311056472536443825 := by
  unfold tailWord_172601
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295275647703529749053657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4196850431802353166035771 6295275647703529749053657)
  ·
    refine ⟨4721456735777647311790243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6295275647703529749053657 4721456735777647311790243)
    ·
      refine ⟨7082185103666470967685365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4721456735777647311790243 7082185103666470967685365)
      ·
        refine ⟨663954853468731653220503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7082185103666470967685365 663954853468731653220503)
        ·
          refine ⟨995932280203097479830755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663954853468731653220503 995932280203097479830755)
          ·
            refine ⟨1493898420304646219746133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995932280203097479830755 1493898420304646219746133)
            ·
              refine ⟨8753311056472536443825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1493898420304646219746133 8753311056472536443825)
              ·
                rfl

theorem cell20_172601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 9].length) (baseStart_172601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172601 prefixEnd_172601 := by exact prefixLift 172601
  have htrace : WordTrace (prefixWord ++ tailWord_172601) baseStart_172601 baseEnd_172601 := by
    simpa [prefixWord, tailWord_172601, baseEnd_172601] using wordTrace_append hprefix tailTrace_172601
  have hstable : (prefixWord ++ tailWord_172601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172601).length < 2 ^ (prefixWord ++ tailWord_172601).sum := by decide
  have hdescent : baseEnd_172601 < baseStart_172601 := by decide
  rcases family_descends (prefixWord ++ tailWord_172601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172604 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 3]
def baseStart_172604 : Nat := 118140960795 + 172604 * 2 ^ 59
def prefixEnd_172604 : Nat := 4983230072969 + 3 ^ 40 * 172604 * 2
def baseEnd_172604 : Nat := 78781168789998150894413

theorem tailTrace_172604 : CollatzResearch.WordTrace tailWord_172604 prefixEnd_172604 78781168789998150894413 := by
  unfold tailWord_172604
  simp only [CollatzResearch.WordTrace]
  refine ⟨3147692533346330630706433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4196923377795107507608577 3147692533346330630706433)
  ·
    refine ⟨2360769400009747973029825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3147692533346330630706433 2360769400009747973029825)
    ·
      refine ⟨1770577050007310979772369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2360769400009747973029825 1770577050007310979772369)
      ·
        refine ⟨1327932787505483234829277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1770577050007310979772369 1327932787505483234829277)
        ·
          refine ⟨497974795314556213060979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1327932787505483234829277 497974795314556213060979)
          ·
            refine ⟨746962192971834319591469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497974795314556213060979 746962192971834319591469)
            ·
              refine ⟨280110822364437869846801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 746962192971834319591469 280110822364437869846801)
              ·
                refine ⟨210083116773328402385101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280110822364437869846801 210083116773328402385101)
                ·
                  refine ⟨78781168789998150894413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210083116773328402385101 78781168789998150894413)
                  ·
                    rfl

theorem cell20_172604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_172604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172604 prefixEnd_172604 := by exact prefixLift 172604
  have htrace : WordTrace (prefixWord ++ tailWord_172604) baseStart_172604 baseEnd_172604 := by
    simpa [prefixWord, tailWord_172604, baseEnd_172604] using wordTrace_append hprefix tailTrace_172604
  have hstable : (prefixWord ++ tailWord_172604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172604).length < 2 ^ (prefixWord ++ tailWord_172604).sum := by decide
  have hdescent : baseEnd_172604 < baseStart_172604 := by decide
  rcases family_descends (prefixWord ++ tailWord_172604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172632 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_172632 : Nat := 118140960795 + 172632 * 2 ^ 59
def prefixEnd_172632 : Nat := 4983230072969 + 3 ^ 40 * 172632 * 2
def baseEnd_172632 : Nat := 78793948752954497960965

theorem tailTrace_172632 : CollatzResearch.WordTrace tailWord_172632 prefixEnd_172632 78793948752954497960965 := by
  unfold tailWord_172632
  simp only [CollatzResearch.WordTrace]
  refine ⟨3148203155295611021716075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4197604207060814695621433 3148203155295611021716075)
  ·
    refine ⟨4722304732943416532574113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3148203155295611021716075 4722304732943416532574113)
    ·
      refine ⟨3541728549707562399430585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4722304732943416532574113 3541728549707562399430585)
      ·
        refine ⟨2656296412280671799572939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3541728549707562399430585 2656296412280671799572939)
        ·
          refine ⟨3984444618421007699359409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656296412280671799572939 3984444618421007699359409)
          ·
            refine ⟨2988333463815755774519557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3984444618421007699359409 2988333463815755774519557)
            ·
              refine ⟨560312524465454207722417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2988333463815755774519557 560312524465454207722417)
              ·
                refine ⟨420234393349090655791813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560312524465454207722417 420234393349090655791813)
                ·
                  refine ⟨78793948752954497960965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 420234393349090655791813 78793948752954497960965)
                  ·
                    rfl

theorem cell20_172632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_172632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172632 prefixEnd_172632 := by exact prefixLift 172632
  have htrace : WordTrace (prefixWord ++ tailWord_172632) baseStart_172632 baseEnd_172632 := by
    simpa [prefixWord, tailWord_172632, baseEnd_172632] using wordTrace_append hprefix tailTrace_172632
  have hstable : (prefixWord ++ tailWord_172632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172632).length < 2 ^ (prefixWord ++ tailWord_172632).sum := by decide
  have hdescent : baseEnd_172632 < baseStart_172632 := by decide
  rcases family_descends (prefixWord ++ tailWord_172632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172645 : List Nat := [1, 3, 1, 3, 4, 2, 1, 3, 2]
def baseStart_172645 : Nat := 118140960795 + 172645 * 2 ^ 59
def prefixEnd_172645 : Nat := 4983230072969 + 3 ^ 40 * 172645 * 2
def baseEnd_172645 : Nat := 78799882307184230527579

theorem tailTrace_172645 : CollatzResearch.WordTrace tailWord_172645 prefixEnd_172645 78799882307184230527579 := by
  unfold tailWord_172645
  simp only [CollatzResearch.WordTrace]
  refine ⟨6296880459544125263655389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4197920306362750175770259 6296880459544125263655389)
  ·
    refine ⟨2361330172329046973870771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6296880459544125263655389 2361330172329046973870771)
    ·
      refine ⟨3541995258493570460806157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2361330172329046973870771 3541995258493570460806157)
      ·
        refine ⟨1328248221935088922802309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3541995258493570460806157 1328248221935088922802309)
        ·
          refine ⟨249046541612829173025433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1328248221935088922802309 249046541612829173025433)
          ·
            refine ⟨186784906209621879769075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249046541612829173025433 186784906209621879769075)
            ·
              refine ⟨280177359314432819653613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186784906209621879769075 280177359314432819653613)
              ·
                refine ⟨105066509742912307370105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280177359314432819653613 105066509742912307370105)
                ·
                  refine ⟨78799882307184230527579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105066509742912307370105 78799882307184230527579)
                  ·
                    rfl

theorem cell20_172645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_172645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172645 prefixEnd_172645 := by exact prefixLift 172645
  have htrace : WordTrace (prefixWord ++ tailWord_172645) baseStart_172645 baseEnd_172645 := by
    simpa [prefixWord, tailWord_172645, baseEnd_172645] using wordTrace_append hprefix tailTrace_172645
  have hstable : (prefixWord ++ tailWord_172645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172645).length < 2 ^ (prefixWord ++ tailWord_172645).sum := by decide
  have hdescent : baseEnd_172645 < baseStart_172645 := by decide
  rcases family_descends (prefixWord ++ tailWord_172645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172656 : List Nat := [2, 1, 1, 1, 7, 2, 6]
def baseStart_172656 : Nat := 118140960795 + 172656 * 2 ^ 59
def prefixEnd_172656 : Nat := 4983230072969 + 3 ^ 40 * 172656 * 2
def baseEnd_172656 : Nat := 8756100334101897906763

theorem tailTrace_172656 : CollatzResearch.WordTrace tailWord_172656 prefixEnd_172656 8756100334101897906763 := by
  unfold tailWord_172656
  simp only [CollatzResearch.WordTrace]
  refine ⟨3148640831252137071152911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4198187775002849428203881 3148640831252137071152911)
  ·
    refine ⟨4722961246878205606729367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3148640831252137071152911 4722961246878205606729367)
    ·
      refine ⟨7084441870317308410094051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4722961246878205606729367 7084441870317308410094051)
      ·
        refine ⟨10626662805475962615141077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7084441870317308410094051 10626662805475962615141077)
        ·
          refine ⟨249062409503342873792369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10626662805475962615141077 249062409503342873792369)
          ·
            refine ⟨186796807127507155344277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249062409503342873792369 186796807127507155344277)
            ·
              refine ⟨8756100334101897906763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 186796807127507155344277 8756100334101897906763)
              ·
                rfl

theorem cell20_172656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 6].length) (baseStart_172656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172656 prefixEnd_172656 := by exact prefixLift 172656
  have htrace : WordTrace (prefixWord ++ tailWord_172656) baseStart_172656 baseEnd_172656 := by
    simpa [prefixWord, tailWord_172656, baseEnd_172656] using wordTrace_append hprefix tailTrace_172656
  have hstable : (prefixWord ++ tailWord_172656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172656).length < 2 ^ (prefixWord ++ tailWord_172656).sum := by decide
  have hdescent : baseEnd_172656 < baseStart_172656 := by decide
  rcases family_descends (prefixWord ++ tailWord_172656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172662 : List Nat := [5, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_172662 : Nat := 118140960795 + 172662 * 2 ^ 59
def prefixEnd_172662 : Nat := 4983230072969 + 3 ^ 40 * 172662 * 2
def baseEnd_172662 : Nat := 78807641570407726960843

theorem tailTrace_172662 : CollatzResearch.WordTrace tailWord_172662 prefixEnd_172662 78807641570407726960843 := by
  unfold tailWord_172662
  simp only [CollatzResearch.WordTrace]
  refine ⟨393593781280158572939015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4198333666988358111349493 393593781280158572939015)
  ·
    refine ⟨590390671920237859408523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393593781280158572939015 590390671920237859408523)
    ·
      refine ⟨885586007880356789112785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590390671920237859408523 885586007880356789112785)
      ·
        refine ⟨664189505910267591834589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 885586007880356789112785 664189505910267591834589)
        ·
          refine ⟨249071064716350346937971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 664189505910267591834589 249071064716350346937971)
          ·
            refine ⟨373606597074525520406957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249071064716350346937971 373606597074525520406957)
            ·
              refine ⟨140102473902947070152609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373606597074525520406957 140102473902947070152609)
              ·
                refine ⟨105076855427210302614457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140102473902947070152609 105076855427210302614457)
                ·
                  refine ⟨78807641570407726960843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105076855427210302614457 78807641570407726960843)
                  ·
                    rfl

theorem cell20_172662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_172662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172662 prefixEnd_172662 := by exact prefixLift 172662
  have htrace : WordTrace (prefixWord ++ tailWord_172662) baseStart_172662 baseEnd_172662 := by
    simpa [prefixWord, tailWord_172662, baseEnd_172662] using wordTrace_append hprefix tailTrace_172662
  have hstable : (prefixWord ++ tailWord_172662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172662).length < 2 ^ (prefixWord ++ tailWord_172662).sum := by decide
  have hdescent : baseEnd_172662 < baseStart_172662 := by decide
  rcases family_descends (prefixWord ++ tailWord_172662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172677 : List Nat := [1, 3, 1, 1, 4, 2, 1, 7]
def baseStart_172677 : Nat := 118140960795 + 172677 * 2 ^ 59
def prefixEnd_172677 : Nat := 4983230072969 + 3 ^ 40 * 172677 * 2
def baseEnd_172677 : Nat := 26271495993044780486927

theorem tailTrace_172677 : CollatzResearch.WordTrace tailWord_172677 prefixEnd_172677 26271495993044780486927 := by
  unfold tailWord_172677
  simp only [CollatzResearch.WordTrace]
  refine ⟨6298047595428194728820285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4198698396952129819213523 6298047595428194728820285)
  ·
    refine ⟨2361767848285573023307607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6298047595428194728820285 2361767848285573023307607)
    ·
      refine ⟨3542651772428359534961411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2361767848285573023307607 3542651772428359534961411)
      ·
        refine ⟨5313977658642539302442117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3542651772428359534961411 5313977658642539302442117)
        ·
          refine ⟨996370810995476119207897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5313977658642539302442117 996370810995476119207897)
          ·
            refine ⟨747278108246607089405923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 996370810995476119207897 747278108246607089405923)
            ·
              refine ⟨1120917162369910634108885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747278108246607089405923 1120917162369910634108885)
              ·
                refine ⟨26271495993044780486927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1120917162369910634108885 26271495993044780486927)
                ·
                  rfl

theorem cell20_172677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_172677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172677 prefixEnd_172677 := by exact prefixLift 172677
  have htrace : WordTrace (prefixWord ++ tailWord_172677) baseStart_172677 baseEnd_172677 := by
    simpa [prefixWord, tailWord_172677, baseEnd_172677] using wordTrace_append hprefix tailTrace_172677
  have hstable : (prefixWord ++ tailWord_172677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172677).length < 2 ^ (prefixWord ++ tailWord_172677).sum := by decide
  have hdescent : baseEnd_172677 < baseStart_172677 := by decide
  rcases family_descends (prefixWord ++ tailWord_172677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172684 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_172684 : Nat := 118140960795 + 172684 * 2 ^ 59
def prefixEnd_172684 : Nat := 4983230072969 + 3 ^ 40 * 172684 * 2
def baseEnd_172684 : Nat := 78817682969873428227419

theorem tailTrace_172684 : CollatzResearch.WordTrace tailWord_172684 prefixEnd_172684 78817682969873428227419 := by
  unfold tailWord_172684
  simp only [CollatzResearch.WordTrace]
  refine ⟨3149151453201417462162553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4198868604268556616216737 3149151453201417462162553)
  ·
    refine ⟨2361863589901063096621915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3149151453201417462162553 2361863589901063096621915)
    ·
      refine ⟨3542795384851594644932873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2361863589901063096621915 3542795384851594644932873)
      ·
        refine ⟨2657096538638695983699655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3542795384851594644932873 2657096538638695983699655)
        ·
          refine ⟨3985644807958043975549483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657096538638695983699655 3985644807958043975549483)
          ·
            refine ⟨5978467211937065963324225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985644807958043975549483 5978467211937065963324225)
            ·
              refine ⟨4483850408952799472493169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5978467211937065963324225 4483850408952799472493169)
              ·
                refine ⟨3362887806714599604369877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4483850408952799472493169 3362887806714599604369877)
                ·
                  refine ⟨78817682969873428227419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3362887806714599604369877 78817682969873428227419)
                  ·
                    rfl

theorem cell20_172684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_172684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172684 prefixEnd_172684 := by exact prefixLift 172684
  have htrace : WordTrace (prefixWord ++ tailWord_172684) baseStart_172684 baseEnd_172684 := by
    simpa [prefixWord, tailWord_172684, baseEnd_172684] using wordTrace_append hprefix tailTrace_172684
  have hstable : (prefixWord ++ tailWord_172684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172684).length < 2 ^ (prefixWord ++ tailWord_172684).sum := by decide
  have hdescent : baseEnd_172684 < baseStart_172684 := by decide
  rcases family_descends (prefixWord ++ tailWord_172684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172711 : List Nat := [1, 1, 6, 3, 2, 7]
def baseStart_172711 : Nat := 118140960795 + 172711 * 2 ^ 59
def prefixEnd_172711 : Nat := 4983230072969 + 3 ^ 40 * 172711 * 2
def baseEnd_172711 : Nat := 2919629870577086456567

theorem tailTrace_172711 : CollatzResearch.WordTrace tailWord_172711 prefixEnd_172711 2919629870577086456567 := by
  unfold tailWord_172711
  simp only [CollatzResearch.WordTrace]
  refine ⟨6299287677305018535557987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4199525118203345690371991 6299287677305018535557987)
  ·
    refine ⟨9448931515957527803336981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6299287677305018535557987 9448931515957527803336981)
    ·
      refine ⟨442918664810509115781421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9448931515957527803336981 442918664810509115781421)
      ·
        refine ⟨166094499303940918418033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442918664810509115781421 166094499303940918418033)
        ·
          refine ⟨124570874477955688813525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166094499303940918418033 124570874477955688813525)
          ·
            refine ⟨2919629870577086456567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 124570874477955688813525 2919629870577086456567)
            ·
              rfl

theorem cell20_172711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 7].length) (baseStart_172711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172711 prefixEnd_172711 := by exact prefixLift 172711
  have htrace : WordTrace (prefixWord ++ tailWord_172711) baseStart_172711 baseEnd_172711 := by
    simpa [prefixWord, tailWord_172711, baseEnd_172711] using wordTrace_append hprefix tailTrace_172711
  have hstable : (prefixWord ++ tailWord_172711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172711).length < 2 ^ (prefixWord ++ tailWord_172711).sum := by decide
  have hdescent : baseEnd_172711 < baseStart_172711 := by decide
  rcases family_descends (prefixWord ++ tailWord_172711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172714 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_172714 : Nat := 118140960795 + 172714 * 2 ^ 59
def prefixEnd_172714 : Nat := 4983230072969 + 3 ^ 40 * 172714 * 2
def baseEnd_172714 : Nat := 78831375787326657227297

theorem tailTrace_172714 : CollatzResearch.WordTrace tailWord_172714 prefixEnd_172714 78831375787326657227297 := by
  unfold tailWord_172714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574849274073537511979299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4199598064196100031944797 1574849274073537511979299)
  ·
    refine ⟨2362273911110306267968949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1574849274073537511979299 2362273911110306267968949)
    ·
      refine ⟨221463179166591212622089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2362273911110306267968949 221463179166591212622089)
      ·
        refine ⟨166097384374943409466567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221463179166591212622089 166097384374943409466567)
        ·
          refine ⟨249146076562415114199851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166097384374943409466567 249146076562415114199851)
          ·
            refine ⟨373719114843622671299777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249146076562415114199851 373719114843622671299777)
            ·
              refine ⟨280289336132717003474833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373719114843622671299777 280289336132717003474833)
              ·
                refine ⟨210217002099537752606125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280289336132717003474833 210217002099537752606125)
                ·
                  refine ⟨78831375787326657227297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210217002099537752606125 78831375787326657227297)
                  ·
                    rfl

theorem cell20_172714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_172714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172714 prefixEnd_172714 := by exact prefixLift 172714
  have htrace : WordTrace (prefixWord ++ tailWord_172714) baseStart_172714 baseEnd_172714 := by
    simpa [prefixWord, tailWord_172714, baseEnd_172714] using wordTrace_append hprefix tailTrace_172714
  have hstable : (prefixWord ++ tailWord_172714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172714).length < 2 ^ (prefixWord ++ tailWord_172714).sum := by decide
  have hdescent : baseEnd_172714 < baseStart_172714 := by decide
  rcases family_descends (prefixWord ++ tailWord_172714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172721 : List Nat := [1, 2, 2, 6, 1, 1, 1, 4, 2]
def baseStart_172721 : Nat := 118140960795 + 172721 * 2 ^ 59
def prefixEnd_172721 : Nat := 4983230072969 + 3 ^ 40 * 172721 * 2
def baseEnd_172721 : Nat := 78834570778065743993935

theorem tailTrace_172721 : CollatzResearch.WordTrace tailWord_172721 prefixEnd_172721 78834570778065743993935 := by
  unfold tailWord_172721
  simp only [CollatzResearch.WordTrace]
  refine ⟨6299652407268790243422017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4199768271512526828948011 6299652407268790243422017)
  ·
    refine ⟨4724739305451592682566513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6299652407268790243422017 4724739305451592682566513)
    ·
      refine ⟨3543554479088694511924885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4724739305451592682566513 3543554479088694511924885)
      ·
        refine ⟨166104116207282555246479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3543554479088694511924885 166104116207282555246479)
        ·
          refine ⟨249156174310923832869719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166104116207282555246479 249156174310923832869719)
          ·
            refine ⟨373734261466385749304579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249156174310923832869719 373734261466385749304579)
            ·
              refine ⟨560601392199578623956869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373734261466385749304579 560601392199578623956869)
              ·
                refine ⟨105112761037420991991913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 560601392199578623956869 105112761037420991991913)
                ·
                  refine ⟨78834570778065743993935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105112761037420991991913 78834570778065743993935)
                  ·
                    rfl

theorem cell20_172721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_172721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172721 prefixEnd_172721 := by exact prefixLift 172721
  have htrace : WordTrace (prefixWord ++ tailWord_172721) baseStart_172721 baseEnd_172721 := by
    simpa [prefixWord, tailWord_172721, baseEnd_172721] using wordTrace_append hprefix tailTrace_172721
  have hstable : (prefixWord ++ tailWord_172721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172721).length < 2 ^ (prefixWord ++ tailWord_172721).sum := by decide
  have hdescent : baseEnd_172721 < baseStart_172721 := by decide
  rcases family_descends (prefixWord ++ tailWord_172721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172746 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_172746 : Nat := 118140960795 + 172746 * 2 ^ 59
def prefixEnd_172746 : Nat := 4983230072969 + 3 ^ 40 * 172746 * 2
def baseEnd_172746 : Nat := 78845981459276768160499

theorem tailTrace_172746 : CollatzResearch.WordTrace tailWord_172746 prefixEnd_172746 78845981459276768160499 := by
  unfold tailWord_172746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575141058044554878270523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4200376154785479675388061 1575141058044554878270523)
  ·
    refine ⟨2362711587066832317405785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1575141058044554878270523 2362711587066832317405785)
    ·
      refine ⟨1772033690300124238054339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2362711587066832317405785 1772033690300124238054339)
      ·
        refine ⟨2658050535450186357081509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1772033690300124238054339 2658050535450186357081509)
        ·
          refine ⟨498384475396909941952783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2658050535450186357081509 498384475396909941952783)
          ·
            refine ⟨747576713095364912929175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498384475396909941952783 747576713095364912929175)
            ·
              refine ⟨1121365069643047369393763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747576713095364912929175 1121365069643047369393763)
              ·
                refine ⟨1682047604464571054090645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121365069643047369393763 1682047604464571054090645)
                ·
                  refine ⟨78845981459276768160499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1682047604464571054090645 78845981459276768160499)
                  ·
                    rfl

theorem cell20_172746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_172746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172746 prefixEnd_172746 := by exact prefixLift 172746
  have htrace : WordTrace (prefixWord ++ tailWord_172746) baseStart_172746 baseEnd_172746 := by
    simpa [prefixWord, tailWord_172746, baseEnd_172746] using wordTrace_append hprefix tailTrace_172746
  have hstable : (prefixWord ++ tailWord_172746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172746).length < 2 ^ (prefixWord ++ tailWord_172746).sum := by decide
  have hdescent : baseEnd_172746 < baseStart_172746 := by decide
  rcases family_descends (prefixWord ++ tailWord_172746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172777 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 3]
def baseStart_172777 : Nat := 118140960795 + 172777 * 2 ^ 59
def prefixEnd_172777 : Nat := 4983230072969 + 3 ^ 40 * 172777 * 2
def baseEnd_172777 : Nat := 78860130703978438127039

theorem tailTrace_172777 : CollatzResearch.WordTrace tailWord_172777 prefixEnd_172777 78860130703978438127039 := by
  unfold tailWord_172777
  simp only [CollatzResearch.WordTrace]
  refine ⟨6301694895065911807460585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4201129930043941204973723 6301694895065911807460585)
  ·
    refine ⟨4726271171299433855595439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6301694895065911807460585 4726271171299433855595439)
    ·
      refine ⟨7089406756949150783393159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726271171299433855595439 7089406756949150783393159)
      ·
        refine ⟨10634110135423726175089739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7089406756949150783393159 10634110135423726175089739)
        ·
          refine ⟨15951165203135589262634609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10634110135423726175089739 15951165203135589262634609)
          ·
            refine ⟨11963373902351691946975957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15951165203135589262634609 11963373902351691946975957)
            ·
              refine ⟨280391575836367780007249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11963373902351691946975957 280391575836367780007249)
              ·
                refine ⟨210293681877275835005437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280391575836367780007249 210293681877275835005437)
                ·
                  refine ⟨78860130703978438127039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210293681877275835005437 78860130703978438127039)
                  ·
                    rfl

theorem cell20_172777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_172777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172777 prefixEnd_172777 := by exact prefixLift 172777
  have htrace : WordTrace (prefixWord ++ tailWord_172777) baseStart_172777 baseEnd_172777 := by
    simpa [prefixWord, tailWord_172777, baseEnd_172777] using wordTrace_append hprefix tailTrace_172777
  have hstable : (prefixWord ++ tailWord_172777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172777).length < 2 ^ (prefixWord ++ tailWord_172777).sum := by decide
  have hdescent : baseEnd_172777 < baseStart_172777 := by decide
  rcases family_descends (prefixWord ++ tailWord_172777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172784 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_172784 : Nat := 118140960795 + 172784 * 2 ^ 59
def prefixEnd_172784 : Nat := 4983230072969 + 3 ^ 40 * 172784 * 2
def baseEnd_172784 : Nat := 78863325694717524893677

theorem tailTrace_172784 : CollatzResearch.WordTrace tailWord_172784 prefixEnd_172784 78863325694717524893677 := by
  unfold tailWord_172784
  simp only [CollatzResearch.WordTrace]
  refine ⟨3150975103020276001482703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4201300137360368001976937 3150975103020276001482703)
  ·
    refine ⟨4726462654530414002224055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3150975103020276001482703 4726462654530414002224055)
    ·
      refine ⟨7089693981795621003336083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726462654530414002224055 7089693981795621003336083)
      ·
        refine ⟨10634540972693431505004125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7089693981795621003336083 10634540972693431505004125)
        ·
          refine ⟨3987952864760036814376547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10634540972693431505004125 3987952864760036814376547)
          ·
            refine ⟨5981929297140055221564821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3987952864760036814376547 5981929297140055221564821)
            ·
              refine ⟨280402935803440088510851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5981929297140055221564821 280402935803440088510851)
              ·
                refine ⟨420604403705160132766277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280402935803440088510851 420604403705160132766277)
                ·
                  refine ⟨78863325694717524893677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 420604403705160132766277 78863325694717524893677)
                  ·
                    rfl

theorem cell20_172784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_172784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172784 prefixEnd_172784 := by exact prefixLift 172784
  have htrace : WordTrace (prefixWord ++ tailWord_172784) baseStart_172784 baseEnd_172784 := by
    simpa [prefixWord, tailWord_172784, baseEnd_172784] using wordTrace_append hprefix tailTrace_172784
  have hstable : (prefixWord ++ tailWord_172784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172784).length < 2 ^ (prefixWord ++ tailWord_172784).sum := by decide
  have hdescent : baseEnd_172784 < baseStart_172784 := by decide
  rcases family_descends (prefixWord ++ tailWord_172784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172808 : List Nat := [2, 1, 3, 2, 2, 2, 4, 4]
def baseStart_172808 : Nat := 118140960795 + 172808 * 2 ^ 59
def prefixEnd_172808 : Nat := 4983230072969 + 3 ^ 40 * 172808 * 2
def baseEnd_172808 : Nat := 26291426649560036031193

theorem tailTrace_172808 : CollatzResearch.WordTrace tailWord_172808 prefixEnd_172808 26291426649560036031193 := by
  unfold tailWord_172808
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151412778976802050919539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4201883705302402734559385 3151412778976802050919539)
  ·
    refine ⟨4727119168465203076379309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3151412778976802050919539 4727119168465203076379309)
    ·
      refine ⟨1772669688174451153642241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4727119168465203076379309 1772669688174451153642241)
      ·
        refine ⟨1329502266130838365231681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1772669688174451153642241 1329502266130838365231681)
        ·
          refine ⟨997126699598128773923761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1329502266130838365231681 997126699598128773923761)
          ·
            refine ⟨747845024698596580442821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 997126699598128773923761 747845024698596580442821)
            ·
              refine ⟨140220942130986858833029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 747845024698596580442821 140220942130986858833029)
              ·
                refine ⟨26291426649560036031193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140220942130986858833029 26291426649560036031193)
                ·
                  rfl

theorem cell20_172808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_172808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172808 prefixEnd_172808 := by exact prefixLift 172808
  have htrace : WordTrace (prefixWord ++ tailWord_172808) baseStart_172808 baseEnd_172808 := by
    simpa [prefixWord, tailWord_172808, baseEnd_172808] using wordTrace_append hprefix tailTrace_172808
  have hstable : (prefixWord ++ tailWord_172808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172808).length < 2 ^ (prefixWord ++ tailWord_172808).sum := by decide
  have hdescent : baseEnd_172808 < baseStart_172808 := by decide
  rcases family_descends (prefixWord ++ tailWord_172808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172845 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 3]
def baseStart_172845 : Nat := 118140960795 + 172845 * 2 ^ 59
def prefixEnd_172845 : Nat := 4983230072969 + 3 ^ 40 * 172845 * 2
def baseEnd_172845 : Nat := 78891167756872423860095

theorem tailTrace_172845 : CollatzResearch.WordTrace tailWord_172845 prefixEnd_172845 78891167756872423860095 := by
  unfold tailWord_172845
  simp only [CollatzResearch.WordTrace]
  refine ⟨6304175058819559420935989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4202783372546372947290659 6304175058819559420935989)
  ·
    refine ⟨591016411764333695712749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6304175058819559420935989 591016411764333695712749)
    ·
      refine ⟨221631154411625135892281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 591016411764333695712749 221631154411625135892281)
      ·
        refine ⟨166223365808718851919211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221631154411625135892281 166223365808718851919211)
        ·
          refine ⟨249335048713078277878817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166223365808718851919211 249335048713078277878817)
          ·
            refine ⟨187001286534808708409113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249335048713078277878817 187001286534808708409113)
            ·
              refine ⟨140250964901106531306835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187001286534808708409113 140250964901106531306835)
              ·
                refine ⟨210376447351659796960253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140250964901106531306835 210376447351659796960253)
                ·
                  refine ⟨78891167756872423860095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210376447351659796960253 78891167756872423860095)
                  ·
                    rfl

theorem cell20_172845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_172845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172845 prefixEnd_172845 := by exact prefixLift 172845
  have htrace : WordTrace (prefixWord ++ tailWord_172845) baseStart_172845 baseEnd_172845 := by
    simpa [prefixWord, tailWord_172845, baseEnd_172845] using wordTrace_append hprefix tailTrace_172845
  have hstable : (prefixWord ++ tailWord_172845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172845).length < 2 ^ (prefixWord ++ tailWord_172845).sum := by decide
  have hdescent : baseEnd_172845 < baseStart_172845 := by decide
  rcases family_descends (prefixWord ++ tailWord_172845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172846 : List Nat := [4, 1, 3, 2, 1, 1, 1, 7]
def baseStart_172846 : Nat := 118140960795 + 172846 * 2 ^ 59
def prefixEnd_172846 : Nat := 4983230072969 + 3 ^ 40 * 172846 * 2
def baseEnd_172846 : Nat := 26297208061373621608919

theorem tailTrace_172846 : CollatzResearch.WordTrace tailWord_172846 prefixEnd_172846 26297208061373621608919 := by
  unfold tailWord_172846
  simp only [CollatzResearch.WordTrace]
  refine ⟨788026441476992073965299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4202807687877291061148261 788026441476992073965299)
  ·
    refine ⟨1182039662215488110947949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 788026441476992073965299 1182039662215488110947949)
    ·
      refine ⟨443264873330808041605481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1182039662215488110947949 443264873330808041605481)
      ·
        refine ⟨332448654998106031204111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443264873330808041605481 332448654998106031204111)
        ·
          refine ⟨498672982497159046806167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332448654998106031204111 498672982497159046806167)
          ·
            refine ⟨748009473745738570209251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498672982497159046806167 748009473745738570209251)
            ·
              refine ⟨1122014210618607855313877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748009473745738570209251 1122014210618607855313877)
              ·
                refine ⟨26297208061373621608919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1122014210618607855313877 26297208061373621608919)
                ·
                  rfl

theorem cell20_172846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_172846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172846 prefixEnd_172846 := by exact prefixLift 172846
  have htrace : WordTrace (prefixWord ++ tailWord_172846) baseStart_172846 baseEnd_172846 := by
    simpa [prefixWord, tailWord_172846, baseEnd_172846] using wordTrace_append hprefix tailTrace_172846
  have hstable : (prefixWord ++ tailWord_172846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172846).length < 2 ^ (prefixWord ++ tailWord_172846).sum := by decide
  have hdescent : baseEnd_172846 < baseStart_172846 := by decide
  rcases family_descends (prefixWord ++ tailWord_172846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172874 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_172874 : Nat := 118140960795 + 172874 * 2 ^ 59
def prefixEnd_172874 : Nat := 4983230072969 + 3 ^ 40 * 172874 * 2
def baseEnd_172874 : Nat := 78904404147077211893309

theorem tailTrace_172874 : CollatzResearch.WordTrace tailWord_172874 prefixEnd_172874 78904404147077211893309 := by
  unfold tailWord_172874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1576308193928624343435419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4203488517142998249161117 1576308193928624343435419)
  ·
    refine ⟨2364462290892936515153129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1576308193928624343435419 2364462290892936515153129)
    ·
      refine ⟨1773346718169702386364847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2364462290892936515153129 1773346718169702386364847)
      ·
        refine ⟨2660020077254553579547271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1773346718169702386364847 2660020077254553579547271)
        ·
          refine ⟨3990030115881830369320907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660020077254553579547271 3990030115881830369320907)
          ·
            refine ⟨5985045173822745553981361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990030115881830369320907 5985045173822745553981361)
            ·
              refine ⟨4488783880367059165486021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5985045173822745553981361 4488783880367059165486021)
              ·
                refine ⟨841646977568823593528629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4488783880367059165486021 841646977568823593528629)
                ·
                  refine ⟨78904404147077211893309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 841646977568823593528629 78904404147077211893309)
                  ·
                    rfl

theorem cell20_172874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_172874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172874 prefixEnd_172874 := by exact prefixLift 172874
  have htrace : WordTrace (prefixWord ++ tailWord_172874) baseStart_172874 baseEnd_172874 := by
    simpa [prefixWord, tailWord_172874, baseEnd_172874] using wordTrace_append hprefix tailTrace_172874
  have hstable : (prefixWord ++ tailWord_172874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172874).length < 2 ^ (prefixWord ++ tailWord_172874).sum := by decide
  have hdescent : baseEnd_172874 < baseStart_172874 := by decide
  rcases family_descends (prefixWord ++ tailWord_172874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172884 : List Nat := [2, 4, 1, 1, 5, 7]
def baseStart_172884 : Nat := 118140960795 + 172884 * 2 ^ 59
def prefixEnd_172884 : Nat := 4983230072969 + 3 ^ 40 * 172884 * 2
def baseEnd_172884 : Nat := 2922554385909689687405

theorem tailTrace_172884 : CollatzResearch.WordTrace tailWord_172884 prefixEnd_172884 2922554385909689687405 := by
  unfold tailWord_172884
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152798752839134540802853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4203731670452179387737137 3152798752839134540802853)
  ·
    refine ⟨591149766157337726400535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3152798752839134540802853 591149766157337726400535)
    ·
      refine ⟨886724649236006589600803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 591149766157337726400535 886724649236006589600803)
      ·
        refine ⟨1330086973854009884401205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886724649236006589600803 1330086973854009884401205)
        ·
          refine ⟨124695653798813426662613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1330086973854009884401205 124695653798813426662613)
          ·
            refine ⟨2922554385909689687405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 124695653798813426662613 2922554385909689687405)
            ·
              rfl

theorem cell20_172884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 7].length) (baseStart_172884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172884 prefixEnd_172884 := by exact prefixLift 172884
  have htrace : WordTrace (prefixWord ++ tailWord_172884) baseStart_172884 baseEnd_172884 := by
    simpa [prefixWord, tailWord_172884, baseEnd_172884] using wordTrace_append hprefix tailTrace_172884
  have hstable : (prefixWord ++ tailWord_172884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172884).length < 2 ^ (prefixWord ++ tailWord_172884).sum := by decide
  have hdescent : baseEnd_172884 < baseStart_172884 := by decide
  rcases family_descends (prefixWord ++ tailWord_172884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172946 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_172946 : Nat := 118140960795 + 172946 * 2 ^ 59
def prefixEnd_172946 : Nat := 4983230072969 + 3 ^ 40 * 172946 * 2
def baseEnd_172946 : Nat := 78937266908964961493015

theorem tailTrace_172946 : CollatzResearch.WordTrace tailWord_172946 prefixEnd_172946 78937266908964961493015 := by
  unfold tailWord_172946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1576964707863413417590673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4205239220969102446908461 1576964707863413417590673)
  ·
    refine ⟨1182723530897560063193005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1576964707863413417590673 1182723530897560063193005)
    ·
      refine ⟨443521324086585023697377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1182723530897560063193005 443521324086585023697377)
      ·
        refine ⟨332640993064938767773033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443521324086585023697377 332640993064938767773033)
        ·
          refine ⟨249480744798704075829775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332640993064938767773033 249480744798704075829775)
          ·
            refine ⟨374221117198056113744663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249480744798704075829775 374221117198056113744663)
            ·
              refine ⟨561331675797084170616995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374221117198056113744663 561331675797084170616995)
              ·
                refine ⟨841997513695626255925493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561331675797084170616995 841997513695626255925493)
                ·
                  refine ⟨78937266908964961493015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 841997513695626255925493 78937266908964961493015)
                  ·
                    rfl

theorem cell20_172946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_172946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172946 prefixEnd_172946 := by exact prefixLift 172946
  have htrace : WordTrace (prefixWord ++ tailWord_172946) baseStart_172946 baseEnd_172946 := by
    simpa [prefixWord, tailWord_172946, baseEnd_172946] using wordTrace_append hprefix tailTrace_172946
  have hstable : (prefixWord ++ tailWord_172946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172946).length < 2 ^ (prefixWord ++ tailWord_172946).sum := by decide
  have hdescent : baseEnd_172946 < baseStart_172946 := by decide
  rcases family_descends (prefixWord ++ tailWord_172946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172973 : List Nat := [1, 5, 2, 3, 2, 1, 2, 4]
def baseStart_172973 : Nat := 118140960795 + 172973 * 2 ^ 59
def prefixEnd_172973 : Nat := 4983230072969 + 3 ^ 40 * 172973 * 2
def baseEnd_172973 : Nat := 26316530148224289197635

theorem tailTrace_172973 : CollatzResearch.WordTrace tailWord_172973 prefixEnd_172973 26316530148224289197635 := by
  unfold tailWord_172973
  simp only [CollatzResearch.WordTrace]
  refine ⟨6308843602355837281595573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4205895734903891521063715 6308843602355837281595573)
  ·
    refine ⟨591454087720859745149585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6308843602355837281595573 591454087720859745149585)
    ·
      refine ⟨443590565790644808862189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591454087720859745149585 443590565790644808862189)
      ·
        refine ⟨166346462171491803323321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443590565790644808862189 166346462171491803323321)
        ·
          refine ⟨124759846628618852492491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166346462171491803323321 124759846628618852492491)
          ·
            refine ⟨187139769942928278738737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124759846628618852492491 187139769942928278738737)
            ·
              refine ⟨140354827457196209054053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187139769942928278738737 140354827457196209054053)
              ·
                refine ⟨26316530148224289197635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140354827457196209054053 26316530148224289197635)
                ·
                  rfl

theorem cell20_172973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 4].length) (baseStart_172973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172973 prefixEnd_172973 := by exact prefixLift 172973
  have htrace : WordTrace (prefixWord ++ tailWord_172973) baseStart_172973 baseEnd_172973 := by
    simpa [prefixWord, tailWord_172973, baseEnd_172973] using wordTrace_append hprefix tailTrace_172973
  have hstable : (prefixWord ++ tailWord_172973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172973).length < 2 ^ (prefixWord ++ tailWord_172973).sum := by decide
  have hdescent : baseEnd_172973 < baseStart_172973 := by decide
  rcases family_descends (prefixWord ++ tailWord_172973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172977 : List Nat := [1, 2, 2, 4, 3, 2, 2, 4]
def baseStart_172977 : Nat := 118140960795 + 172977 * 2 ^ 59
def prefixEnd_172977 : Nat := 4983230072969 + 3 ^ 40 * 172977 * 2
def baseEnd_172977 : Nat := 26317138717888877153185

theorem tailTrace_172977 : CollatzResearch.WordTrace tailWord_172977 prefixEnd_172977 26317138717888877153185 := by
  unfold tailWord_172977
  simp only [CollatzResearch.WordTrace]
  refine ⟨6308989494341345964741185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4205992996227563976494123 6308989494341345964741185)
  ·
    refine ⟨4731742120756009473555889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6308989494341345964741185 4731742120756009473555889)
    ·
      refine ⟨3548806590567007105166917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4731742120756009473555889 3548806590567007105166917)
      ·
        refine ⟨665401235731313832218797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3548806590567007105166917 665401235731313832218797)
        ·
          refine ⟨249525463399242687082049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 665401235731313832218797 249525463399242687082049)
          ·
            refine ⟨187144097549432015311537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249525463399242687082049 187144097549432015311537)
            ·
              refine ⟨140358073162074011483653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187144097549432015311537 140358073162074011483653)
              ·
                refine ⟨26317138717888877153185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140358073162074011483653 26317138717888877153185)
                ·
                  rfl

theorem cell20_172977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 4].length) (baseStart_172977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172977 prefixEnd_172977 := by exact prefixLift 172977
  have htrace : WordTrace (prefixWord ++ tailWord_172977) baseStart_172977 baseEnd_172977 := by
    simpa [prefixWord, tailWord_172977, baseEnd_172977] using wordTrace_append hprefix tailTrace_172977
  have hstable : (prefixWord ++ tailWord_172977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172977).length < 2 ^ (prefixWord ++ tailWord_172977).sum := by decide
  have hdescent : baseEnd_172977 < baseStart_172977 := by decide
  rcases family_descends (prefixWord ++ tailWord_172977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172981 : List Nat := [1, 3, 3, 2, 1, 1, 3, 6]
def baseStart_172981 : Nat := 118140960795 + 172981 * 2 ^ 59
def prefixEnd_172981 : Nat := 4983230072969 + 3 ^ 40 * 172981 * 2
def baseEnd_172981 : Nat := 26317747287553465108735

theorem tailTrace_172981 : CollatzResearch.WordTrace tailWord_172981 prefixEnd_172981 26317747287553465108735 := by
  unfold tailWord_172981
  simp only [CollatzResearch.WordTrace]
  refine ⟨6309135386326854647886797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4206090257551236431924531 6309135386326854647886797)
  ·
    refine ⟨2365925769872570492957549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6309135386326854647886797 2365925769872570492957549)
    ·
      refine ⟨887222163702213934859081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2365925769872570492957549 887222163702213934859081)
      ·
        refine ⟨665416622776660451144311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 887222163702213934859081 665416622776660451144311)
        ·
          refine ⟨998124934164990676716467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665416622776660451144311 998124934164990676716467)
          ·
            refine ⟨1497187401247486015074701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998124934164990676716467 1497187401247486015074701)
            ·
              refine ⟨561445275467807255653013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1497187401247486015074701 561445275467807255653013)
              ·
                refine ⟨26317747287553465108735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 561445275467807255653013 26317747287553465108735)
                ·
                  rfl

theorem cell20_172981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_172981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_172981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_172981 prefixEnd_172981 := by exact prefixLift 172981
  have htrace : WordTrace (prefixWord ++ tailWord_172981) baseStart_172981 baseEnd_172981 := by
    simpa [prefixWord, tailWord_172981, baseEnd_172981] using wordTrace_append hprefix tailTrace_172981
  have hstable : (prefixWord ++ tailWord_172981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172981).length < 2 ^ (prefixWord ++ tailWord_172981).sum := by decide
  have hdescent : baseEnd_172981 < baseStart_172981 := by decide
  rcases family_descends (prefixWord ++ tailWord_172981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173067 : List Nat := [1, 1, 1, 1, 6, 3, 1, 4, 2]
def baseStart_173067 : Nat := 118140960795 + 173067 * 2 ^ 59
def prefixEnd_173067 : Nat := 4983230072969 + 3 ^ 40 * 173067 * 2
def baseEnd_173067 : Nat := 78992494606026318459187

theorem tailTrace_173067 : CollatzResearch.WordTrace tailWord_173067 prefixEnd_173067 78992494606026318459187 := by
  unfold tailWord_173067
  simp only [CollatzResearch.WordTrace]
  refine ⟨6312272064015291335517455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4208181376010194223678303 6312272064015291335517455)
  ·
    refine ⟨9468408096022937003276183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6312272064015291335517455 9468408096022937003276183)
    ·
      refine ⟨14202612144034405504914275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9468408096022937003276183 14202612144034405504914275)
      ·
        refine ⟨21303918216051608257371413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14202612144034405504914275 21303918216051608257371413)
        ·
          refine ⟨998621166377419137064285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21303918216051608257371413 998621166377419137064285)
          ·
            refine ⟨374482937391532176399107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 998621166377419137064285 374482937391532176399107)
            ·
              refine ⟨561724406087298264598661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374482937391532176399107 561724406087298264598661)
              ·
                refine ⟨105323326141368424612249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 561724406087298264598661 105323326141368424612249)
                ·
                  refine ⟨78992494606026318459187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105323326141368424612249 78992494606026318459187)
                  ·
                    rfl

theorem cell20_173067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 2].length) (baseStart_173067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173067 prefixEnd_173067 := by exact prefixLift 173067
  have htrace : WordTrace (prefixWord ++ tailWord_173067) baseStart_173067 baseEnd_173067 := by
    simpa [prefixWord, tailWord_173067, baseEnd_173067] using wordTrace_append hprefix tailTrace_173067
  have hstable : (prefixWord ++ tailWord_173067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173067).length < 2 ^ (prefixWord ++ tailWord_173067).sum := by decide
  have hdescent : baseEnd_173067 < baseStart_173067 := by decide
  rcases family_descends (prefixWord ++ tailWord_173067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173105 : List Nat := [1, 2, 2, 3, 1, 2, 4, 3, 2]
def baseStart_173105 : Nat := 118140960795 + 173105 * 2 ^ 59
def prefixEnd_173105 : Nat := 4983230072969 + 3 ^ 40 * 173105 * 2
def baseEnd_173105 : Nat := 79009838841467075192365

theorem tailTrace_173105 : CollatzResearch.WordTrace tailWord_173105 prefixEnd_173105 79009838841467075192365 := by
  unfold tailWord_173105
  simp only [CollatzResearch.WordTrace]
  refine ⟨6313658037877623825400769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4209105358585082550267179 6313658037877623825400769)
  ·
    refine ⟨4735243528408217869050577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6313658037877623825400769 4735243528408217869050577)
    ·
      refine ⟨3551432646306163401787933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4735243528408217869050577 3551432646306163401787933)
      ·
        refine ⟨1331787242364811275670475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3551432646306163401787933 1331787242364811275670475)
        ·
          refine ⟨1997680863547216913505713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1331787242364811275670475 1997680863547216913505713)
          ·
            refine ⟨1498260647660412685129285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1997680863547216913505713 1498260647660412685129285)
            ·
              refine ⟨280923871436327378461741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1498260647660412685129285 280923871436327378461741)
              ·
                refine ⟨105346451788622766923153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280923871436327378461741 105346451788622766923153)
                ·
                  refine ⟨79009838841467075192365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105346451788622766923153 79009838841467075192365)
                  ·
                    rfl

theorem cell20_173105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_173105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173105 prefixEnd_173105 := by exact prefixLift 173105
  have htrace : WordTrace (prefixWord ++ tailWord_173105) baseStart_173105 baseEnd_173105 := by
    simpa [prefixWord, tailWord_173105, baseEnd_173105] using wordTrace_append hprefix tailTrace_173105
  have hstable : (prefixWord ++ tailWord_173105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173105).length < 2 ^ (prefixWord ++ tailWord_173105).sum := by decide
  have hdescent : baseEnd_173105 < baseStart_173105 := by decide
  rcases family_descends (prefixWord ++ tailWord_173105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173109 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_173109 : Nat := 118140960795 + 173109 * 2 ^ 59
def prefixEnd_173109 : Nat := 4983230072969 + 3 ^ 40 * 173109 * 2
def baseEnd_173109 : Nat := 79011664550460839059015

theorem tailTrace_173109 : CollatzResearch.WordTrace tailWord_173109 prefixEnd_173109 79011664550460839059015 := by
  unfold tailWord_173109
  simp only [CollatzResearch.WordTrace]
  refine ⟨6313803929863132508546381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4209202619908755005697587 6313803929863132508546381)
  ·
    refine ⟨2367676473698674690704893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6313803929863132508546381 2367676473698674690704893)
    ·
      refine ⟨887878677637003009014335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2367676473698674690704893 887878677637003009014335)
      ·
        refine ⟨1331818016455504513521503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887878677637003009014335 1331818016455504513521503)
        ·
          refine ⟨1997727024683256770282255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1331818016455504513521503 1997727024683256770282255)
          ·
            refine ⟨2996590537024885155423383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997727024683256770282255 2996590537024885155423383)
            ·
              refine ⟨4494885805537327733135075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996590537024885155423383 4494885805537327733135075)
              ·
                refine ⟨6742328708305991599702613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4494885805537327733135075 6742328708305991599702613)
                ·
                  refine ⟨79011664550460839059015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6742328708305991599702613 79011664550460839059015)
                  ·
                    rfl

theorem cell20_173109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_173109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173109 prefixEnd_173109 := by exact prefixLift 173109
  have htrace : WordTrace (prefixWord ++ tailWord_173109) baseStart_173109 baseEnd_173109 := by
    simpa [prefixWord, tailWord_173109, baseEnd_173109] using wordTrace_append hprefix tailTrace_173109
  have hstable : (prefixWord ++ tailWord_173109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173109).length < 2 ^ (prefixWord ++ tailWord_173109).sum := by decide
  have hdescent : baseEnd_173109 < baseStart_173109 := by decide
  rcases family_descends (prefixWord ++ tailWord_173109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173233 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 3]
def baseStart_173233 : Nat := 118140960795 + 173233 * 2 ^ 59
def prefixEnd_173233 : Nat := 4983230072969 + 3 ^ 40 * 173233 * 2
def baseEnd_173233 : Nat := 79068261529267518925175

theorem tailTrace_173233 : CollatzResearch.WordTrace tailWord_173233 prefixEnd_173233 79068261529267518925175 := by
  unfold tailWord_173233
  simp only [CollatzResearch.WordTrace]
  refine ⟨6318326581413901686060353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4212217720942601124040235 6318326581413901686060353)
  ·
    refine ⟨4738744936060426264545265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6318326581413901686060353 4738744936060426264545265)
    ·
      refine ⟨3554058702045319698408949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4738744936060426264545265 3554058702045319698408949)
      ·
        refine ⟨333193003316748721725839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3554058702045319698408949 333193003316748721725839)
        ·
          refine ⟨499789504975123082588759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333193003316748721725839 499789504975123082588759)
          ·
            refine ⟨749684257462684623883139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499789504975123082588759 749684257462684623883139)
            ·
              refine ⟨1124526386194026935824709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749684257462684623883139 1124526386194026935824709)
              ·
                refine ⟨210848697411380050467133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1124526386194026935824709 210848697411380050467133)
                ·
                  refine ⟨79068261529267518925175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210848697411380050467133 79068261529267518925175)
                  ·
                    rfl

theorem cell20_173233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_173233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173233 prefixEnd_173233 := by exact prefixLift 173233
  have htrace : WordTrace (prefixWord ++ tailWord_173233) baseStart_173233 baseEnd_173233 := by
    simpa [prefixWord, tailWord_173233, baseEnd_173233] using wordTrace_append hprefix tailTrace_173233
  have hstable : (prefixWord ++ tailWord_173233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173233).length < 2 ^ (prefixWord ++ tailWord_173233).sum := by decide
  have hdescent : baseEnd_173233 < baseStart_173233 := by decide
  rcases family_descends (prefixWord ++ tailWord_173233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173285 : List Nat := [1, 3, 1, 4, 3, 1, 7]
def baseStart_173285 : Nat := 118140960795 + 173285 * 2 ^ 59
def prefixEnd_173285 : Nat := 4983230072969 + 3 ^ 40 * 173285 * 2
def baseEnd_173285 : Nat := 8787999527354049910181

theorem tailTrace_173285 : CollatzResearch.WordTrace tailWord_173285 prefixEnd_173285 8787999527354049910181 := by
  unfold tailWord_173285
  simp only [CollatzResearch.WordTrace]
  refine ⟨6320223177225514566953309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4213482118150343044635539 6320223177225514566953309)
  ·
    refine ⟨2370083691459567962607491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6320223177225514566953309 2370083691459567962607491)
    ·
      refine ⟨3555125537189351943911237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370083691459567962607491 3555125537189351943911237)
      ·
        refine ⟨666586038223003489483357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3555125537189351943911237 666586038223003489483357)
        ·
          refine ⟨249969764333626308556259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 666586038223003489483357 249969764333626308556259)
          ·
            refine ⟨374954646500439462834389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249969764333626308556259 374954646500439462834389)
            ·
              refine ⟨8787999527354049910181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 374954646500439462834389 8787999527354049910181)
              ·
                rfl

theorem cell20_173285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 7].length) (baseStart_173285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173285 prefixEnd_173285 := by exact prefixLift 173285
  have htrace : WordTrace (prefixWord ++ tailWord_173285) baseStart_173285 baseEnd_173285 := by
    simpa [prefixWord, tailWord_173285, baseEnd_173285] using wordTrace_append hprefix tailTrace_173285
  have hstable : (prefixWord ++ tailWord_173285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173285).length < 2 ^ (prefixWord ++ tailWord_173285).sum := by decide
  have hdescent : baseEnd_173285 < baseStart_173285 := by decide
  rcases family_descends (prefixWord ++ tailWord_173285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173292 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_173292 : Nat := 118140960795 + 173292 * 2 ^ 59
def prefixEnd_173292 : Nat := 4983230072969 + 3 ^ 40 * 173292 * 2
def baseEnd_173292 : Nat := 79095190736925535958267

theorem tailTrace_173292 : CollatzResearch.WordTrace tailWord_173292 prefixEnd_173292 79095190736925535958267 := by
  unfold tailWord_173292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160239244100077381229065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4213652325466769841638753 3160239244100077381229065)
  ·
    refine ⟨2370179433075058035921799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3160239244100077381229065 2370179433075058035921799)
    ·
      refine ⟨3555269149612587053882699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370179433075058035921799 3555269149612587053882699)
      ·
        refine ⟨5332903724418880580824049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555269149612587053882699 5332903724418880580824049)
        ·
          refine ⟨3999677793314160435618037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5332903724418880580824049 3999677793314160435618037)
          ·
            refine ⟨374969793123202540839191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3999677793314160435618037 374969793123202540839191)
            ·
              refine ⟨562454689684803811258787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374969793123202540839191 562454689684803811258787)
              ·
                refine ⟨843682034527205716888181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562454689684803811258787 843682034527205716888181)
                ·
                  refine ⟨79095190736925535958267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 843682034527205716888181 79095190736925535958267)
                  ·
                    rfl

theorem cell20_173292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_173292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173292 prefixEnd_173292 := by exact prefixLift 173292
  have htrace : WordTrace (prefixWord ++ tailWord_173292) baseStart_173292 baseEnd_173292 := by
    simpa [prefixWord, tailWord_173292, baseEnd_173292] using wordTrace_append hprefix tailTrace_173292
  have hstable : (prefixWord ++ tailWord_173292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173292).length < 2 ^ (prefixWord ++ tailWord_173292).sum := by decide
  have hdescent : baseEnd_173292 < baseStart_173292 := by decide
  rcases family_descends (prefixWord ++ tailWord_173292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173299 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_173299 : Nat := 118140960795 + 173299 * 2 ^ 59
def prefixEnd_173299 : Nat := 4983230072969 + 3 ^ 40 * 173299 * 2
def baseEnd_173299 : Nat := 79098385727664622724905

theorem tailTrace_173299 : CollatzResearch.WordTrace tailWord_173299 prefixEnd_173299 79098385727664622724905 := by
  unfold tailWord_173299
  simp only [CollatzResearch.WordTrace]
  refine ⟨6320733799174794957962951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4213822532783196638641967 6320733799174794957962951)
  ·
    refine ⟨9481100698762192436944427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6320733799174794957962951 9481100698762192436944427)
    ·
      refine ⟨14221651048143288655416641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9481100698762192436944427 14221651048143288655416641)
      ·
        refine ⟨10666238286107466491562481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14221651048143288655416641 10666238286107466491562481)
        ·
          refine ⟨7999678714580599868671861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10666238286107466491562481 7999678714580599868671861)
          ·
            refine ⟨749969879491931237687987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7999678714580599868671861 749969879491931237687987)
            ·
              refine ⟨1124954819237896856531981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749969879491931237687987 1124954819237896856531981)
              ·
                refine ⟨421858057214211321199493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1124954819237896856531981 421858057214211321199493)
                ·
                  refine ⟨79098385727664622724905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421858057214211321199493 79098385727664622724905)
                  ·
                    rfl

theorem cell20_173299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_173299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173299 prefixEnd_173299 := by exact prefixLift 173299
  have htrace : WordTrace (prefixWord ++ tailWord_173299) baseStart_173299 baseEnd_173299 := by
    simpa [prefixWord, tailWord_173299, baseEnd_173299] using wordTrace_append hprefix tailTrace_173299
  have hstable : (prefixWord ++ tailWord_173299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173299).length < 2 ^ (prefixWord ++ tailWord_173299).sum := by decide
  have hdescent : baseEnd_173299 < baseStart_173299 := by decide
  rcases family_descends (prefixWord ++ tailWord_173299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173306 : List Nat := [3, 1, 1, 1, 1, 4, 2, 7]
def baseStart_173306 : Nat := 118140960795 + 173306 * 2 ^ 59
def prefixEnd_173306 : Nat := 4983230072969 + 3 ^ 40 * 173306 * 2
def baseEnd_173306 : Nat := 26367193572801236497181

theorem tailTrace_173306 : CollatzResearch.WordTrace tailWord_173306 prefixEnd_173306 26367193572801236497181 := by
  unfold tailWord_173306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580247277537358788366943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4213992740099623435645181 1580247277537358788366943)
  ·
    refine ⟨2370370916306038182550415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1580247277537358788366943 2370370916306038182550415)
    ·
      refine ⟨3555556374459057273825623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370370916306038182550415 3555556374459057273825623)
      ·
        refine ⟨5333334561688585910738435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555556374459057273825623 5333334561688585910738435)
        ·
          refine ⟨8000001842532878866107653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5333334561688585910738435 8000001842532878866107653)
          ·
            refine ⟨1500000345474914787395185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8000001842532878866107653 1500000345474914787395185)
            ·
              refine ⟨1125000259106186090546389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1500000345474914787395185 1125000259106186090546389)
              ·
                refine ⟨26367193572801236497181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1125000259106186090546389 26367193572801236497181)
                ·
                  rfl

theorem cell20_173306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_173306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173306 prefixEnd_173306 := by exact prefixLift 173306
  have htrace : WordTrace (prefixWord ++ tailWord_173306) baseStart_173306 baseEnd_173306 := by
    simpa [prefixWord, tailWord_173306, baseEnd_173306] using wordTrace_append hprefix tailTrace_173306
  have hstable : (prefixWord ++ tailWord_173306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173306).length < 2 ^ (prefixWord ++ tailWord_173306).sum := by decide
  have hdescent : baseEnd_173306 < baseStart_173306 := by decide
  rcases family_descends (prefixWord ++ tailWord_173306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173316 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_173316 : Nat := 118140960795 + 173316 * 2 ^ 59
def prefixEnd_173316 : Nat := 4983230072969 + 3 ^ 40 * 173316 * 2
def baseEnd_173316 : Nat := 79106144990888119158169

theorem tailTrace_173316 : CollatzResearch.WordTrace tailWord_173316 prefixEnd_173316 79106144990888119158169 := by
  unfold tailWord_173316
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160676920056603430665901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4214235893408804574221201 3160676920056603430665901)
  ·
    refine ⟨1185253845021226286499713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3160676920056603430665901 1185253845021226286499713)
    ·
      refine ⟨888940383765919714874785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1185253845021226286499713 888940383765919714874785)
      ·
        refine ⟨666705287824439786156089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 888940383765919714874785 666705287824439786156089)
        ·
          refine ⟨500028965868329839617067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 666705287824439786156089 500028965868329839617067)
          ·
            refine ⟨750043448802494759425601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500028965868329839617067 750043448802494759425601)
            ·
              refine ⟨562532586601871069569201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750043448802494759425601 562532586601871069569201)
              ·
                refine ⟨421899439951403302176901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562532586601871069569201 421899439951403302176901)
                ·
                  refine ⟨79106144990888119158169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421899439951403302176901 79106144990888119158169)
                  ·
                    rfl

theorem cell20_173316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_173316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173316 prefixEnd_173316 := by exact prefixLift 173316
  have htrace : WordTrace (prefixWord ++ tailWord_173316) baseStart_173316 baseEnd_173316 := by
    simpa [prefixWord, tailWord_173316, baseEnd_173316] using wordTrace_append hprefix tailTrace_173316
  have hstable : (prefixWord ++ tailWord_173316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173316).length < 2 ^ (prefixWord ++ tailWord_173316).sum := by decide
  have hdescent : baseEnd_173316 < baseStart_173316 := by decide
  rcases family_descends (prefixWord ++ tailWord_173316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173323 : List Nat := [1, 1, 1, 1, 5, 3, 4, 4]
def baseStart_173323 : Nat := 118140960795 + 173323 * 2 ^ 59
def prefixEnd_173323 : Nat := 4983230072969 + 3 ^ 40 * 173323 * 2
def baseEnd_173323 : Nat := 26369779993875735308269

theorem tailTrace_173323 : CollatzResearch.WordTrace tailWord_173323 prefixEnd_173323 26369779993875735308269 := by
  unfold tailWord_173323
  simp only [CollatzResearch.WordTrace]
  refine ⟨6321609151087847056836623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4214406100725231371224415 6321609151087847056836623)
  ·
    refine ⟨9482413726631770585254935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6321609151087847056836623 9482413726631770585254935)
    ·
      refine ⟨14223620589947655877882403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9482413726631770585254935 14223620589947655877882403)
      ·
        refine ⟨21335430884921483816823605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14223620589947655877882403 21335430884921483816823605)
        ·
          refine ⟨2000196645461389107827213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21335430884921483816823605 2000196645461389107827213)
          ·
            refine ⟨750073742048020915435205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2000196645461389107827213 750073742048020915435205)
            ·
              refine ⟨140638826634003921644101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 750073742048020915435205 140638826634003921644101)
              ·
                refine ⟨26369779993875735308269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140638826634003921644101 26369779993875735308269)
                ·
                  rfl

theorem cell20_173323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 4].length) (baseStart_173323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173323 prefixEnd_173323 := by exact prefixLift 173323
  have htrace : WordTrace (prefixWord ++ tailWord_173323) baseStart_173323 baseEnd_173323 := by
    simpa [prefixWord, tailWord_173323, baseEnd_173323] using wordTrace_append hprefix tailTrace_173323
  have hstable : (prefixWord ++ tailWord_173323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173323).length < 2 ^ (prefixWord ++ tailWord_173323).sum := by decide
  have hdescent : baseEnd_173323 < baseStart_173323 := by decide
  rcases family_descends (prefixWord ++ tailWord_173323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173361 : List Nat := [1, 2, 2, 3, 3, 2, 2, 5]
def baseStart_173361 : Nat := 118140960795 + 173361 * 2 ^ 59
def prefixEnd_173361 : Nat := 4983230072969 + 3 ^ 40 * 173361 * 2
def baseEnd_173361 : Nat := 26375561405689320885995

theorem tailTrace_173361 : CollatzResearch.WordTrace tailWord_173361 prefixEnd_173361 26375561405689320885995 := by
  unfold tailWord_173361
  simp only [CollatzResearch.WordTrace]
  refine ⟨6322995124950179546719937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4215330083300119697813291 6322995124950179546719937)
  ·
    refine ⟨4742246343712634660039953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6322995124950179546719937 4742246343712634660039953)
    ·
      refine ⟨3556684757784475995029965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4742246343712634660039953 3556684757784475995029965)
      ·
        refine ⟨1333756784169178498136237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3556684757784475995029965 1333756784169178498136237)
        ·
          refine ⟨500158794063441936801089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1333756784169178498136237 500158794063441936801089)
          ·
            refine ⟨375119095547581452600817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 500158794063441936801089 375119095547581452600817)
            ·
              refine ⟨281339321660686089450613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375119095547581452600817 281339321660686089450613)
              ·
                refine ⟨26375561405689320885995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281339321660686089450613 26375561405689320885995)
                ·
                  rfl

theorem cell20_173361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_173361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173361 prefixEnd_173361 := by exact prefixLift 173361
  have htrace : WordTrace (prefixWord ++ tailWord_173361) baseStart_173361 baseEnd_173361 := by
    simpa [prefixWord, tailWord_173361, baseEnd_173361] using wordTrace_append hprefix tailTrace_173361
  have hstable : (prefixWord ++ tailWord_173361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173361).length < 2 ^ (prefixWord ++ tailWord_173361).sum := by decide
  have hdescent : baseEnd_173361 < baseStart_173361 := by decide
  rcases family_descends (prefixWord ++ tailWord_173361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173392 : List Nat := [2, 1, 1, 1, 1, 5, 2, 5, 2]
def baseStart_173392 : Nat := 118140960795 + 173392 * 2 ^ 59
def prefixEnd_173392 : Nat := 4983230072969 + 3 ^ 40 * 173392 * 2
def baseEnd_173392 : Nat := 79140833461769632624525

theorem tailTrace_173392 : CollatzResearch.WordTrace tailWord_173392 prefixEnd_173392 79140833461769632624525 := by
  unfold tailWord_173392
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162062893918935920549215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4216083858558581227398953 3162062893918935920549215)
  ·
    refine ⟨4743094340878403880823823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3162062893918935920549215 4743094340878403880823823)
    ·
      refine ⟨7114641511317605821235735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4743094340878403880823823 7114641511317605821235735)
      ·
        refine ⟨10671962266976408731853603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7114641511317605821235735 10671962266976408731853603)
        ·
          refine ⟨16007943400464613097780405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10671962266976408731853603 16007943400464613097780405)
          ·
            refine ⟨1500744693793557477916913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16007943400464613097780405 1500744693793557477916913)
            ·
              refine ⟨1125558520345168108437685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1500744693793557477916913 1125558520345168108437685)
              ·
                refine ⟨105521111282359510166033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1125558520345168108437685 105521111282359510166033)
                ·
                  refine ⟨79140833461769632624525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105521111282359510166033 79140833461769632624525)
                  ·
                    rfl

theorem cell20_173392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_173392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173392 prefixEnd_173392 := by exact prefixLift 173392
  have htrace : WordTrace (prefixWord ++ tailWord_173392) baseStart_173392 baseEnd_173392 := by
    simpa [prefixWord, tailWord_173392, baseEnd_173392] using wordTrace_append hprefix tailTrace_173392
  have hstable : (prefixWord ++ tailWord_173392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173392).length < 2 ^ (prefixWord ++ tailWord_173392).sum := by decide
  have hdescent : baseEnd_173392 < baseStart_173392 := by decide
  rcases family_descends (prefixWord ++ tailWord_173392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173413 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_173413 : Nat := 118140960795 + 173413 * 2 ^ 59
def prefixEnd_173413 : Nat := 4983230072969 + 3 ^ 40 * 173413 * 2
def baseEnd_173413 : Nat := 79150418433986892924439

theorem tailTrace_173413 : CollatzResearch.WordTrace tailWord_173413 prefixEnd_173413 79150418433986892924439 := by
  unfold tailWord_173413
  simp only [CollatzResearch.WordTrace]
  refine ⟨6324891720761792427612893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4216594480507861618408595 6324891720761792427612893)
  ·
    refine ⟨2371834395285672160354835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6324891720761792427612893 2371834395285672160354835)
    ·
      refine ⟨3557751592928508240532253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2371834395285672160354835 3557751592928508240532253)
      ·
        refine ⟨1334156847348190590199595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3557751592928508240532253 1334156847348190590199595)
        ·
          refine ⟨2001235271022285885299393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334156847348190590199595 2001235271022285885299393)
          ·
            refine ⟨1500926453266714413974545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2001235271022285885299393 1500926453266714413974545)
            ·
              refine ⟨1125694839950035810480909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1500926453266714413974545 1125694839950035810480909)
              ·
                refine ⟨422135564981263428930341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1125694839950035810480909 422135564981263428930341)
                ·
                  refine ⟨79150418433986892924439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422135564981263428930341 79150418433986892924439)
                  ·
                    rfl

theorem cell20_173413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_173413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173413 prefixEnd_173413 := by exact prefixLift 173413
  have htrace : WordTrace (prefixWord ++ tailWord_173413) baseStart_173413 baseEnd_173413 := by
    simpa [prefixWord, tailWord_173413, baseEnd_173413] using wordTrace_append hprefix tailTrace_173413
  have hstable : (prefixWord ++ tailWord_173413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173413).length < 2 ^ (prefixWord ++ tailWord_173413).sum := by decide
  have hdescent : baseEnd_173413 < baseStart_173413 := by decide
  rcases family_descends (prefixWord ++ tailWord_173413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173416 : List Nat := [2, 1, 4, 2, 3, 2, 1, 5]
def baseStart_173416 : Nat := 118140960795 + 173416 * 2 ^ 59
def prefixEnd_173416 : Nat := 4983230072969 + 3 ^ 40 * 173416 * 2
def baseEnd_173416 : Nat := 26383929238577405274809

theorem tailTrace_173416 : CollatzResearch.WordTrace tailWord_173416 prefixEnd_173416 26383929238577405274809 := by
  unfold tailWord_173416
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162500569875461969986051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4216667426500615959981401 3162500569875461969986051)
  ·
    refine ⟨4743750854813192954979077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3162500569875461969986051 4743750854813192954979077)
    ·
      refine ⟨889453285277473679058577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4743750854813192954979077 889453285277473679058577)
      ·
        refine ⟨667089963958105259293933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 889453285277473679058577 667089963958105259293933)
        ·
          refine ⟨250158736484289472235225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 667089963958105259293933 250158736484289472235225)
          ·
            refine ⟨187619052363217104176419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250158736484289472235225 187619052363217104176419)
            ·
              refine ⟨281428578544825656264629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187619052363217104176419 281428578544825656264629)
              ·
                refine ⟨26383929238577405274809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281428578544825656264629 26383929238577405274809)
                ·
                  rfl

theorem cell20_173416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_173416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173416 prefixEnd_173416 := by exact prefixLift 173416
  have htrace : WordTrace (prefixWord ++ tailWord_173416) baseStart_173416 baseEnd_173416 := by
    simpa [prefixWord, tailWord_173416, baseEnd_173416] using wordTrace_append hprefix tailTrace_173416
  have hstable : (prefixWord ++ tailWord_173416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173416).length < 2 ^ (prefixWord ++ tailWord_173416).sum := by decide
  have hdescent : baseEnd_173416 < baseStart_173416 := by decide
  rcases family_descends (prefixWord ++ tailWord_173416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173437 : List Nat := [1, 4, 1, 1, 2, 2, 5, 4]
def baseStart_173437 : Nat := 118140960795 + 173437 * 2 ^ 59
def prefixEnd_173437 : Nat := 4983230072969 + 3 ^ 40 * 173437 * 2
def baseEnd_173437 : Nat := 26387124229316492041447

theorem tailTrace_173437 : CollatzResearch.WordTrace tailWord_173437 prefixEnd_173437 26387124229316492041447 := by
  unfold tailWord_173437
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325767072674844526486565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4217178048449896350991043 6325767072674844526486565)
  ·
    refine ⟨1186081326126533348716231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6325767072674844526486565 1186081326126533348716231)
    ·
      refine ⟨1779121989189800023074347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1186081326126533348716231 1779121989189800023074347)
      ·
        refine ⟨2668682983784700034611521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1779121989189800023074347 2668682983784700034611521)
        ·
          refine ⟨2001512237838525025958641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2668682983784700034611521 2001512237838525025958641)
          ·
            refine ⟨1501134178378893769468981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2001512237838525025958641 1501134178378893769468981)
            ·
              refine ⟨140731329223021290887717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1501134178378893769468981 140731329223021290887717)
              ·
                refine ⟨26387124229316492041447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140731329223021290887717 26387124229316492041447)
                ·
                  rfl

theorem cell20_173437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 4].length) (baseStart_173437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173437 prefixEnd_173437 := by exact prefixLift 173437
  have htrace : WordTrace (prefixWord ++ tailWord_173437) baseStart_173437 baseEnd_173437 := by
    simpa [prefixWord, tailWord_173437, baseEnd_173437] using wordTrace_append hprefix tailTrace_173437
  have hstable : (prefixWord ++ tailWord_173437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173437).length < 2 ^ (prefixWord ++ tailWord_173437).sum := by decide
  have hdescent : baseEnd_173437 < baseStart_173437 := by decide
  rcases family_descends (prefixWord ++ tailWord_173437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173447 : List Nat := [1, 1, 4, 2, 2, 3, 2, 3, 2]
def baseStart_173447 : Nat := 118140960795 + 173447 * 2 ^ 59
def prefixEnd_173447 : Nat := 4983230072969 + 3 ^ 40 * 173447 * 2
def baseEnd_173447 : Nat := 79165936960433885790967

theorem tailTrace_173447 : CollatzResearch.WordTrace tailWord_173447 prefixEnd_173447 79165936960433885790967 := by
  unfold tailWord_173447
  simp only [CollatzResearch.WordTrace]
  refine ⟨6326131802638616234350595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4217421201759077489567063 6326131802638616234350595)
  ·
    refine ⟨9489197703957924351525893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6326131802638616234350595 9489197703957924351525893)
    ·
      refine ⟨1779224569492110815911105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9489197703957924351525893 1779224569492110815911105)
      ·
        refine ⟨1334418427119083111933329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1779224569492110815911105 1334418427119083111933329)
        ·
          refine ⟨1000813820339312333949997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1334418427119083111933329 1000813820339312333949997)
          ·
            refine ⟨375305182627242125231249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1000813820339312333949997 375305182627242125231249)
            ·
              refine ⟨281478886970431593923437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375305182627242125231249 281478886970431593923437)
              ·
                refine ⟨105554582613911847721289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281478886970431593923437 105554582613911847721289)
                ·
                  refine ⟨79165936960433885790967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105554582613911847721289 79165936960433885790967)
                  ·
                    rfl

theorem cell20_173447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 2].length) (baseStart_173447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173447 prefixEnd_173447 := by exact prefixLift 173447
  have htrace : WordTrace (prefixWord ++ tailWord_173447) baseStart_173447 baseEnd_173447 := by
    simpa [prefixWord, tailWord_173447, baseEnd_173447] using wordTrace_append hprefix tailTrace_173447
  have hstable : (prefixWord ++ tailWord_173447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173447).length < 2 ^ (prefixWord ++ tailWord_173447).sum := by decide
  have hdescent : baseEnd_173447 < baseStart_173447 := by decide
  rcases family_descends (prefixWord ++ tailWord_173447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173489 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_173489 : Nat := 118140960795 + 173489 * 2 ^ 59
def prefixEnd_173489 : Nat := 4983230072969 + 3 ^ 40 * 173489 * 2
def baseEnd_173489 : Nat := 79185106904868406390795

theorem tailTrace_173489 : CollatzResearch.WordTrace tailWord_173489 prefixEnd_173489 79185106904868406390795 := by
  unfold tailWord_173489
  simp only [CollatzResearch.WordTrace]
  refine ⟨6327663668486457407379521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4218442445657638271586347 6327663668486457407379521)
  ·
    refine ⟨4745747751364843055534641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6327663668486457407379521 4745747751364843055534641)
    ·
      refine ⟨3559310813523632291650981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4745747751364843055534641 3559310813523632291650981)
      ·
        refine ⟨667370777535681054684559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3559310813523632291650981 667370777535681054684559)
        ·
          refine ⟨1001056166303521582026839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667370777535681054684559 1001056166303521582026839)
          ·
            refine ⟨1501584249455282373040259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001056166303521582026839 1501584249455282373040259)
            ·
              refine ⟨2252376374182923559560389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501584249455282373040259 2252376374182923559560389)
              ·
                refine ⟨422320570159298167417573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2252376374182923559560389 422320570159298167417573)
                ·
                  refine ⟨79185106904868406390795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422320570159298167417573 79185106904868406390795)
                  ·
                    rfl

theorem cell20_173489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_173489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173489 prefixEnd_173489 := by exact prefixLift 173489
  have htrace : WordTrace (prefixWord ++ tailWord_173489) baseStart_173489 baseEnd_173489 := by
    simpa [prefixWord, tailWord_173489, baseEnd_173489] using wordTrace_append hprefix tailTrace_173489
  have hstable : (prefixWord ++ tailWord_173489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173489).length < 2 ^ (prefixWord ++ tailWord_173489).sum := by decide
  have hdescent : baseEnd_173489 < baseStart_173489 := by decide
  rcases family_descends (prefixWord ++ tailWord_173489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173537 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 3]
def baseStart_173537 : Nat := 118140960795 + 173537 * 2 ^ 59
def prefixEnd_173537 : Nat := 4983230072969 + 3 ^ 40 * 173537 * 2
def baseEnd_173537 : Nat := 79207015412793572790599

theorem tailTrace_173537 : CollatzResearch.WordTrace tailWord_173537 prefixEnd_173537 79207015412793572790599 := by
  unfold tailWord_173537
  simp only [CollatzResearch.WordTrace]
  refine ⟨6329414372312561605126865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4219609581541707736751243 6329414372312561605126865)
  ·
    refine ⟨4747060779234421203845149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6329414372312561605126865 4747060779234421203845149)
    ·
      refine ⟨1780147792212907951441931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4747060779234421203845149 1780147792212907951441931)
      ·
        refine ⟨2670221688319361927162897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780147792212907951441931 2670221688319361927162897)
        ·
          refine ⟨2002666266239521445372173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2670221688319361927162897 2002666266239521445372173)
          ·
            refine ⟨750999849839820542014565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2002666266239521445372173 750999849839820542014565)
            ·
              refine ⟨140812471844966351627731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 750999849839820542014565 140812471844966351627731)
              ·
                refine ⟨211218707767449527441597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140812471844966351627731 211218707767449527441597)
                ·
                  refine ⟨79207015412793572790599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211218707767449527441597 79207015412793572790599)
                  ·
                    rfl

theorem cell20_173537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_173537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173537 prefixEnd_173537 := by exact prefixLift 173537
  have htrace : WordTrace (prefixWord ++ tailWord_173537) baseStart_173537 baseEnd_173537 := by
    simpa [prefixWord, tailWord_173537, baseEnd_173537] using wordTrace_append hprefix tailTrace_173537
  have hstable : (prefixWord ++ tailWord_173537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173537).length < 2 ^ (prefixWord ++ tailWord_173537).sum := by decide
  have hdescent : baseEnd_173537 < baseStart_173537 := by decide
  rcases family_descends (prefixWord ++ tailWord_173537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173572 : List Nat := [2, 3, 2, 3, 10]
def baseStart_173572 : Nat := 118140960795 + 173572 * 2 ^ 59
def prefixEnd_173572 : Nat := 4983230072969 + 3 ^ 40 * 173572 * 2
def baseEnd_173572 : Nat := 978061609462827242269

theorem tailTrace_173572 : CollatzResearch.WordTrace tailWord_173572 prefixEnd_173572 978061609462827242269 := by
  unfold tailWord_173572
  simp only [CollatzResearch.WordTrace]
  refine ⟨3165345463592881291325485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4220460618123841721767313 3165345463592881291325485)
  ·
    refine ⟨1187004548847330484247057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3165345463592881291325485 1187004548847330484247057)
    ·
      refine ⟨890253411635497863185293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1187004548847330484247057 890253411635497863185293)
      ·
        refine ⟨333845029363311698694485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 890253411635497863185293 333845029363311698694485)
        ·
          refine ⟨978061609462827242269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 333845029363311698694485 978061609462827242269)
          ·
            rfl

theorem cell20_173572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 10].length) (baseStart_173572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173572 prefixEnd_173572 := by exact prefixLift 173572
  have htrace : WordTrace (prefixWord ++ tailWord_173572) baseStart_173572 baseEnd_173572 := by
    simpa [prefixWord, tailWord_173572, baseEnd_173572] using wordTrace_append hprefix tailTrace_173572
  have hstable : (prefixWord ++ tailWord_173572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173572).length < 2 ^ (prefixWord ++ tailWord_173572).sum := by decide
  have hdescent : baseEnd_173572 < baseStart_173572 := by decide
  rcases family_descends (prefixWord ++ tailWord_173572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173574 : List Nat := [6, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_173574 : Nat := 118140960795 + 173574 * 2 ^ 59
def prefixEnd_173574 : Nat := 4983230072969 + 3 ^ 40 * 173574 * 2
def baseEnd_173574 : Nat := 79223903220985888557115

theorem tailTrace_173574 : CollatzResearch.WordTrace tailWord_173574 prefixEnd_173574 79223903220985888557115 := by
  unfold tailWord_173574
  simp only [CollatzResearch.WordTrace]
  refine ⟨197836371036828653881993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4220509248785677949482517 197836371036828653881993)
  ·
    refine ⟨148377278277621490411495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197836371036828653881993 148377278277621490411495)
    ·
      refine ⟨222565917416432235617243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148377278277621490411495 222565917416432235617243)
      ·
        refine ⟨333848876124648353425865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222565917416432235617243 333848876124648353425865)
        ·
          refine ⟨250386657093486265069399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333848876124648353425865 250386657093486265069399)
          ·
            refine ⟨375579985640229397604099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250386657093486265069399 375579985640229397604099)
            ·
              refine ⟨563369978460344096406149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375579985640229397604099 563369978460344096406149)
              ·
                refine ⟨105631870961314518076153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 563369978460344096406149 105631870961314518076153)
                ·
                  refine ⟨79223903220985888557115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105631870961314518076153 79223903220985888557115)
                  ·
                    rfl

theorem cell20_173574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_173574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173574 prefixEnd_173574 := by exact prefixLift 173574
  have htrace : WordTrace (prefixWord ++ tailWord_173574) baseStart_173574 baseEnd_173574 := by
    simpa [prefixWord, tailWord_173574, baseEnd_173574] using wordTrace_append hprefix tailTrace_173574
  have hstable : (prefixWord ++ tailWord_173574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173574).length < 2 ^ (prefixWord ++ tailWord_173574).sum := by decide
  have hdescent : baseEnd_173574 < baseStart_173574 := by decide
  rcases family_descends (prefixWord ++ tailWord_173574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173575 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 3]
def baseStart_173575 : Nat := 118140960795 + 173575 * 2 ^ 59
def prefixEnd_173575 : Nat := 4983230072969 + 3 ^ 40 * 173575 * 2
def baseEnd_173575 : Nat := 79224359648234329523777

theorem tailTrace_173575 : CollatzResearch.WordTrace tailWord_173575 prefixEnd_173575 79224359648234329523777 := by
  unfold tailWord_173575
  simp only [CollatzResearch.WordTrace]
  refine ⟨6330800346174894095010179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4220533564116596063340119 6330800346174894095010179)
  ·
    refine ⟨9496200519262341142515269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6330800346174894095010179 9496200519262341142515269)
    ·
      refine ⟨1780537597361688964221613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9496200519262341142515269 1780537597361688964221613)
      ·
        refine ⟨667701599010633361583105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1780537597361688964221613 667701599010633361583105)
        ·
          refine ⟨500776199257975021187329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667701599010633361583105 500776199257975021187329)
          ·
            refine ⟨375582149443481265890497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 500776199257975021187329 375582149443481265890497)
            ·
              refine ⟨281686612082610949417873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375582149443481265890497 281686612082610949417873)
              ·
                refine ⟨211264959061958212063405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281686612082610949417873 211264959061958212063405)
                ·
                  refine ⟨79224359648234329523777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211264959061958212063405 79224359648234329523777)
                  ·
                    rfl

theorem cell20_173575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 3].length) (baseStart_173575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173575 prefixEnd_173575 := by exact prefixLift 173575
  have htrace : WordTrace (prefixWord ++ tailWord_173575) baseStart_173575 baseEnd_173575 := by
    simpa [prefixWord, tailWord_173575, baseEnd_173575] using wordTrace_append hprefix tailTrace_173575
  have hstable : (prefixWord ++ tailWord_173575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173575).length < 2 ^ (prefixWord ++ tailWord_173575).sum := by decide
  have hdescent : baseEnd_173575 < baseStart_173575 := by decide
  rcases family_descends (prefixWord ++ tailWord_173575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173578 : List Nat := [3, 1, 2, 2, 2, 4, 2, 2, 2]
def baseStart_173578 : Nat := 118140960795 + 173578 * 2 ^ 59
def prefixEnd_173578 : Nat := 4983230072969 + 3 ^ 40 * 173578 * 2
def baseEnd_173578 : Nat := 79225728929979652423765

theorem tailTrace_173578 : CollatzResearch.WordTrace tailWord_173578 prefixEnd_173578 79225728929979652423765 := by
  unfold tailWord_173578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582727441291006401842347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4220606510109350404912925 1582727441291006401842347)
  ·
    refine ⟨2374091161936509602763521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582727441291006401842347 2374091161936509602763521)
    ·
      refine ⟨1780568371452382202072641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2374091161936509602763521 1780568371452382202072641)
      ·
        refine ⟨1335426278589286651554481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1780568371452382202072641 1335426278589286651554481)
        ·
          refine ⟨1001569708941964988665861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1335426278589286651554481 1001569708941964988665861)
          ·
            refine ⟨187794320426618435374849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1001569708941964988665861 187794320426618435374849)
            ·
              refine ⟨140845740319963826531137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187794320426618435374849 140845740319963826531137)
              ·
                refine ⟨105634305239972869898353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140845740319963826531137 105634305239972869898353)
                ·
                  refine ⟨79225728929979652423765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105634305239972869898353 79225728929979652423765)
                  ·
                    rfl

theorem cell20_173578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_173578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173578 prefixEnd_173578 := by exact prefixLift 173578
  have htrace : WordTrace (prefixWord ++ tailWord_173578) baseStart_173578 baseEnd_173578 := by
    simpa [prefixWord, tailWord_173578, baseEnd_173578] using wordTrace_append hprefix tailTrace_173578
  have hstable : (prefixWord ++ tailWord_173578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173578).length < 2 ^ (prefixWord ++ tailWord_173578).sum := by decide
  have hdescent : baseEnd_173578 < baseStart_173578 := by decide
  rcases family_descends (prefixWord ++ tailWord_173578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173589 : List Nat := [1, 3, 2, 1, 3, 4, 1, 5]
def baseStart_173589 : Nat := 118140960795 + 173589 * 2 ^ 59
def prefixEnd_173589 : Nat := 4983230072969 + 3 ^ 40 * 173589 * 2
def baseEnd_173589 : Nat := 26410249876570834352351

theorem tailTrace_173589 : CollatzResearch.WordTrace tailWord_173589 prefixEnd_173589 26410249876570834352351 := by
  unfold tailWord_173589
  simp only [CollatzResearch.WordTrace]
  refine ⟨6331310968124174486019821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4220873978749449657346547 6331310968124174486019821)
  ·
    refine ⟨2374241613046565432257433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6331310968124174486019821 2374241613046565432257433)
    ·
      refine ⟨1780681209784924074193075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2374241613046565432257433 1780681209784924074193075)
      ·
        refine ⟨2671021814677386111289613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780681209784924074193075 2671021814677386111289613)
        ·
          refine ⟨1001633180504019791733605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2671021814677386111289613 1001633180504019791733605)
          ·
            refine ⟨187806221344503710950051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1001633180504019791733605 187806221344503710950051)
            ·
              refine ⟨281709332016755566425077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187806221344503710950051 281709332016755566425077)
              ·
                refine ⟨26410249876570834352351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281709332016755566425077 26410249876570834352351)
                ·
                  rfl

theorem cell20_173589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 5].length) (baseStart_173589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173589 prefixEnd_173589 := by exact prefixLift 173589
  have htrace : WordTrace (prefixWord ++ tailWord_173589) baseStart_173589 baseEnd_173589 := by
    simpa [prefixWord, tailWord_173589, baseEnd_173589] using wordTrace_append hprefix tailTrace_173589
  have hstable : (prefixWord ++ tailWord_173589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173589).length < 2 ^ (prefixWord ++ tailWord_173589).sum := by decide
  have hdescent : baseEnd_173589 < baseStart_173589 := by decide
  rcases family_descends (prefixWord ++ tailWord_173589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173596 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 3]
def baseStart_173596 : Nat := 118140960795 + 173596 * 2 ^ 59
def prefixEnd_173596 : Nat := 4983230072969 + 3 ^ 40 * 173596 * 2
def baseEnd_173596 : Nat := 79233944620451589823691

theorem tailTrace_173596 : CollatzResearch.WordTrace tailWord_173596 prefixEnd_173596 79233944620451589823691 := by
  unfold tailWord_173596
  simp only [CollatzResearch.WordTrace]
  refine ⟨3165783139549407340762321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4221044186065876454349761 3165783139549407340762321)
  ·
    refine ⟨2374337354662055505571741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3165783139549407340762321 2374337354662055505571741)
    ·
      refine ⟨890376507998270814589403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2374337354662055505571741 890376507998270814589403)
      ·
        refine ⟨1335564761997406221884105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890376507998270814589403 1335564761997406221884105)
        ·
          refine ⟨1001673571498054666413079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1335564761997406221884105 1001673571498054666413079)
          ·
            refine ⟨1502510357247081999619619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001673571498054666413079 1502510357247081999619619)
            ·
              refine ⟨2253765535870622999429429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502510357247081999619619 2253765535870622999429429)
              ·
                refine ⟨211290518987870906196509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2253765535870622999429429 211290518987870906196509)
                ·
                  refine ⟨79233944620451589823691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211290518987870906196509 79233944620451589823691)
                  ·
                    rfl

theorem cell20_173596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_173596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173596 prefixEnd_173596 := by exact prefixLift 173596
  have htrace : WordTrace (prefixWord ++ tailWord_173596) baseStart_173596 baseEnd_173596 := by
    simpa [prefixWord, tailWord_173596, baseEnd_173596] using wordTrace_append hprefix tailTrace_173596
  have hstable : (prefixWord ++ tailWord_173596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173596).length < 2 ^ (prefixWord ++ tailWord_173596).sum := by decide
  have hdescent : baseEnd_173596 < baseStart_173596 := by decide
  rcases family_descends (prefixWord ++ tailWord_173596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173617 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_173617 : Nat := 118140960795 + 173617 * 2 ^ 59
def prefixEnd_173617 : Nat := 4983230072969 + 3 ^ 40 * 173617 * 2
def baseEnd_173617 : Nat := 79243529592668850123605

theorem tailTrace_173617 : CollatzResearch.WordTrace tailWord_173617 prefixEnd_173617 79243529592668850123605 := by
  unfold tailWord_173617
  simp only [CollatzResearch.WordTrace]
  refine ⟨6332332212022735268039105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4221554808015156845359403 6332332212022735268039105)
  ·
    refine ⟨4749249159017051451029329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6332332212022735268039105 4749249159017051451029329)
    ·
      refine ⟨3561936869262788588271997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4749249159017051451029329 3561936869262788588271997)
      ·
        refine ⟨1335726325973545720601999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3561936869262788588271997 1335726325973545720601999)
        ·
          refine ⟨2003589488960318580902999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335726325973545720601999 2003589488960318580902999)
          ·
            refine ⟨3005384233440477871354499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003589488960318580902999 3005384233440477871354499)
            ·
              refine ⟨4508076350160716807031749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005384233440477871354499 4508076350160716807031749)
              ·
                refine ⟨845264315655134401318453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4508076350160716807031749 845264315655134401318453)
                ·
                  refine ⟨79243529592668850123605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 845264315655134401318453 79243529592668850123605)
                  ·
                    rfl

theorem cell20_173617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_173617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173617 prefixEnd_173617 := by exact prefixLift 173617
  have htrace : WordTrace (prefixWord ++ tailWord_173617) baseStart_173617 baseEnd_173617 := by
    simpa [prefixWord, tailWord_173617, baseEnd_173617] using wordTrace_append hprefix tailTrace_173617
  have hstable : (prefixWord ++ tailWord_173617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173617).length < 2 ^ (prefixWord ++ tailWord_173617).sum := by decide
  have hdescent : baseEnd_173617 < baseStart_173617 := by decide
  rcases family_descends (prefixWord ++ tailWord_173617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173672 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_173672 : Nat := 118140960795 + 173672 * 2 ^ 59
def prefixEnd_173672 : Nat := 4983230072969 + 3 ^ 40 * 173672 * 2
def baseEnd_173672 : Nat := 79268633091333103290047

theorem tailTrace_173672 : CollatzResearch.WordTrace tailWord_173672 prefixEnd_173672 79268633091333103290047 := by
  unfold tailWord_173672
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167169113411739830645635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4222892151215653107527513 3167169113411739830645635)
  ·
    refine ⟨4750753670117609745968453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3167169113411739830645635 4750753670117609745968453)
    ·
      refine ⟨890766313147051827369085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4750753670117609745968453 890766313147051827369085)
      ·
        refine ⟨334037367430144435263407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 890766313147051827369085 334037367430144435263407)
        ·
          refine ⟨501056051145216652895111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334037367430144435263407 501056051145216652895111)
          ·
            refine ⟨751584076717824979342667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501056051145216652895111 751584076717824979342667)
            ·
              refine ⟨1127376115076737469014001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751584076717824979342667 1127376115076737469014001)
              ·
                refine ⟨845532086307553101760501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127376115076737469014001 845532086307553101760501)
                ·
                  refine ⟨79268633091333103290047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 845532086307553101760501 79268633091333103290047)
                  ·
                    rfl

theorem cell20_173672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_173672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173672 prefixEnd_173672 := by exact prefixLift 173672
  have htrace : WordTrace (prefixWord ++ tailWord_173672) baseStart_173672 baseEnd_173672 := by
    simpa [prefixWord, tailWord_173672, baseEnd_173672] using wordTrace_append hprefix tailTrace_173672
  have hstable : (prefixWord ++ tailWord_173672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173672).length < 2 ^ (prefixWord ++ tailWord_173672).sum := by decide
  have hdescent : baseEnd_173672 < baseStart_173672 := by decide
  rcases family_descends (prefixWord ++ tailWord_173672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173706 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_173706 : Nat := 118140960795 + 173706 * 2 ^ 59
def prefixEnd_173706 : Nat := 4983230072969 + 3 ^ 40 * 173706 * 2
def baseEnd_173706 : Nat := 79284151617780096156575

theorem tailTrace_173706 : CollatzResearch.WordTrace tailWord_173706 prefixEnd_173706 79284151617780096156575 := by
  unfold tailWord_173706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583894577175075867007243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4223718872466868978685981 1583894577175075867007243)
  ·
    refine ⟨2375841865762613800510865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1583894577175075867007243 2375841865762613800510865)
    ·
      refine ⟨1781881399321960350383149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2375841865762613800510865 1781881399321960350383149)
      ·
        refine ⟨668205524745735131393681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1781881399321960350383149 668205524745735131393681)
        ·
          refine ⟨501154143559301348545261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668205524745735131393681 501154143559301348545261)
          ·
            refine ⟨187932803834738005704473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 501154143559301348545261 187932803834738005704473)
            ·
              refine ⟨140949602876053504278355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187932803834738005704473 140949602876053504278355)
              ·
                refine ⟨211424404314080256417533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140949602876053504278355 211424404314080256417533)
                ·
                  refine ⟨79284151617780096156575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211424404314080256417533 79284151617780096156575)
                  ·
                    rfl

theorem cell20_173706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_173706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173706 prefixEnd_173706 := by exact prefixLift 173706
  have htrace : WordTrace (prefixWord ++ tailWord_173706) baseStart_173706 baseEnd_173706 := by
    simpa [prefixWord, tailWord_173706, baseEnd_173706] using wordTrace_append hprefix tailTrace_173706
  have hstable : (prefixWord ++ tailWord_173706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173706).length < 2 ^ (prefixWord ++ tailWord_173706).sum := by decide
  have hdescent : baseEnd_173706 < baseStart_173706 := by decide
  rcases family_descends (prefixWord ++ tailWord_173706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173745 : List Nat := [1, 2, 2, 15]
def baseStart_173745 : Nat := 118140960795 + 173745 * 2 ^ 59
def prefixEnd_173745 : Nat := 4983230072969 + 3 ^ 40 * 173745 * 2
def baseEnd_173745 : Nat := 326345482635676106405

theorem tailTrace_173745 : CollatzResearch.WordTrace tailWord_173745 prefixEnd_173745 326345482635676106405 := by
  unfold tailWord_173745
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337000755559013128698689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4224667170372675419132459 6337000755559013128698689)
  ·
    refine ⟨4752750566669259846524017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6337000755559013128698689 4752750566669259846524017)
    ·
      refine ⟨3564562925001944884893013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4752750566669259846524017 3564562925001944884893013)
      ·
        refine ⟨326345482635676106405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 3564562925001944884893013 326345482635676106405)
        ·
          rfl

theorem cell20_173745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 15].length) (baseStart_173745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173745 prefixEnd_173745 := by exact prefixLift 173745
  have htrace : WordTrace (prefixWord ++ tailWord_173745) baseStart_173745 baseEnd_173745 := by
    simpa [prefixWord, tailWord_173745, baseEnd_173745] using wordTrace_append hprefix tailTrace_173745
  have hstable : (prefixWord ++ tailWord_173745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173745).length < 2 ^ (prefixWord ++ tailWord_173745).sum := by decide
  have hdescent : baseEnd_173745 < baseStart_173745 := by decide
  rcases family_descends (prefixWord ++ tailWord_173745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173751 : List Nat := [1, 1, 3, 1, 5, 1, 4, 2, 2]
def baseStart_173751 : Nat := 118140960795 + 173751 * 2 ^ 59
def prefixEnd_173751 : Nat := 4983230072969 + 3 ^ 40 * 173751 * 2
def baseEnd_173751 : Nat := 79304690843959939656391

theorem tailTrace_173751 : CollatzResearch.WordTrace tailWord_173751 prefixEnd_173751 79304690843959939656391 := by
  unfold tailWord_173751
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337219593537276153417107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4224813062358184102278071 6337219593537276153417107)
  ·
    refine ⟨9505829390305914230125661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6337219593537276153417107 9505829390305914230125661)
    ·
      refine ⟨3564686021364717836297123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9505829390305914230125661 3564686021364717836297123)
      ·
        refine ⟨5347029032047076754445685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3564686021364717836297123 5347029032047076754445685)
        ·
          refine ⟨501283971754413445729283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5347029032047076754445685 501283971754413445729283)
          ·
            refine ⟨751925957631620168593925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501283971754413445729283 751925957631620168593925)
            ·
              refine ⟨140986117055928781611361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 751925957631620168593925 140986117055928781611361)
              ·
                refine ⟨105739587791946586208521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140986117055928781611361 105739587791946586208521)
                ·
                  refine ⟨79304690843959939656391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105739587791946586208521 79304690843959939656391)
                  ·
                    rfl

theorem cell20_173751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 2].length) (baseStart_173751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173751 prefixEnd_173751 := by exact prefixLift 173751
  have htrace : WordTrace (prefixWord ++ tailWord_173751) baseStart_173751 baseEnd_173751 := by
    simpa [prefixWord, tailWord_173751, baseEnd_173751] using wordTrace_append hprefix tailTrace_173751
  have hstable : (prefixWord ++ tailWord_173751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173751).length < 2 ^ (prefixWord ++ tailWord_173751).sum := by decide
  have hdescent : baseEnd_173751 < baseStart_173751 := by decide
  rcases family_descends (prefixWord ++ tailWord_173751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173772 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 4]
def baseStart_173772 : Nat := 118140960795 + 173772 * 2 ^ 59
def prefixEnd_173772 : Nat := 4983230072969 + 3 ^ 40 * 173772 * 2
def baseEnd_173772 : Nat := 79314275816177199956305

theorem tailTrace_173772 : CollatzResearch.WordTrace tailWord_173772 prefixEnd_173772 79314275816177199956305 := by
  unfold tailWord_173772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168992763230598369965785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4225323684307464493287713 3168992763230598369965785)
  ·
    refine ⟨2376744572422948777474339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3168992763230598369965785 2376744572422948777474339)
    ·
      refine ⟨3565116858634423166211509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2376744572422948777474339 3565116858634423166211509)
      ·
        refine ⟨334229705496977171832329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3565116858634423166211509 334229705496977171832329)
        ·
          refine ⟨250672279122732878874247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334229705496977171832329 250672279122732878874247)
          ·
            refine ⟨376008418684099318311371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250672279122732878874247 376008418684099318311371)
            ·
              refine ⟨564012628026148977467057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376008418684099318311371 564012628026148977467057)
              ·
                refine ⟨423009471019611733100293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 564012628026148977467057 423009471019611733100293)
                ·
                  refine ⟨79314275816177199956305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423009471019611733100293 79314275816177199956305)
                  ·
                    rfl

theorem cell20_173772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_173772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173772 prefixEnd_173772 := by exact prefixLift 173772
  have htrace : WordTrace (prefixWord ++ tailWord_173772) baseStart_173772 baseEnd_173772 := by
    simpa [prefixWord, tailWord_173772, baseEnd_173772] using wordTrace_append hprefix tailTrace_173772
  have hstable : (prefixWord ++ tailWord_173772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173772).length < 2 ^ (prefixWord ++ tailWord_173772).sum := by decide
  have hdescent : baseEnd_173772 < baseStart_173772 := by decide
  rcases family_descends (prefixWord ++ tailWord_173772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173799 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 3]
def baseStart_173799 : Nat := 118140960795 + 173799 * 2 ^ 59
def prefixEnd_173799 : Nat := 4983230072969 + 3 ^ 40 * 173799 * 2
def baseEnd_173799 : Nat := 79326599351885106056195

theorem tailTrace_173799 : CollatzResearch.WordTrace tailWord_173799 prefixEnd_173799 79326599351885106056195 := by
  unfold tailWord_173799
  simp only [CollatzResearch.WordTrace]
  refine ⟨6338970297363380351164451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4225980198242253567442967 6338970297363380351164451)
  ·
    refine ⟨9508455446045070526746677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6338970297363380351164451 9508455446045070526746677)
    ·
      refine ⟨891417698066725361882501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9508455446045070526746677 891417698066725361882501)
      ·
        refine ⟨167140818387511005352969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 891417698066725361882501 167140818387511005352969)
        ·
          refine ⟨125355613790633254014727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167140818387511005352969 125355613790633254014727)
          ·
            refine ⟨188033420685949881022091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125355613790633254014727 188033420685949881022091)
            ·
              refine ⟨282050131028924821533137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188033420685949881022091 282050131028924821533137)
              ·
                refine ⟨211537598271693616149853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282050131028924821533137 211537598271693616149853)
                ·
                  refine ⟨79326599351885106056195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211537598271693616149853 79326599351885106056195)
                  ·
                    rfl

theorem cell20_173799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 3].length) (baseStart_173799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173799 prefixEnd_173799 := by exact prefixLift 173799
  have htrace : WordTrace (prefixWord ++ tailWord_173799) baseStart_173799 baseEnd_173799 := by
    simpa [prefixWord, tailWord_173799, baseEnd_173799] using wordTrace_append hprefix tailTrace_173799
  have hstable : (prefixWord ++ tailWord_173799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173799).length < 2 ^ (prefixWord ++ tailWord_173799).sum := by decide
  have hdescent : baseEnd_173799 < baseStart_173799 := by decide
  rcases family_descends (prefixWord ++ tailWord_173799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173800 : List Nat := [2, 1, 4, 1, 3, 2, 7]
def baseStart_173800 : Nat := 118140960795 + 173800 * 2 ^ 59
def prefixEnd_173800 : Nat := 4983230072969 + 3 ^ 40 * 173800 * 2
def baseEnd_173800 : Nat := 8814117308792616335873

theorem tailTrace_173800 : CollatzResearch.WordTrace tailWord_173800 prefixEnd_173800 8814117308792616335873 := by
  unfold tailWord_173800
  simp only [CollatzResearch.WordTrace]
  refine ⟨3169503385179878760975427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4226004513573171681300569 3169503385179878760975427)
  ·
    refine ⟨4754255077769818141463141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3169503385179878760975427 4754255077769818141463141)
    ·
      refine ⟨891422827081840901524339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4754255077769818141463141 891422827081840901524339)
      ·
        refine ⟨1337134240622761352286509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891422827081840901524339 1337134240622761352286509)
        ·
          refine ⟨501425340233535507107441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1337134240622761352286509 501425340233535507107441)
          ·
            refine ⟨376069005175151630330581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501425340233535507107441 376069005175151630330581)
            ·
              refine ⟨8814117308792616335873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 376069005175151630330581 8814117308792616335873)
              ·
                rfl

theorem cell20_173800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 7].length) (baseStart_173800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173800 prefixEnd_173800 := by exact prefixLift 173800
  have htrace : WordTrace (prefixWord ++ tailWord_173800) baseStart_173800 baseEnd_173800 := by
    simpa [prefixWord, tailWord_173800, baseEnd_173800] using wordTrace_append hprefix tailTrace_173800
  have hstable : (prefixWord ++ tailWord_173800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173800).length < 2 ^ (prefixWord ++ tailWord_173800).sum := by decide
  have hdescent : baseEnd_173800 < baseStart_173800 := by decide
  rcases family_descends (prefixWord ++ tailWord_173800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173807 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_173807 : Nat := 118140960795 + 173807 * 2 ^ 59
def prefixEnd_173807 : Nat := 4983230072969 + 3 ^ 40 * 173807 * 2
def baseEnd_173807 : Nat := 79330250769872633789495

theorem tailTrace_173807 : CollatzResearch.WordTrace tailWord_173807 prefixEnd_173807 79330250769872633789495 := by
  unfold tailWord_173807
  simp only [CollatzResearch.WordTrace]
  refine ⟨6339262081334397717455675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4226174720889598478303783 6339262081334397717455675)
  ·
    refine ⟨9508893122001596576183513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6339262081334397717455675 9508893122001596576183513)
    ·
      refine ⟨7131669841501197432137635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9508893122001596576183513 7131669841501197432137635)
      ·
        refine ⟨10697504762251796148206453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7131669841501197432137635 10697504762251796148206453)
        ·
          refine ⟨1002891071461105888894355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10697504762251796148206453 1002891071461105888894355)
          ·
            refine ⟨1504336607191658833341533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002891071461105888894355 1504336607191658833341533)
            ·
              refine ⟨564126227696872062503075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1504336607191658833341533 564126227696872062503075)
              ·
                refine ⟨846189341545308093754613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564126227696872062503075 846189341545308093754613)
                ·
                  refine ⟨79330250769872633789495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 846189341545308093754613 79330250769872633789495)
                  ·
                    rfl

theorem cell20_173807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_173807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173807 prefixEnd_173807 := by exact prefixLift 173807
  have htrace : WordTrace (prefixWord ++ tailWord_173807) baseStart_173807 baseEnd_173807 := by
    simpa [prefixWord, tailWord_173807, baseEnd_173807] using wordTrace_append hprefix tailTrace_173807
  have hstable : (prefixWord ++ tailWord_173807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173807).length < 2 ^ (prefixWord ++ tailWord_173807).sum := by decide
  have hdescent : baseEnd_173807 < baseStart_173807 := by decide
  rcases family_descends (prefixWord ++ tailWord_173807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173810 : List Nat := [3, 2, 1, 3, 1, 1, 1, 6, 2]
def baseStart_173810 : Nat := 118140960795 + 173810 * 2 ^ 59
def prefixEnd_173810 : Nat := 4983230072969 + 3 ^ 40 * 173810 * 2
def baseEnd_173810 : Nat := 79331620051617956689483

theorem tailTrace_173810 : CollatzResearch.WordTrace tailWord_173810 prefixEnd_173810 79331620051617956689483 := by
  unfold tailWord_173810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1584842875080882307453721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4226247666882352819876589 1584842875080882307453721)
  ·
    refine ⟨1188632156310661730590291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1584842875080882307453721 1188632156310661730590291)
    ·
      refine ⟨1782948234465992595885437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1188632156310661730590291 1782948234465992595885437)
      ·
        refine ⟨668605587924747223457039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1782948234465992595885437 668605587924747223457039)
        ·
          refine ⟨1002908381887120835185559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668605587924747223457039 1002908381887120835185559)
          ·
            refine ⟨1504362572830681252778339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002908381887120835185559 1504362572830681252778339)
            ·
              refine ⟨2256543859246021879167509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504362572830681252778339 2256543859246021879167509)
              ·
                refine ⟨105775493402157275585977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2256543859246021879167509 105775493402157275585977)
                ·
                  refine ⟨79331620051617956689483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105775493402157275585977 79331620051617956689483)
                  ·
                    rfl

theorem cell20_173810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_173810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173810 prefixEnd_173810 := by exact prefixLift 173810
  have htrace : WordTrace (prefixWord ++ tailWord_173810) baseStart_173810 baseEnd_173810 := by
    simpa [prefixWord, tailWord_173810, baseEnd_173810] using wordTrace_append hprefix tailTrace_173810
  have hstable : (prefixWord ++ tailWord_173810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173810).length < 2 ^ (prefixWord ++ tailWord_173810).sum := by decide
  have hdescent : baseEnd_173810 < baseStart_173810 := by decide
  rcases family_descends (prefixWord ++ tailWord_173810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173845 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_173845 : Nat := 118140960795 + 173845 * 2 ^ 59
def prefixEnd_173845 : Nat := 4983230072969 + 3 ^ 40 * 173845 * 2
def baseEnd_173845 : Nat := 79347595005313390522673

theorem tailTrace_173845 : CollatzResearch.WordTrace tailWord_173845 prefixEnd_173845 79347595005313390522673 := by
  unfold tailWord_173845
  simp only [CollatzResearch.WordTrace]
  refine ⟨6340648055196730207338989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4227098703464486804892659 6340648055196730207338989)
  ·
    refine ⟨2377743020698773827752121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6340648055196730207338989 2377743020698773827752121)
    ·
      refine ⟨1783307265524080370814091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2377743020698773827752121 1783307265524080370814091)
      ·
        refine ⟨2674960898286120556221137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1783307265524080370814091 2674960898286120556221137)
        ·
          refine ⟨2006220673714590417165853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2674960898286120556221137 2006220673714590417165853)
          ·
            refine ⟨752332752642971406437195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2006220673714590417165853 752332752642971406437195)
            ·
              refine ⟨1128499128964457109655793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752332752642971406437195 1128499128964457109655793)
              ·
                refine ⟨846374346723342832241845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128499128964457109655793 846374346723342832241845)
                ·
                  refine ⟨79347595005313390522673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 846374346723342832241845 79347595005313390522673)
                  ·
                    rfl

theorem cell20_173845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_173845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173845 prefixEnd_173845 := by exact prefixLift 173845
  have htrace : WordTrace (prefixWord ++ tailWord_173845) baseStart_173845 baseEnd_173845 := by
    simpa [prefixWord, tailWord_173845, baseEnd_173845] using wordTrace_append hprefix tailTrace_173845
  have hstable : (prefixWord ++ tailWord_173845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173845).length < 2 ^ (prefixWord ++ tailWord_173845).sum := by decide
  have hdescent : baseEnd_173845 < baseStart_173845 := by decide
  rcases family_descends (prefixWord ++ tailWord_173845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173848 : List Nat := [2, 1, 2, 3, 1, 1, 5, 3, 2]
def baseStart_173848 : Nat := 118140960795 + 173848 * 2 ^ 59
def prefixEnd_173848 : Nat := 4983230072969 + 3 ^ 40 * 173848 * 2
def baseEnd_173848 : Nat := 79348964287058713422661

theorem tailTrace_173848 : CollatzResearch.WordTrace tailWord_173848 prefixEnd_173848 79348964287058713422661 := by
  unfold tailWord_173848
  simp only [CollatzResearch.WordTrace]
  refine ⟨3170378737092930859849099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4227171649457241146465465 3170378737092930859849099)
  ·
    refine ⟨4755568105639396289773649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3170378737092930859849099 4755568105639396289773649)
    ·
      refine ⟨3566676079229547217330237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4755568105639396289773649 3566676079229547217330237)
      ·
        refine ⟨1337503529711080206498839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3566676079229547217330237 1337503529711080206498839)
        ·
          refine ⟨2006255294566620309748259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337503529711080206498839 2006255294566620309748259)
          ·
            refine ⟨3009382941849930464622389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006255294566620309748259 3009382941849930464622389)
            ·
              refine ⟨282129650798430981058349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3009382941849930464622389 282129650798430981058349)
              ·
                refine ⟨105798619049411617896881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282129650798430981058349 105798619049411617896881)
                ·
                  refine ⟨79348964287058713422661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105798619049411617896881 79348964287058713422661)
                  ·
                    rfl

theorem cell20_173848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_173848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173848 prefixEnd_173848 := by exact prefixLift 173848
  have htrace : WordTrace (prefixWord ++ tailWord_173848) baseStart_173848 baseEnd_173848 := by
    simpa [prefixWord, tailWord_173848, baseEnd_173848] using wordTrace_append hprefix tailTrace_173848
  have hstable : (prefixWord ++ tailWord_173848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173848).length < 2 ^ (prefixWord ++ tailWord_173848).sum := by decide
  have hdescent : baseEnd_173848 < baseStart_173848 := by decide
  rcases family_descends (prefixWord ++ tailWord_173848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173859 : List Nat := [1, 1, 1, 4, 2, 1, 10]
def baseStart_173859 : Nat := 118140960795 + 173859 * 2 ^ 59
def prefixEnd_173859 : Nat := 4983230072969 + 3 ^ 40 * 173859 * 2
def baseEnd_173859 : Nat := 8817109442976840450661

theorem tailTrace_173859 : CollatzResearch.WordTrace tailWord_173859 prefixEnd_173859 8817109442976840450661 := by
  unfold tailWord_173859
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341158677146010598348631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4227439118097340398899087 6341158677146010598348631)
  ·
    refine ⟨9511738015719015897522947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6341158677146010598348631 9511738015719015897522947)
    ·
      refine ⟨14267607023578523846284421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9511738015719015897522947 14267607023578523846284421)
      ·
        refine ⟨2675176316920973221178329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14267607023578523846284421 2675176316920973221178329)
        ·
          refine ⟨2006382237690729915883747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2675176316920973221178329 2006382237690729915883747)
          ·
            refine ⟨3009573356536094873825621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006382237690729915883747 3009573356536094873825621)
            ·
              refine ⟨8817109442976840450661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3009573356536094873825621 8817109442976840450661)
              ·
                rfl

theorem cell20_173859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 10].length) (baseStart_173859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173859 prefixEnd_173859 := by exact prefixLift 173859
  have htrace : WordTrace (prefixWord ++ tailWord_173859) baseStart_173859 baseEnd_173859 := by
    simpa [prefixWord, tailWord_173859, baseEnd_173859] using wordTrace_append hprefix tailTrace_173859
  have hstable : (prefixWord ++ tailWord_173859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173859).length < 2 ^ (prefixWord ++ tailWord_173859).sum := by decide
  have hdescent : baseEnd_173859 < baseStart_173859 := by decide
  rcases family_descends (prefixWord ++ tailWord_173859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173897 : List Nat := [1, 2, 1, 1, 2, 4, 1, 8]
def baseStart_173897 : Nat := 118140960795 + 173897 * 2 ^ 59
def prefixEnd_173897 : Nat := 4983230072969 + 3 ^ 40 * 173897 * 2
def baseEnd_173897 : Nat := 26457109740744106929709

theorem tailTrace_173897 : CollatzResearch.WordTrace tailWord_173897 prefixEnd_173897 26457109740744106929709 := by
  unfold tailWord_173897
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342544651008343088231945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4228363100672228725487963 6342544651008343088231945)
  ·
    refine ⟨4756908488256257316173959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6342544651008343088231945 4756908488256257316173959)
    ·
      refine ⟨7135362732384385974260939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4756908488256257316173959 7135362732384385974260939)
      ·
        refine ⟨10703044098576578961391409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7135362732384385974260939 10703044098576578961391409)
        ·
          refine ⟨8027283073932434221043557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10703044098576578961391409 8027283073932434221043557)
          ·
            refine ⟨1505115576362331416445667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8027283073932434221043557 1505115576362331416445667)
            ·
              refine ⟨2257673364543497124668501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505115576362331416445667 2257673364543497124668501)
              ·
                refine ⟨26457109740744106929709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2257673364543497124668501 26457109740744106929709)
                ·
                  rfl

theorem cell20_173897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_173897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173897 prefixEnd_173897 := by exact prefixLift 173897
  have htrace : WordTrace (prefixWord ++ tailWord_173897) baseStart_173897 baseEnd_173897 := by
    simpa [prefixWord, tailWord_173897, baseEnd_173897] using wordTrace_append hprefix tailTrace_173897
  have hstable : (prefixWord ++ tailWord_173897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173897).length < 2 ^ (prefixWord ++ tailWord_173897).sum := by decide
  have hdescent : baseEnd_173897 < baseStart_173897 := by decide
  rcases family_descends (prefixWord ++ tailWord_173897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173952 : List Nat := [2, 1, 1, 2, 1, 2, 7, 4]
def baseStart_173952 : Nat := 118140960795 + 173952 * 2 ^ 59
def prefixEnd_173952 : Nat := 4983230072969 + 3 ^ 40 * 173952 * 2
def baseEnd_173952 : Nat := 26465477573632191318523

theorem tailTrace_173952 : CollatzResearch.WordTrace tailWord_173952 prefixEnd_173952 26465477573632191318523 := by
  unfold tailWord_173952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3172275332904543740742055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4229700443872724987656073 3172275332904543740742055)
  ·
    refine ⟨4758412999356815611113083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3172275332904543740742055 4758412999356815611113083)
    ·
      refine ⟨7137619499035223416669625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4758412999356815611113083 7137619499035223416669625)
      ·
        refine ⟨5353214624276417562502219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7137619499035223416669625 5353214624276417562502219)
        ·
          refine ⟨8029821936414626343753329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5353214624276417562502219 8029821936414626343753329)
          ·
            refine ⟨6022366452310969757814997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8029821936414626343753329 6022366452310969757814997)
            ·
              refine ⟨141149213726038353698789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6022366452310969757814997 141149213726038353698789)
              ·
                refine ⟨26465477573632191318523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141149213726038353698789 26465477573632191318523)
                ·
                  rfl

theorem cell20_173952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_173952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173952 prefixEnd_173952 := by exact prefixLift 173952
  have htrace : WordTrace (prefixWord ++ tailWord_173952) baseStart_173952 baseEnd_173952 := by
    simpa [prefixWord, tailWord_173952, baseEnd_173952] using wordTrace_append hprefix tailTrace_173952
  have hstable : (prefixWord ++ tailWord_173952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173952).length < 2 ^ (prefixWord ++ tailWord_173952).sum := by decide
  have hdescent : baseEnd_173952 < baseStart_173952 := by decide
  rcases family_descends (prefixWord ++ tailWord_173952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173973 : List Nat := [1, 3, 2, 1, 1, 3, 9]
def baseStart_173973 : Nat := 118140960795 + 173973 * 2 ^ 59
def prefixEnd_173973 : Nat := 4983230072969 + 3 ^ 40 * 173973 * 2
def baseEnd_173973 : Nat := 8822890854790426028387

theorem tailTrace_173973 : CollatzResearch.WordTrace tailWord_173973 prefixEnd_173973 8822890854790426028387 := by
  unfold tailWord_173973
  simp only [CollatzResearch.WordTrace]
  refine ⟨6345316598733008067998573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4230211065822005378665715 6345316598733008067998573)
  ·
    refine ⟨2379493724524878025499465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6345316598733008067998573 2379493724524878025499465)
    ·
      refine ⟨1784620293393658519124599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2379493724524878025499465 1784620293393658519124599)
      ·
        refine ⟨2676930440090487778686899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784620293393658519124599 2676930440090487778686899)
        ·
          refine ⟨4015395660135731668030349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676930440090487778686899 4015395660135731668030349)
          ·
            refine ⟨1505773372550899375511381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4015395660135731668030349 1505773372550899375511381)
            ·
              refine ⟨8822890854790426028387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1505773372550899375511381 8822890854790426028387)
              ·
                rfl

theorem cell20_173973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 9].length) (baseStart_173973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_173973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_173973 prefixEnd_173973 := by exact prefixLift 173973
  have htrace : WordTrace (prefixWord ++ tailWord_173973) baseStart_173973 baseEnd_173973 := by
    simpa [prefixWord, tailWord_173973, baseEnd_173973] using wordTrace_append hprefix tailTrace_173973
  have hstable : (prefixWord ++ tailWord_173973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173973).length < 2 ^ (prefixWord ++ tailWord_173973).sum := by decide
  have hdescent : baseEnd_173973 < baseStart_173973 := by decide
  rcases family_descends (prefixWord ++ tailWord_173973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174021 : List Nat := [1, 3, 1, 1, 1, 1, 1, 9, 2]
def baseStart_174021 : Nat := 118140960795 + 174021 * 2 ^ 59
def prefixEnd_174021 : Nat := 4983230072969 + 3 ^ 40 * 174021 * 2
def baseEnd_174021 : Nat := 79427926201039000655287

theorem tailTrace_174021 : CollatzResearch.WordTrace tailWord_174021 prefixEnd_174021 79427926201039000655287 := by
  unfold tailWord_174021
  simp only [CollatzResearch.WordTrace]
  refine ⟨6347067302559112265745917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4231378201706074843830611 6347067302559112265745917)
  ·
    refine ⟨2380150238459667099654719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6347067302559112265745917 2380150238459667099654719)
    ·
      refine ⟨3570225357689500649482079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2380150238459667099654719 3570225357689500649482079)
      ·
        refine ⟨5355338036534250974223119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3570225357689500649482079 5355338036534250974223119)
        ·
          refine ⟨8033007054801376461334679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5355338036534250974223119 8033007054801376461334679)
          ·
            refine ⟨12049510582202064692002019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8033007054801376461334679 12049510582202064692002019)
            ·
              refine ⟨18074265873303097038003029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12049510582202064692002019 18074265873303097038003029)
              ·
                refine ⟨105903901601385334207049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18074265873303097038003029 105903901601385334207049)
                ·
                  refine ⟨79427926201039000655287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105903901601385334207049 79427926201039000655287)
                  ·
                    rfl

theorem cell20_174021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_174021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174021 prefixEnd_174021 := by exact prefixLift 174021
  have htrace : WordTrace (prefixWord ++ tailWord_174021) baseStart_174021 baseEnd_174021 := by
    simpa [prefixWord, tailWord_174021, baseEnd_174021] using wordTrace_append hprefix tailTrace_174021
  have hstable : (prefixWord ++ tailWord_174021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174021).length < 2 ^ (prefixWord ++ tailWord_174021).sum := by decide
  have hdescent : baseEnd_174021 < baseStart_174021 := by decide
  rcases family_descends (prefixWord ++ tailWord_174021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174028 : List Nat := [2, 2, 1, 4, 1, 4, 6]
def baseStart_174028 : Nat := 118140960795 + 174028 * 2 ^ 59
def prefixEnd_174028 : Nat := 4983230072969 + 3 ^ 40 * 174028 * 2
def baseEnd_174028 : Nat := 8825680132419787491325

theorem tailTrace_174028 : CollatzResearch.WordTrace tailWord_174028 prefixEnd_174028 8825680132419787491325 := by
  unfold tailWord_174028
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173661306766876230625369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4231548409022501640833825 3173661306766876230625369)
  ·
    refine ⟨2380245980075157172969027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3173661306766876230625369 2380245980075157172969027)
    ·
      refine ⟨3570368970112735759453541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2380245980075157172969027 3570368970112735759453541)
      ·
        refine ⟨669444181896137954897539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3570368970112735759453541 669444181896137954897539)
        ·
          refine ⟨1004166272844206932346309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669444181896137954897539 1004166272844206932346309)
          ·
            refine ⟨188281176158288799814933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1004166272844206932346309 188281176158288799814933)
            ·
              refine ⟨8825680132419787491325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 188281176158288799814933 8825680132419787491325)
              ·
                rfl

theorem cell20_174028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 6].length) (baseStart_174028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174028 prefixEnd_174028 := by exact prefixLift 174028
  have htrace : WordTrace (prefixWord ++ tailWord_174028) baseStart_174028 baseEnd_174028 := by
    simpa [prefixWord, tailWord_174028, baseEnd_174028] using wordTrace_append hprefix tailTrace_174028
  have hstable : (prefixWord ++ tailWord_174028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174028).length < 2 ^ (prefixWord ++ tailWord_174028).sum := by decide
  have hdescent : baseEnd_174028 < baseStart_174028 := by decide
  rcases family_descends (prefixWord ++ tailWord_174028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174034 : List Nat := [3, 2, 2, 3, 2, 1, 3, 2, 2]
def baseStart_174034 : Nat := 118140960795 + 174034 * 2 ^ 59
def prefixEnd_174034 : Nat := 4983230072969 + 3 ^ 40 * 174034 * 2
def baseEnd_174034 : Nat := 79433859755268733221901

theorem tailTrace_174034 : CollatzResearch.WordTrace tailWord_174034 prefixEnd_174034 79433859755268733221901 := by
  unfold tailWord_174034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586885362878003871492289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4231694301008010323979437 1586885362878003871492289)
  ·
    refine ⟨1190164022158502903619217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1586885362878003871492289 1190164022158502903619217)
    ·
      refine ⟨892623016618877177714413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1190164022158502903619217 892623016618877177714413)
      ·
        refine ⟨334733631232078941642905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 892623016618877177714413 334733631232078941642905)
        ·
          refine ⟨251050223424059206232179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334733631232078941642905 251050223424059206232179)
          ·
            refine ⟨376575335136088809348269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251050223424059206232179 376575335136088809348269)
            ·
              refine ⟨141215750676033303505601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376575335136088809348269 141215750676033303505601)
              ·
                refine ⟨105911813007024977629201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141215750676033303505601 105911813007024977629201)
                ·
                  refine ⟨79433859755268733221901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105911813007024977629201 79433859755268733221901)
                  ·
                    rfl

theorem cell20_174034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_174034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174034 prefixEnd_174034 := by exact prefixLift 174034
  have htrace : WordTrace (prefixWord ++ tailWord_174034) baseStart_174034 baseEnd_174034 := by
    simpa [prefixWord, tailWord_174034, baseEnd_174034] using wordTrace_append hprefix tailTrace_174034
  have hstable : (prefixWord ++ tailWord_174034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174034).length < 2 ^ (prefixWord ++ tailWord_174034).sum := by decide
  have hdescent : baseEnd_174034 < baseStart_174034 := by decide
  rcases family_descends (prefixWord ++ tailWord_174034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174044 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 3]
def baseStart_174044 : Nat := 118140960795 + 174044 * 2 ^ 59
def prefixEnd_174044 : Nat := 4983230072969 + 3 ^ 40 * 174044 * 2
def baseEnd_174044 : Nat := 79438424027753142888527

theorem tailTrace_174044 : CollatzResearch.WordTrace tailWord_174044 prefixEnd_174044 79438424027753142888527 := by
  unfold tailWord_174044
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173953090737893596916593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4231937454317191462555457 3173953090737893596916593)
  ·
    refine ⟨2380464818053420197687445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3173953090737893596916593 2380464818053420197687445)
    ·
      refine ⟨111584288346254071766599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2380464818053420197687445 111584288346254071766599)
      ·
        refine ⟨167376432519381107649899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111584288346254071766599 167376432519381107649899)
        ·
          refine ⟨251064648779071661474849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167376432519381107649899 251064648779071661474849)
          ·
            refine ⟨188298486584303746106137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251064648779071661474849 188298486584303746106137)
            ·
              refine ⟨141223864938227809579603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188298486584303746106137 141223864938227809579603)
              ·
                refine ⟨211835797407341714369405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141223864938227809579603 211835797407341714369405)
                ·
                  refine ⟨79438424027753142888527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211835797407341714369405 79438424027753142888527)
                  ·
                    rfl

theorem cell20_174044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_174044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174044 prefixEnd_174044 := by exact prefixLift 174044
  have htrace : WordTrace (prefixWord ++ tailWord_174044) baseStart_174044 baseEnd_174044 := by
    simpa [prefixWord, tailWord_174044, baseEnd_174044] using wordTrace_append hprefix tailTrace_174044
  have hstable : (prefixWord ++ tailWord_174044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174044).length < 2 ^ (prefixWord ++ tailWord_174044).sum := by decide
  have hdescent : baseEnd_174044 < baseStart_174044 := by decide
  rcases family_descends (prefixWord ++ tailWord_174044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174045 : List Nat := [1, 4, 3, 1, 3, 1, 2, 5]
def baseStart_174045 : Nat := 118140960795 + 174045 * 2 ^ 59
def prefixEnd_174045 : Nat := 4983230072969 + 3 ^ 40 * 174045 * 2
def baseEnd_174045 : Nat := 26479626818333861285063

theorem tailTrace_174045 : CollatzResearch.WordTrace tailWord_174045 prefixEnd_174045 26479626818333861285063 := by
  unfold tailWord_174045
  simp only [CollatzResearch.WordTrace]
  refine ⟨6347942654472164364619589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4231961769648109576413059 6347942654472164364619589)
  ·
    refine ⟨1190239247713530818366173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6347942654472164364619589 1190239247713530818366173)
    ·
      refine ⟨446339717892574056887315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1190239247713530818366173 446339717892574056887315)
      ·
        refine ⟨669509576838861085330973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446339717892574056887315 669509576838861085330973)
        ·
          refine ⟨251066091314572906999115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 669509576838861085330973 251066091314572906999115)
          ·
            refine ⟨376599136971859360498673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251066091314572906999115 376599136971859360498673)
            ·
              refine ⟨282449352728894520374005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376599136971859360498673 282449352728894520374005)
              ·
                refine ⟨26479626818333861285063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282449352728894520374005 26479626818333861285063)
                ·
                  rfl

theorem cell20_174045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 5].length) (baseStart_174045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174045 prefixEnd_174045 := by exact prefixLift 174045
  have htrace : WordTrace (prefixWord ++ tailWord_174045) baseStart_174045 baseEnd_174045 := by
    simpa [prefixWord, tailWord_174045, baseEnd_174045] using wordTrace_append hprefix tailTrace_174045
  have hstable : (prefixWord ++ tailWord_174045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174045).length < 2 ^ (prefixWord ++ tailWord_174045).sum := by decide
  have hdescent : baseEnd_174045 < baseStart_174045 := by decide
  rcases family_descends (prefixWord ++ tailWord_174045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174049 : List Nat := [1, 2, 3, 1, 2, 1, 3, 7]
def baseStart_174049 : Nat := 118140960795 + 174049 * 2 ^ 59
def prefixEnd_174049 : Nat := 4983230072969 + 3 ^ 40 * 174049 * 2
def baseEnd_174049 : Nat := 26480235387998449240613

theorem tailTrace_174049 : CollatzResearch.WordTrace tailWord_174049 prefixEnd_174049 26480235387998449240613 := by
  unfold tailWord_174049
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348088546457673047765201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4232059030971782031843467 6348088546457673047765201)
  ·
    refine ⟨4761066409843254785823901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6348088546457673047765201 4761066409843254785823901)
    ·
      refine ⟨1785399903691220544683963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4761066409843254785823901 1785399903691220544683963)
      ·
        refine ⟨2678099855536830817025945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785399903691220544683963 2678099855536830817025945)
        ·
          refine ⟨2008574891652623112769459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2678099855536830817025945 2008574891652623112769459)
          ·
            refine ⟨3012862337478934669154189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008574891652623112769459 3012862337478934669154189)
            ·
              refine ⟨1129823376554600500932821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3012862337478934669154189 1129823376554600500932821)
              ·
                refine ⟨26480235387998449240613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1129823376554600500932821 26480235387998449240613)
                ·
                  rfl

theorem cell20_174049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_174049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174049 prefixEnd_174049 := by exact prefixLift 174049
  have htrace : WordTrace (prefixWord ++ tailWord_174049) baseStart_174049 baseEnd_174049 := by
    simpa [prefixWord, tailWord_174049, baseEnd_174049] using wordTrace_append hprefix tailTrace_174049
  have hstable : (prefixWord ++ tailWord_174049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174049).length < 2 ^ (prefixWord ++ tailWord_174049).sum := by decide
  have hdescent : baseEnd_174049 < baseStart_174049 := by decide
  rcases family_descends (prefixWord ++ tailWord_174049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174087 : List Nat := [1, 1, 4, 3, 1, 10]
def baseStart_174087 : Nat := 118140960795 + 174087 * 2 ^ 59
def prefixEnd_174087 : Nat := 4983230072969 + 3 ^ 40 * 174087 * 2
def baseEnd_174087 : Nat := 2942890755534670535371

theorem tailTrace_174087 : CollatzResearch.WordTrace tailWord_174087 prefixEnd_174087 2942890755534670535371 := by
  unfold tailWord_174087
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349474520320005537648515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4232983013546670358432343 6349474520320005537648515)
  ·
    refine ⟨9524211780480008306472773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6349474520320005537648515 9524211780480008306472773)
    ·
      refine ⟨1785789708840001557463645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9524211780480008306472773 1785789708840001557463645)
      ·
        refine ⟨669671140815000584048867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1785789708840001557463645 669671140815000584048867)
        ·
          refine ⟨1004506711222500876073301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669671140815000584048867 1004506711222500876073301)
          ·
            refine ⟨2942890755534670535371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1004506711222500876073301 2942890755534670535371)
            ·
              rfl

theorem cell20_174087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 10].length) (baseStart_174087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174087 prefixEnd_174087 := by exact prefixLift 174087
  have htrace : WordTrace (prefixWord ++ tailWord_174087) baseStart_174087 baseEnd_174087 := by
    simpa [prefixWord, tailWord_174087, baseEnd_174087] using wordTrace_append hprefix tailTrace_174087
  have hstable : (prefixWord ++ tailWord_174087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174087).length < 2 ^ (prefixWord ++ tailWord_174087).sum := by decide
  have hdescent : baseEnd_174087 < baseStart_174087 := by decide
  rcases family_descends (prefixWord ++ tailWord_174087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174111 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 3]
def baseStart_174111 : Nat := 118140960795 + 174111 * 2 ^ 59
def prefixEnd_174111 : Nat := 4983230072969 + 3 ^ 40 * 174111 * 2
def baseEnd_174111 : Nat := 79469004653398687654919

theorem tailTrace_174111 : CollatzResearch.WordTrace tailWord_174111 prefixEnd_174111 79469004653398687654919 := by
  unfold tailWord_174111
  simp only [CollatzResearch.WordTrace]
  refine ⟨6350349872233057636522187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4233566581488705091014791 6350349872233057636522187)
  ·
    refine ⟨9525524808349586454783281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6350349872233057636522187 9525524808349586454783281)
    ·
      refine ⟨7144143606262189841087461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9525524808349586454783281 7144143606262189841087461)
      ·
        refine ⟨1339526926174160595203899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7144143606262189841087461 1339526926174160595203899)
        ·
          refine ⟨2009290389261240892805849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339526926174160595203899 2009290389261240892805849)
          ·
            refine ⟨1506967791945930669604387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2009290389261240892805849 1506967791945930669604387)
            ·
              refine ⟨2260451687918896004406581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506967791945930669604387 2260451687918896004406581)
              ·
                refine ⟨211917345742396500413117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2260451687918896004406581 211917345742396500413117)
                ·
                  refine ⟨79469004653398687654919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211917345742396500413117 79469004653398687654919)
                  ·
                    rfl

theorem cell20_174111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 3].length) (baseStart_174111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174111 prefixEnd_174111 := by exact prefixLift 174111
  have htrace : WordTrace (prefixWord ++ tailWord_174111) baseStart_174111 baseEnd_174111 := by
    simpa [prefixWord, tailWord_174111, baseEnd_174111] using wordTrace_append hprefix tailTrace_174111
  have hstable : (prefixWord ++ tailWord_174111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174111).length < 2 ^ (prefixWord ++ tailWord_174111).sum := by decide
  have hdescent : baseEnd_174111 < baseStart_174111 := by decide
  rcases family_descends (prefixWord ++ tailWord_174111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174135 : List Nat := [1, 1, 3, 1, 2, 2, 3, 5, 2]
def baseStart_174135 : Nat := 118140960795 + 174135 * 2 ^ 59
def prefixEnd_174135 : Nat := 4983230072969 + 3 ^ 40 * 174135 * 2
def baseEnd_174135 : Nat := 79479958907361270854821

theorem tailTrace_174135 : CollatzResearch.WordTrace tailWord_174135 prefixEnd_174135 79479958907361270854821 := by
  unfold tailWord_174135
  simp only [CollatzResearch.WordTrace]
  refine ⟨6351225224146109735395859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4234150149430739823597239 6351225224146109735395859)
  ·
    refine ⟨9526837836219164603093789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6351225224146109735395859 9526837836219164603093789)
    ·
      refine ⟨3572564188582186726160171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9526837836219164603093789 3572564188582186726160171)
      ·
        refine ⟨5358846282873280089240257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572564188582186726160171 5358846282873280089240257)
        ·
          refine ⟨4019134712154960066930193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5358846282873280089240257 4019134712154960066930193)
          ·
            refine ⟨3014351034116220050197645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4019134712154960066930193 3014351034116220050197645)
            ·
              refine ⟨1130381637793582518824117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3014351034116220050197645 1130381637793582518824117)
              ·
                refine ⟨105973278543148361139761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1130381637793582518824117 105973278543148361139761)
                ·
                  refine ⟨79479958907361270854821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105973278543148361139761 79479958907361270854821)
                  ·
                    rfl

theorem cell20_174135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 2].length) (baseStart_174135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174135 prefixEnd_174135 := by exact prefixLift 174135
  have htrace : WordTrace (prefixWord ++ tailWord_174135) baseStart_174135 baseEnd_174135 := by
    simpa [prefixWord, tailWord_174135, baseEnd_174135] using wordTrace_append hprefix tailTrace_174135
  have hstable : (prefixWord ++ tailWord_174135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174135).length < 2 ^ (prefixWord ++ tailWord_174135).sum := by decide
  have hdescent : baseEnd_174135 < baseStart_174135 := by decide
  rcases family_descends (prefixWord ++ tailWord_174135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174145 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 3]
def baseStart_174145 : Nat := 118140960795 + 174145 * 2 ^ 59
def prefixEnd_174145 : Nat := 4983230072969 + 3 ^ 40 * 174145 * 2
def baseEnd_174145 : Nat := 79484523179845680521447

theorem tailTrace_174145 : CollatzResearch.WordTrace tailWord_174145 prefixEnd_174145 79484523179845680521447 := by
  unfold tailWord_174145
  simp only [CollatzResearch.WordTrace]
  refine ⟨6351589954109881443259889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4234393302739920962173259 6351589954109881443259889)
  ·
    refine ⟨4763692465582411082444917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6351589954109881443259889 4763692465582411082444917)
    ·
      refine ⟨446596168648351038979211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4763692465582411082444917 446596168648351038979211)
      ·
        refine ⟨669894252972526558468817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446596168648351038979211 669894252972526558468817)
        ·
          refine ⟨502420689729394918851613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669894252972526558468817 502420689729394918851613)
          ·
            refine ⟨188407758648523094569355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 502420689729394918851613 188407758648523094569355)
            ·
              refine ⟨282611637972784641854033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188407758648523094569355 282611637972784641854033)
              ·
                refine ⟨211958728479588481390525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282611637972784641854033 211958728479588481390525)
                ·
                  refine ⟨79484523179845680521447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211958728479588481390525 79484523179845680521447)
                  ·
                    rfl

theorem cell20_174145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_174145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174145 prefixEnd_174145 := by exact prefixLift 174145
  have htrace : WordTrace (prefixWord ++ tailWord_174145) baseStart_174145 baseEnd_174145 := by
    simpa [prefixWord, tailWord_174145, baseEnd_174145] using wordTrace_append hprefix tailTrace_174145
  have hstable : (prefixWord ++ tailWord_174145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174145).length < 2 ^ (prefixWord ++ tailWord_174145).sum := by decide
  have hdescent : baseEnd_174145 < baseStart_174145 := by decide
  rcases family_descends (prefixWord ++ tailWord_174145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174156 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_174156 : Nat := 118140960795 + 174156 * 2 ^ 59
def prefixEnd_174156 : Nat := 4983230072969 + 3 ^ 40 * 174156 * 2
def baseEnd_174156 : Nat := 79489543879578531154735

theorem tailTrace_174156 : CollatzResearch.WordTrace tailWord_174156 prefixEnd_174156 79489543879578531154735 := by
  unfold tailWord_174156
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175995578535015160955161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4234660771380020214606881 3175995578535015160955161)
  ·
    refine ⟨2381996683901261370716371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3175995578535015160955161 2381996683901261370716371)
    ·
      refine ⟨3572995025851892056074557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381996683901261370716371 3572995025851892056074557)
      ·
        refine ⟨1339873134694459521027959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3572995025851892056074557 1339873134694459521027959)
        ·
          refine ⟨2009809702041689281541939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339873134694459521027959 2009809702041689281541939)
          ·
            refine ⟨3014714553062533922312909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009809702041689281541939 3014714553062533922312909)
            ·
              refine ⟨1130517957398450220867341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3014714553062533922312909 1130517957398450220867341)
              ·
                refine ⟨423944234024418832825253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130517957398450220867341 423944234024418832825253)
                ·
                  refine ⟨79489543879578531154735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423944234024418832825253 79489543879578531154735)
                  ·
                    rfl

theorem cell20_174156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_174156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174156 prefixEnd_174156 := by exact prefixLift 174156
  have htrace : WordTrace (prefixWord ++ tailWord_174156) baseStart_174156 baseEnd_174156 := by
    simpa [prefixWord, tailWord_174156, baseEnd_174156] using wordTrace_append hprefix tailTrace_174156
  have hstable : (prefixWord ++ tailWord_174156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174156).length < 2 ^ (prefixWord ++ tailWord_174156).sum := by decide
  have hdescent : baseEnd_174156 < baseStart_174156 := by decide
  rcases family_descends (prefixWord ++ tailWord_174156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174180 : List Nat := [2, 3, 1, 1, 2, 1, 6, 4]
def baseStart_174180 : Nat := 118140960795 + 174180 * 2 ^ 59
def prefixEnd_174180 : Nat := 4983230072969 + 3 ^ 40 * 174180 * 2
def baseEnd_174180 : Nat := 26500166044513704784879

theorem tailTrace_174180 : CollatzResearch.WordTrace tailWord_174180 prefixEnd_174180 26500166044513704784879 := by
  unfold tailWord_174180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3176433254491541210391997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4235244339322054947189329 3176433254491541210391997)
  ·
    refine ⟨1191162470434327953896999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3176433254491541210391997 1191162470434327953896999)
    ·
      refine ⟨1786743705651491930845499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191162470434327953896999 1786743705651491930845499)
      ·
        refine ⟨2680115558477237896268249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786743705651491930845499 2680115558477237896268249)
        ·
          refine ⟨2010086668857928422201187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2680115558477237896268249 2010086668857928422201187)
          ·
            refine ⟨3015130003286892633301781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010086668857928422201187 3015130003286892633301781)
            ·
              refine ⟨141334218904073092186021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3015130003286892633301781 141334218904073092186021)
              ·
                refine ⟨26500166044513704784879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141334218904073092186021 26500166044513704784879)
                ·
                  rfl

theorem cell20_174180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_174180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174180 prefixEnd_174180 := by exact prefixLift 174180
  have htrace : WordTrace (prefixWord ++ tailWord_174180) baseStart_174180 baseEnd_174180 := by
    simpa [prefixWord, tailWord_174180, baseEnd_174180] using wordTrace_append hprefix tailTrace_174180
  have hstable : (prefixWord ++ tailWord_174180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174180).length < 2 ^ (prefixWord ++ tailWord_174180).sum := by decide
  have hdescent : baseEnd_174180 < baseStart_174180 := by decide
  rcases family_descends (prefixWord ++ tailWord_174180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174186 : List Nat := [3, 1, 3, 2, 4, 1, 1, 3, 2]
def baseStart_174186 : Nat := 118140960795 + 174186 * 2 ^ 59
def prefixEnd_174186 : Nat := 4983230072969 + 3 ^ 40 * 174186 * 2
def baseEnd_174186 : Nat := 79503236697031760154613

theorem tailTrace_174186 : CollatzResearch.WordTrace tailWord_174186 prefixEnd_174186 79503236697031760154613 := by
  unfold tailWord_174186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588271336740336361375603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4235390231307563630334941 1588271336740336361375603)
  ·
    refine ⟨2382407005110504542063405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1588271336740336361375603 2382407005110504542063405)
    ·
      refine ⟨893402626916439203273777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2382407005110504542063405 893402626916439203273777)
      ·
        refine ⟨670051970187329402455333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 893402626916439203273777 670051970187329402455333)
        ·
          refine ⟨125634744410124262960375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 670051970187329402455333 125634744410124262960375)
          ·
            refine ⟨188452116615186394440563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125634744410124262960375 188452116615186394440563)
            ·
              refine ⟨282678174922779591660845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188452116615186394440563 282678174922779591660845)
              ·
                refine ⟨106004315596042346872817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282678174922779591660845 106004315596042346872817)
                ·
                  refine ⟨79503236697031760154613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106004315596042346872817 79503236697031760154613)
                  ·
                    rfl

theorem cell20_174186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_174186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174186 prefixEnd_174186 := by exact prefixLift 174186
  have htrace : WordTrace (prefixWord ++ tailWord_174186) baseStart_174186 baseEnd_174186 := by
    simpa [prefixWord, tailWord_174186, baseEnd_174186] using wordTrace_append hprefix tailTrace_174186
  have hstable : (prefixWord ++ tailWord_174186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174186).length < 2 ^ (prefixWord ++ tailWord_174186).sum := by decide
  have hdescent : baseEnd_174186 < baseStart_174186 := by decide
  rcases family_descends (prefixWord ++ tailWord_174186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174201 : List Nat := [1, 2, 1, 3, 4, 1, 8]
def baseStart_174201 : Nat := 118140960795 + 174201 * 2 ^ 59
def prefixEnd_174201 : Nat := 4983230072969 + 3 ^ 40 * 174201 * 2
def baseEnd_174201 : Nat := 8834453678417597183839

theorem tailTrace_174201 : CollatzResearch.WordTrace tailWord_174201 prefixEnd_174201 8834453678417597183839 := by
  unfold tailWord_174201
  simp only [CollatzResearch.WordTrace]
  refine ⟨6353632441907003007298457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4235754961271335338198971 6353632441907003007298457)
  ·
    refine ⟨4765224331430252255473843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6353632441907003007298457 4765224331430252255473843)
    ·
      refine ⟨7147836497145378383210765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4765224331430252255473843 7147836497145378383210765)
      ·
        refine ⟨2680438686429516893704037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7147836497145378383210765 2680438686429516893704037)
        ·
          refine ⟨502582253705534417569507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2680438686429516893704037 502582253705534417569507)
          ·
            refine ⟨753873380558301626354261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502582253705534417569507 753873380558301626354261)
            ·
              refine ⟨8834453678417597183839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 753873380558301626354261 8834453678417597183839)
              ·
                rfl

theorem cell20_174201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 8].length) (baseStart_174201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174201 prefixEnd_174201 := by exact prefixLift 174201
  have htrace : WordTrace (prefixWord ++ tailWord_174201) baseStart_174201 baseEnd_174201 := by
    simpa [prefixWord, tailWord_174201, baseEnd_174201] using wordTrace_append hprefix tailTrace_174201
  have hstable : (prefixWord ++ tailWord_174201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174201).length < 2 ^ (prefixWord ++ tailWord_174201).sum := by decide
  have hdescent : baseEnd_174201 < baseStart_174201 := by decide
  rcases family_descends (prefixWord ++ tailWord_174201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174211 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 4]
def baseStart_174211 : Nat := 118140960795 + 174211 * 2 ^ 59
def prefixEnd_174211 : Nat := 4983230072969 + 3 ^ 40 * 174211 * 2
def baseEnd_174211 : Nat := 79514647378242784321177

theorem tailTrace_174211 : CollatzResearch.WordTrace tailWord_174211 prefixEnd_174211 79514647378242784321177 := by
  unfold tailWord_174211
  simp only [CollatzResearch.WordTrace]
  refine ⟨6353997171870774715162487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4235998114580516476774991 6353997171870774715162487)
  ·
    refine ⟨9530995757806162072743731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6353997171870774715162487 9530995757806162072743731)
    ·
      refine ⟨14296493636709243109115597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9530995757806162072743731 14296493636709243109115597)
      ·
        refine ⟨5361185113765966165918349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14296493636709243109115597 5361185113765966165918349)
        ·
          refine ⟨2010444417662237312219381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5361185113765966165918349 2010444417662237312219381)
          ·
            refine ⟨188479164155834748020567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2010444417662237312219381 188479164155834748020567)
            ·
              refine ⟨282718746233752122030851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188479164155834748020567 282718746233752122030851)
              ·
                refine ⟨424078119350628183046277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282718746233752122030851 424078119350628183046277)
                ·
                  refine ⟨79514647378242784321177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 424078119350628183046277 79514647378242784321177)
                  ·
                    rfl

theorem cell20_174211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 4].length) (baseStart_174211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174211 prefixEnd_174211 := by exact prefixLift 174211
  have htrace : WordTrace (prefixWord ++ tailWord_174211) baseStart_174211 baseEnd_174211 := by
    simpa [prefixWord, tailWord_174211, baseEnd_174211] using wordTrace_append hprefix tailTrace_174211
  have hstable : (prefixWord ++ tailWord_174211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174211).length < 2 ^ (prefixWord ++ tailWord_174211).sum := by decide
  have hdescent : baseEnd_174211 < baseStart_174211 := by decide
  rcases family_descends (prefixWord ++ tailWord_174211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174218 : List Nat := [3, 1, 2, 3, 1, 3, 2, 5]
def baseStart_174218 : Nat := 118140960795 + 174218 * 2 ^ 59
def prefixEnd_174218 : Nat := 4983230072969 + 3 ^ 40 * 174218 * 2
def baseEnd_174218 : Nat := 26505947456327290362605

theorem tailTrace_174218 : CollatzResearch.WordTrace tailWord_174218 prefixEnd_174218 26505947456327290362605 := by
  unfold tailWord_174218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588563120711353727666827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4236168321896943273778205 1588563120711353727666827)
  ·
    refine ⟨2382844681067030591500241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1588563120711353727666827 2382844681067030591500241)
    ·
      refine ⟨1787133510800272943625181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2382844681067030591500241 1787133510800272943625181)
      ·
        refine ⟨670175066550102353859443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1787133510800272943625181 670175066550102353859443)
        ·
          refine ⟨1005262599825153530789165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670175066550102353859443 1005262599825153530789165)
          ·
            refine ⟨376973474934432574045937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1005262599825153530789165 376973474934432574045937)
            ·
              refine ⟨282730106200824430534453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376973474934432574045937 282730106200824430534453)
              ·
                refine ⟨26505947456327290362605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282730106200824430534453 26505947456327290362605)
                ·
                  rfl

theorem cell20_174218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_174218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174218 prefixEnd_174218 := by exact prefixLift 174218
  have htrace : WordTrace (prefixWord ++ tailWord_174218) baseStart_174218 baseEnd_174218 := by
    simpa [prefixWord, tailWord_174218, baseEnd_174218] using wordTrace_append hprefix tailTrace_174218
  have hstable : (prefixWord ++ tailWord_174218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174218).length < 2 ^ (prefixWord ++ tailWord_174218).sum := by decide
  have hdescent : baseEnd_174218 < baseStart_174218 := by decide
  rcases family_descends (prefixWord ++ tailWord_174218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174263 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 3]
def baseStart_174263 : Nat := 118140960795 + 174263 * 2 ^ 59
def prefixEnd_174263 : Nat := 4983230072969 + 3 ^ 40 * 174263 * 2
def baseEnd_174263 : Nat := 79538381595161714587631

theorem tailTrace_174263 : CollatzResearch.WordTrace tailWord_174263 prefixEnd_174263 79538381595161714587631 := by
  unfold tailWord_174263
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355893767682387596055443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4237262511788258397370295 6355893767682387596055443)
  ·
    refine ⟨9533840651523581394083165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6355893767682387596055443 9533840651523581394083165)
    ·
      refine ⟨3575190244321343022781187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9533840651523581394083165 3575190244321343022781187)
      ·
        refine ⟨5362785366482014534171781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575190244321343022781187 5362785366482014534171781)
        ·
          refine ⟨1005522256215377725157209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5362785366482014534171781 1005522256215377725157209)
          ·
            refine ⟨754141692161533293867907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005522256215377725157209 754141692161533293867907)
            ·
              refine ⟨1131212538242299940801861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754141692161533293867907 1131212538242299940801861)
              ·
                refine ⟨212102350920431238900349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1131212538242299940801861 212102350920431238900349)
                ·
                  refine ⟨79538381595161714587631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212102350920431238900349 79538381595161714587631)
                  ·
                    rfl

theorem cell20_174263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 3].length) (baseStart_174263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174263 prefixEnd_174263 := by exact prefixLift 174263
  have htrace : WordTrace (prefixWord ++ tailWord_174263) baseStart_174263 baseEnd_174263 := by
    simpa [prefixWord, tailWord_174263, baseEnd_174263] using wordTrace_append hprefix tailTrace_174263
  have hstable : (prefixWord ++ tailWord_174263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174263).length < 2 ^ (prefixWord ++ tailWord_174263).sum := by decide
  have hdescent : baseEnd_174263 < baseStart_174263 := by decide
  rcases family_descends (prefixWord ++ tailWord_174263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174266 : List Nat := [3, 1, 1, 1, 2, 2, 6, 2, 2]
def baseStart_174266 : Nat := 118140960795 + 174266 * 2 ^ 59
def prefixEnd_174266 : Nat := 4983230072969 + 3 ^ 40 * 174266 * 2
def baseEnd_174266 : Nat := 79539750876907037487619

theorem tailTrace_174266 : CollatzResearch.WordTrace tailWord_174266 prefixEnd_174266 79539750876907037487619 := by
  unfold tailWord_174266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1589000796667879777103663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4237335457781012738943101 1589000796667879777103663)
  ·
    refine ⟨2383501195001819665655495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1589000796667879777103663 2383501195001819665655495)
    ·
      refine ⟨3575251792502729498483243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2383501195001819665655495 3575251792502729498483243)
      ·
        refine ⟨5362877688754094247724865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575251792502729498483243 5362877688754094247724865)
        ·
          refine ⟨4022158266565570685793649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5362877688754094247724865 4022158266565570685793649)
          ·
            refine ⟨3016618699924178014345237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4022158266565570685793649 3016618699924178014345237)
            ·
              refine ⟨141404001558945844422433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3016618699924178014345237 141404001558945844422433)
              ·
                refine ⟨106053001169209383316825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141404001558945844422433 106053001169209383316825)
                ·
                  refine ⟨79539750876907037487619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106053001169209383316825 79539750876907037487619)
                  ·
                    rfl

theorem cell20_174266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_174266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174266 prefixEnd_174266 := by exact prefixLift 174266
  have htrace : WordTrace (prefixWord ++ tailWord_174266) baseStart_174266 baseEnd_174266 := by
    simpa [prefixWord, tailWord_174266, baseEnd_174266] using wordTrace_append hprefix tailTrace_174266
  have hstable : (prefixWord ++ tailWord_174266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174266).length < 2 ^ (prefixWord ++ tailWord_174266).sum := by decide
  have hdescent : baseEnd_174266 < baseStart_174266 := by decide
  rcases family_descends (prefixWord ++ tailWord_174266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174277 : List Nat := [1, 3, 1, 1, 1, 1, 7, 5]
def baseStart_174277 : Nat := 118140960795 + 174277 * 2 ^ 59
def prefixEnd_174277 : Nat := 4983230072969 + 3 ^ 40 * 174277 * 2
def baseEnd_174277 : Nat := 26514923858879962706969

theorem tailTrace_174277 : CollatzResearch.WordTrace tailWord_174277 prefixEnd_174277 26514923858879962706969 := by
  unfold tailWord_174277
  simp only [CollatzResearch.WordTrace]
  refine ⟨6356404389631667987065085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4237602926421111991376723 6356404389631667987065085)
  ·
    refine ⟨2383651646111875495149407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6356404389631667987065085 2383651646111875495149407)
    ·
      refine ⟨3575477469167813242724111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2383651646111875495149407 3575477469167813242724111)
      ·
        refine ⟨5363216203751719864086167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575477469167813242724111 5363216203751719864086167)
        ·
          refine ⟨8044824305627579796129251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363216203751719864086167 8044824305627579796129251)
          ·
            refine ⟨12067236458441369694193877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044824305627579796129251 12067236458441369694193877)
            ·
              refine ⟨282825854494719602207669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12067236458441369694193877 282825854494719602207669)
              ·
                refine ⟨26514923858879962706969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282825854494719602207669 26514923858879962706969)
                ·
                  rfl

theorem cell20_174277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_174277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174277 prefixEnd_174277 := by exact prefixLift 174277
  have htrace : WordTrace (prefixWord ++ tailWord_174277) baseStart_174277 baseEnd_174277 := by
    simpa [prefixWord, tailWord_174277, baseEnd_174277] using wordTrace_append hprefix tailTrace_174277
  have hstable : (prefixWord ++ tailWord_174277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174277).length < 2 ^ (prefixWord ++ tailWord_174277).sum := by decide
  have hdescent : baseEnd_174277 < baseStart_174277 := by decide
  rcases family_descends (prefixWord ++ tailWord_174277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174300 : List Nat := [2, 2, 5, 2, 1, 1, 2, 3, 2]
def baseStart_174300 : Nat := 118140960795 + 174300 * 2 ^ 59
def prefixEnd_174300 : Nat := 4983230072969 + 3 ^ 40 * 174300 * 2
def baseEnd_174300 : Nat := 79555269403354030354147

theorem tailTrace_174300 : CollatzResearch.WordTrace tailWord_174300 prefixEnd_174300 79555269403354030354147 := by
  unfold tailWord_174300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3178621634274171457576177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4238162179032228610101569 3178621634274171457576177)
  ·
    refine ⟨2383966225705628593182133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3178621634274171457576177 2383966225705628593182133)
    ·
      refine ⟨223496833659902680610825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2383966225705628593182133 223496833659902680610825)
      ·
        refine ⟨167622625244927010458119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223496833659902680610825 167622625244927010458119)
        ·
          refine ⟨251433937867390515687179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167622625244927010458119 251433937867390515687179)
          ·
            refine ⟨377150906801085773530769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251433937867390515687179 377150906801085773530769)
            ·
              refine ⟨282863180100814330148077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377150906801085773530769 282863180100814330148077)
              ·
                refine ⟨106073692537805373805529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282863180100814330148077 106073692537805373805529)
                ·
                  refine ⟨79555269403354030354147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106073692537805373805529 79555269403354030354147)
                  ·
                    rfl

theorem cell20_174300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_174300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174300 prefixEnd_174300 := by exact prefixLift 174300
  have htrace : WordTrace (prefixWord ++ tailWord_174300) baseStart_174300 baseEnd_174300 := by
    simpa [prefixWord, tailWord_174300, baseEnd_174300] using wordTrace_append hprefix tailTrace_174300
  have hstable : (prefixWord ++ tailWord_174300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174300).length < 2 ^ (prefixWord ++ tailWord_174300).sum := by decide
  have hdescent : baseEnd_174300 < baseStart_174300 := by decide
  rcases family_descends (prefixWord ++ tailWord_174300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174346 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_174346 : Nat := 118140960795 + 174346 * 2 ^ 59
def prefixEnd_174346 : Nat := 4983230072969 + 3 ^ 40 * 174346 * 2
def baseEnd_174346 : Nat := 79576265056782314820625

theorem tailTrace_174346 : CollatzResearch.WordTrace tailWord_174346 prefixEnd_174346 79576265056782314820625 := by
  unfold tailWord_174346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1589730256595423192831723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4239280684254461847551261 1589730256595423192831723)
  ·
    refine ⟨2384595384893134789247585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1589730256595423192831723 2384595384893134789247585)
    ·
      refine ⟨1788446538669851091935689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2384595384893134789247585 1788446538669851091935689)
      ·
        refine ⟨1341334904002388318951767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1788446538669851091935689 1341334904002388318951767)
        ·
          refine ⟨2012002356003582478427651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1341334904002388318951767 2012002356003582478427651)
          ·
            refine ⟨3018003534005373717641477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012002356003582478427651 3018003534005373717641477)
            ·
              refine ⟨565875662626007572057777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3018003534005373717641477 565875662626007572057777)
              ·
                refine ⟨424406746969505679043333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565875662626007572057777 424406746969505679043333)
                ·
                  refine ⟨79576265056782314820625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 424406746969505679043333 79576265056782314820625)
                  ·
                    rfl

theorem cell20_174346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_174346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174346 prefixEnd_174346 := by exact prefixLift 174346
  have htrace : WordTrace (prefixWord ++ tailWord_174346) baseStart_174346 baseEnd_174346 := by
    simpa [prefixWord, tailWord_174346, baseEnd_174346] using wordTrace_append hprefix tailTrace_174346
  have hstable : (prefixWord ++ tailWord_174346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174346).length < 2 ^ (prefixWord ++ tailWord_174346).sum := by decide
  have hdescent : baseEnd_174346 < baseStart_174346 := by decide
  rcases family_descends (prefixWord ++ tailWord_174346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174353 : List Nat := [1, 2, 2, 1, 1, 6, 1, 6]
def baseStart_174353 : Nat := 118140960795 + 174353 * 2 ^ 59
def prefixEnd_174353 : Nat := 4983230072969 + 3 ^ 40 * 174353 * 2
def baseEnd_174353 : Nat := 26526486682507133862421

theorem tailTrace_174353 : CollatzResearch.WordTrace tailWord_174353 prefixEnd_174353 26526486682507133862421 := by
  unfold tailWord_174353
  simp only [CollatzResearch.WordTrace]
  refine ⟨6359176337356332966831713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4239450891570888644554475 6359176337356332966831713)
  ·
    refine ⟨4769382253017249725123785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6359176337356332966831713 4769382253017249725123785)
    ·
      refine ⟨3577036689762937293842839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4769382253017249725123785 3577036689762937293842839)
      ·
        refine ⟨5365555034644405940764259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3577036689762937293842839 5365555034644405940764259)
        ·
          refine ⟨8048332551966608911146389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365555034644405940764259 8048332551966608911146389)
          ·
            refine ⟨377265588373434792709987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8048332551966608911146389 377265588373434792709987)
            ·
              refine ⟨565898382560152189064981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377265588373434792709987 565898382560152189064981)
              ·
                refine ⟨26526486682507133862421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 565898382560152189064981 26526486682507133862421)
                ·
                  rfl

theorem cell20_174353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_174353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174353 prefixEnd_174353 := by exact prefixLift 174353
  have htrace : WordTrace (prefixWord ++ tailWord_174353) baseStart_174353 baseEnd_174353 := by
    simpa [prefixWord, tailWord_174353, baseEnd_174353] using wordTrace_append hprefix tailTrace_174353
  have hstable : (prefixWord ++ tailWord_174353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174353).length < 2 ^ (prefixWord ++ tailWord_174353).sum := by decide
  have hdescent : baseEnd_174353 < baseStart_174353 := by decide
  rcases family_descends (prefixWord ++ tailWord_174353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174360 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_174360 : Nat := 118140960795 + 174360 * 2 ^ 59
def prefixEnd_174360 : Nat := 4983230072969 + 3 ^ 40 * 174360 * 2
def baseEnd_174360 : Nat := 79582655038260488353901

theorem tailTrace_174360 : CollatzResearch.WordTrace tailWord_174360 prefixEnd_174360 79582655038260488353901 := by
  unfold tailWord_174360
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179715824165486581168267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4239621098887315441557689 3179715824165486581168267)
  ·
    refine ⟨4769573736248229871752401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3179715824165486581168267 4769573736248229871752401)
    ·
      refine ⟨3577180302186172403814301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4769573736248229871752401 3577180302186172403814301)
      ·
        refine ⟨1341442613319814651430363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3577180302186172403814301 1341442613319814651430363)
        ·
          refine ⟨2012163919979721977145545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1341442613319814651430363 2012163919979721977145545)
          ·
            refine ⟨1509122939984791482859159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2012163919979721977145545 1509122939984791482859159)
            ·
              refine ⟨2263684409977187224288739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509122939984791482859159 2263684409977187224288739)
              ·
                refine ⟨3395526614965780836433109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263684409977187224288739 3395526614965780836433109)
                ·
                  refine ⟨79582655038260488353901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3395526614965780836433109 79582655038260488353901)
                  ·
                    rfl

theorem cell20_174360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_174360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174360 prefixEnd_174360 := by exact prefixLift 174360
  have htrace : WordTrace (prefixWord ++ tailWord_174360) baseStart_174360 baseEnd_174360 := by
    simpa [prefixWord, tailWord_174360, baseEnd_174360] using wordTrace_append hprefix tailTrace_174360
  have hstable : (prefixWord ++ tailWord_174360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174360).length < 2 ^ (prefixWord ++ tailWord_174360).sum := by decide
  have hdescent : baseEnd_174360 < baseStart_174360 := by decide
  rcases family_descends (prefixWord ++ tailWord_174360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174363 : List Nat := [1, 1, 1, 1, 1, 1, 9, 3, 2]
def baseStart_174363 : Nat := 118140960795 + 174363 * 2 ^ 59
def prefixEnd_174363 : Nat := 4983230072969 + 3 ^ 40 * 174363 * 2
def baseEnd_174363 : Nat := 79584024320005811253889

theorem tailTrace_174363 : CollatzResearch.WordTrace tailWord_174363 prefixEnd_174363 79584024320005811253889 := by
  unfold tailWord_174363
  simp only [CollatzResearch.WordTrace]
  refine ⟨6359541067320104674695743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4239694044880069783130495 6359541067320104674695743)
  ·
    refine ⟨9539311600980157012043615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6359541067320104674695743 9539311600980157012043615)
    ·
      refine ⟨14308967401470235518065423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9539311600980157012043615 14308967401470235518065423)
      ·
        refine ⟨21463451102205353277098135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14308967401470235518065423 21463451102205353277098135)
        ·
          refine ⟨32195176653308029915647203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21463451102205353277098135 32195176653308029915647203)
          ·
            refine ⟨48292764979962044873470805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32195176653308029915647203 48292764979962044873470805)
            ·
              refine ⟨282965419804465106680493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 48292764979962044873470805 282965419804465106680493)
              ·
                refine ⟨106112032426674415005185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282965419804465106680493 106112032426674415005185)
                ·
                  refine ⟨79584024320005811253889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106112032426674415005185 79584024320005811253889)
                  ·
                    rfl

theorem cell20_174363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 2].length) (baseStart_174363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174363 prefixEnd_174363 := by exact prefixLift 174363
  have htrace : WordTrace (prefixWord ++ tailWord_174363) baseStart_174363 baseEnd_174363 := by
    simpa [prefixWord, tailWord_174363, baseEnd_174363] using wordTrace_append hprefix tailTrace_174363
  have hstable : (prefixWord ++ tailWord_174363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174363).length < 2 ^ (prefixWord ++ tailWord_174363).sum := by decide
  have hdescent : baseEnd_174363 < baseStart_174363 := by decide
  rcases family_descends (prefixWord ++ tailWord_174363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174370 : List Nat := [3, 3, 1, 1, 3, 3, 6]
def baseStart_174370 : Nat := 118140960795 + 174370 * 2 ^ 59
def prefixEnd_174370 : Nat := 4983230072969 + 3 ^ 40 * 174370 * 2
def baseEnd_174370 : Nat := 8843024367860544224503

theorem tailTrace_174370 : CollatzResearch.WordTrace tailWord_174370 prefixEnd_174370 8843024367860544224503 := by
  unfold tailWord_174370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1589949094573686217550141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4239864252196496580133709 1589949094573686217550141)
  ·
    refine ⟨596230910465132331581303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1589949094573686217550141 596230910465132331581303)
    ·
      refine ⟨894346365697698497371955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 596230910465132331581303 894346365697698497371955)
      ·
        refine ⟨1341519548546547746057933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894346365697698497371955 1341519548546547746057933)
        ·
          refine ⟨503069830704955404771725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1341519548546547746057933 503069830704955404771725)
          ·
            refine ⟨188651186514358276789397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 503069830704955404771725 188651186514358276789397)
            ·
              refine ⟨8843024367860544224503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 188651186514358276789397 8843024367860544224503)
              ·
                rfl

theorem cell20_174370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 6].length) (baseStart_174370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174370 prefixEnd_174370 := by exact prefixLift 174370
  have htrace : WordTrace (prefixWord ++ tailWord_174370) baseStart_174370 baseEnd_174370 := by
    simpa [prefixWord, tailWord_174370, baseEnd_174370] using wordTrace_append hprefix tailTrace_174370
  have hstable : (prefixWord ++ tailWord_174370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174370).length < 2 ^ (prefixWord ++ tailWord_174370).sum := by decide
  have hdescent : baseEnd_174370 < baseStart_174370 := by decide
  rcases family_descends (prefixWord ++ tailWord_174370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174394 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_174394 : Nat := 118140960795 + 174394 * 2 ^ 59
def prefixEnd_174394 : Nat := 4983230072969 + 3 ^ 40 * 174394 * 2
def baseEnd_174394 : Nat := 79598173564707481220429

theorem tailTrace_174394 : CollatzResearch.WordTrace tailWord_174394 prefixEnd_174394 79598173564707481220429 := by
  unfold tailWord_174394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1590167932551949242268559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4240447820138531312716157 1590167932551949242268559)
  ·
    refine ⟨2385251898827923863402839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1590167932551949242268559 2385251898827923863402839)
    ·
      refine ⟨3577877848241885795104259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2385251898827923863402839 3577877848241885795104259)
      ·
        refine ⟨5366816772362828692656389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3577877848241885795104259 5366816772362828692656389)
        ·
          refine ⟨1006278144818030379873073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5366816772362828692656389 1006278144818030379873073)
          ·
            refine ⟨754708608613522784904805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1006278144818030379873073 754708608613522784904805)
            ·
              refine ⟨141507864115035522169651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 754708608613522784904805 141507864115035522169651)
              ·
                refine ⟨212261796172553283254477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141507864115035522169651 212261796172553283254477)
                ·
                  refine ⟨79598173564707481220429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212261796172553283254477 79598173564707481220429)
                  ·
                    rfl

theorem cell20_174394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_174394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174394 prefixEnd_174394 := by exact prefixLift 174394
  have htrace : WordTrace (prefixWord ++ tailWord_174394) baseStart_174394 baseEnd_174394 := by
    simpa [prefixWord, tailWord_174394, baseEnd_174394] using wordTrace_append hprefix tailTrace_174394
  have hstable : (prefixWord ++ tailWord_174394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174394).length < 2 ^ (prefixWord ++ tailWord_174394).sum := by decide
  have hdescent : baseEnd_174394 < baseStart_174394 := by decide
  rcases family_descends (prefixWord ++ tailWord_174394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174432 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 3]
def baseStart_174432 : Nat := 118140960795 + 174432 * 2 ^ 59
def prefixEnd_174432 : Nat := 4983230072969 + 3 ^ 40 * 174432 * 2
def baseEnd_174432 : Nat := 79615517800148237953607

theorem tailTrace_174432 : CollatzResearch.WordTrace tailWord_174432 prefixEnd_174432 79615517800148237953607 := by
  unfold tailWord_174432
  simp only [CollatzResearch.WordTrace]
  refine ⟨3181028852035064729478775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4241371802713419639305033 3181028852035064729478775)
  ·
    refine ⟨4771543278052597094218163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3181028852035064729478775 4771543278052597094218163)
    ·
      refine ⟨7157314917078895641327245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4771543278052597094218163 7157314917078895641327245)
      ·
        refine ⟨2683993093904585865497717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7157314917078895641327245 2683993093904585865497717)
        ·
          refine ⟨251624352553554924890411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2683993093904585865497717 251624352553554924890411)
          ·
            refine ⟨377436528830332387335617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251624352553554924890411 377436528830332387335617)
            ·
              refine ⟨283077396622749290501713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377436528830332387335617 283077396622749290501713)
              ·
                refine ⟨212308047467061967876285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283077396622749290501713 212308047467061967876285)
                ·
                  refine ⟨79615517800148237953607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212308047467061967876285 79615517800148237953607)
                  ·
                    rfl

theorem cell20_174432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_174432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174432 prefixEnd_174432 := by exact prefixLift 174432
  have htrace : WordTrace (prefixWord ++ tailWord_174432) baseStart_174432 baseEnd_174432 := by
    simpa [prefixWord, tailWord_174432, baseEnd_174432] using wordTrace_append hprefix tailTrace_174432
  have hstable : (prefixWord ++ tailWord_174432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174432).length < 2 ^ (prefixWord ++ tailWord_174432).sum := by decide
  have hdescent : baseEnd_174432 < baseStart_174432 := by decide
  rcases family_descends (prefixWord ++ tailWord_174432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174484 : List Nat := [2, 4, 2, 1, 3, 1, 7]
def baseStart_174484 : Nat := 118140960795 + 174484 * 2 ^ 59
def prefixEnd_174484 : Nat := 4983230072969 + 3 ^ 40 * 174484 * 2
def baseEnd_174484 : Nat := 8848805779674129802229

theorem tailTrace_174484 : CollatzResearch.WordTrace tailWord_174484 prefixEnd_174484 8848805779674129802229 := by
  unfold tailWord_174484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3181977149940871169925253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4242636199921161559900337 3181977149940871169925253)
  ·
    refine ⟨596620715613913344360985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3181977149940871169925253 596620715613913344360985)
    ·
      refine ⟨447465536710435008270739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 596620715613913344360985 447465536710435008270739)
      ·
        refine ⟨671198305065652512406109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447465536710435008270739 671198305065652512406109)
        ·
          refine ⟨251699364399619692152291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 671198305065652512406109 251699364399619692152291)
          ·
            refine ⟨377549046599429538228437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251699364399619692152291 377549046599429538228437)
            ·
              refine ⟨8848805779674129802229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 377549046599429538228437 8848805779674129802229)
              ·
                rfl

theorem cell20_174484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 7].length) (baseStart_174484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174484 prefixEnd_174484 := by exact prefixLift 174484
  have htrace : WordTrace (prefixWord ++ tailWord_174484) baseStart_174484 baseEnd_174484 := by
    simpa [prefixWord, tailWord_174484, baseEnd_174484] using wordTrace_append hprefix tailTrace_174484
  have hstable : (prefixWord ++ tailWord_174484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174484).length < 2 ^ (prefixWord ++ tailWord_174484).sum := by decide
  have hdescent : baseEnd_174484 < baseStart_174484 := by decide
  rcases family_descends (prefixWord ++ tailWord_174484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174494 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_174494 : Nat := 118140960795 + 174494 * 2 ^ 59
def prefixEnd_174494 : Nat := 4983230072969 + 3 ^ 40 * 174494 * 2
def baseEnd_174494 : Nat := 79643816289551577886687

theorem tailTrace_174494 : CollatzResearch.WordTrace tailWord_174494 prefixEnd_174494 79643816289551577886687 := by
  unfold tailWord_174494
  simp only [CollatzResearch.WordTrace]
  refine ⟨795539878730689255964317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4242879353230342698476357 795539878730689255964317)
  ·
    refine ⟨298327454524008470986619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 795539878730689255964317 298327454524008470986619)
    ·
      refine ⟨447491181786012706479929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298327454524008470986619 447491181786012706479929)
      ·
        refine ⟨335618386339509529859947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447491181786012706479929 335618386339509529859947)
        ·
          refine ⟨503427579509264294789921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335618386339509529859947 503427579509264294789921)
          ·
            refine ⟨377570684631948221092441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503427579509264294789921 377570684631948221092441)
            ·
              refine ⟨283178013473961165819331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377570684631948221092441 283178013473961165819331)
              ·
                refine ⟨424767020210941748728997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283178013473961165819331 424767020210941748728997)
                ·
                  refine ⟨79643816289551577886687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 424767020210941748728997 79643816289551577886687)
                  ·
                    rfl

theorem cell20_174494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_174494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174494 prefixEnd_174494 := by exact prefixLift 174494
  have htrace : WordTrace (prefixWord ++ tailWord_174494) baseStart_174494 baseEnd_174494 := by
    simpa [prefixWord, tailWord_174494, baseEnd_174494] using wordTrace_append hprefix tailTrace_174494
  have hstable : (prefixWord ++ tailWord_174494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174494).length < 2 ^ (prefixWord ++ tailWord_174494).sum := by decide
  have hdescent : baseEnd_174494 < baseStart_174494 := by decide
  rcases family_descends (prefixWord ++ tailWord_174494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174563 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 3]
def baseStart_174563 : Nat := 118140960795 + 174563 * 2 ^ 59
def prefixEnd_174563 : Nat := 4983230072969 + 3 ^ 40 * 174563 * 2
def baseEnd_174563 : Nat := 79675309769694004586405

theorem tailTrace_174563 : CollatzResearch.WordTrace tailWord_174563 prefixEnd_174563 79675309769694004586405 := by
  unfold tailWord_174563
  simp only [CollatzResearch.WordTrace]
  refine ⟨6366835666595538831976343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4244557111063692554650895 6366835666595538831976343)
  ·
    refine ⟨9550253499893308247964515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6366835666595538831976343 9550253499893308247964515)
    ·
      refine ⟨14325380249839962371946773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9550253499893308247964515 14325380249839962371946773)
      ·
        refine ⟨671502199211248236185005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14325380249839962371946773 671502199211248236185005)
        ·
          refine ⟨251813324704218088569377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 671502199211248236185005 251813324704218088569377)
          ·
            refine ⟨188859993528163566427033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251813324704218088569377 188859993528163566427033)
            ·
              refine ⟨141644995146122674820275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188859993528163566427033 141644995146122674820275)
              ·
                refine ⟨212467492719184012230413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141644995146122674820275 212467492719184012230413)
                ·
                  refine ⟨79675309769694004586405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212467492719184012230413 79675309769694004586405)
                  ·
                    rfl

theorem cell20_174563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 3].length) (baseStart_174563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174563 prefixEnd_174563 := by exact prefixLift 174563
  have htrace : WordTrace (prefixWord ++ tailWord_174563) baseStart_174563 baseEnd_174563 := by
    simpa [prefixWord, tailWord_174563, baseEnd_174563] using wordTrace_append hprefix tailTrace_174563
  have hstable : (prefixWord ++ tailWord_174563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174563).length < 2 ^ (prefixWord ++ tailWord_174563).sum := by decide
  have hdescent : baseEnd_174563 < baseStart_174563 := by decide
  rcases family_descends (prefixWord ++ tailWord_174563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174567 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 3]
def baseStart_174567 : Nat := 118140960795 + 174567 * 2 ^ 59
def prefixEnd_174567 : Nat := 4983230072969 + 3 ^ 40 * 174567 * 2
def baseEnd_174567 : Nat := 79677135478687768453055

theorem tailTrace_174567 : CollatzResearch.WordTrace tailWord_174567 prefixEnd_174567 79677135478687768453055 := by
  unfold tailWord_174567
  simp only [CollatzResearch.WordTrace]
  refine ⟨6366981558581047515121955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4244654372387365010081303 6366981558581047515121955)
  ·
    refine ⟨9550472337871571272682933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6366981558581047515121955 9550472337871571272682933)
    ·
      refine ⟨895356781675459806814025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9550472337871571272682933 895356781675459806814025)
      ·
        refine ⟨671517586256594855110519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 895356781675459806814025 671517586256594855110519)
        ·
          refine ⟨1007276379384892282665779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671517586256594855110519 1007276379384892282665779)
          ·
            refine ⟨1510914569077338423998669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007276379384892282665779 1510914569077338423998669)
            ·
              refine ⟨566592963404001908999501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1510914569077338423998669 566592963404001908999501)
              ·
                refine ⟨212472361276500715874813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566592963404001908999501 212472361276500715874813)
                ·
                  refine ⟨79677135478687768453055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212472361276500715874813 79677135478687768453055)
                  ·
                    rfl

theorem cell20_174567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 3].length) (baseStart_174567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174567 prefixEnd_174567 := by exact prefixLift 174567
  have htrace : WordTrace (prefixWord ++ tailWord_174567) baseStart_174567 baseEnd_174567 := by
    simpa [prefixWord, tailWord_174567, baseEnd_174567] using wordTrace_append hprefix tailTrace_174567
  have hstable : (prefixWord ++ tailWord_174567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174567).length < 2 ^ (prefixWord ++ tailWord_174567).sum := by decide
  have hdescent : baseEnd_174567 < baseStart_174567 := by decide
  rcases family_descends (prefixWord ++ tailWord_174567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174615 : List Nat := [1, 1, 3, 6, 1, 2, 1, 5]
def baseStart_174615 : Nat := 118140960795 + 174615 * 2 ^ 59
def prefixEnd_174615 : Nat := 4983230072969 + 3 ^ 40 * 174615 * 2
def baseEnd_174615 : Nat := 26566347995537644950953

theorem tailTrace_174615 : CollatzResearch.WordTrace tailWord_174615 prefixEnd_174615 26566347995537644950953 := by
  unfold tailWord_174615
  simp only [CollatzResearch.WordTrace]
  refine ⟨6368732262407151712869299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4245821508271434475246199 6368732262407151712869299)
  ·
    refine ⟨9553098393610727569303949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6368732262407151712869299 9553098393610727569303949)
    ·
      refine ⟨3582411897604022838488981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9553098393610727569303949 3582411897604022838488981)
      ·
        refine ⟨167925557700188570554171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3582411897604022838488981 167925557700188570554171)
        ·
          refine ⟨251888336550282855831257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167925557700188570554171 251888336550282855831257)
          ·
            refine ⟨188916252412712141873443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251888336550282855831257 188916252412712141873443)
            ·
              refine ⟨283374378619068212810165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188916252412712141873443 283374378619068212810165)
              ·
                refine ⟨26566347995537644950953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 283374378619068212810165 26566347995537644950953)
                ·
                  rfl

theorem cell20_174615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 5].length) (baseStart_174615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174615 prefixEnd_174615 := by exact prefixLift 174615
  have htrace : WordTrace (prefixWord ++ tailWord_174615) baseStart_174615 baseEnd_174615 := by
    simpa [prefixWord, tailWord_174615, baseEnd_174615] using wordTrace_append hprefix tailTrace_174615
  have hstable : (prefixWord ++ tailWord_174615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174615).length < 2 ^ (prefixWord ++ tailWord_174615).sum := by decide
  have hdescent : baseEnd_174615 < baseStart_174615 := by decide
  rcases family_descends (prefixWord ++ tailWord_174615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174626 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_174626 : Nat := 118140960795 + 174626 * 2 ^ 59
def prefixEnd_174626 : Nat := 4983230072969 + 3 ^ 40 * 174626 * 2
def baseEnd_174626 : Nat := 79704064686345785486147

theorem tailTrace_174626 : CollatzResearch.WordTrace tailWord_174626 prefixEnd_174626 79704064686345785486147 := by
  unfold tailWord_174626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1592283366341825147879933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4246088976911533727679821 1592283366341825147879933)
  ·
    refine ⟨597106262378184430454975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1592283366341825147879933 597106262378184430454975)
    ·
      refine ⟨895659393567276645682463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597106262378184430454975 895659393567276645682463)
      ·
        refine ⟨1343489090350914968523695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 895659393567276645682463 1343489090350914968523695)
        ·
          refine ⟨2015233635526372452785543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343489090350914968523695 2015233635526372452785543)
          ·
            refine ⟨3022850453289558679178315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015233635526372452785543 3022850453289558679178315)
            ·
              refine ⟨4534275679934338018767473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022850453289558679178315 4534275679934338018767473)
              ·
                refine ⟨3400706759950753514075605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4534275679934338018767473 3400706759950753514075605)
                ·
                  refine ⟨79704064686345785486147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3400706759950753514075605 79704064686345785486147)
                  ·
                    rfl

theorem cell20_174626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_174626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174626 prefixEnd_174626 := by exact prefixLift 174626
  have htrace : WordTrace (prefixWord ++ tailWord_174626) baseStart_174626 baseEnd_174626 := by
    simpa [prefixWord, tailWord_174626, baseEnd_174626] using wordTrace_append hprefix tailTrace_174626
  have hstable : (prefixWord ++ tailWord_174626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174626).length < 2 ^ (prefixWord ++ tailWord_174626).sum := by decide
  have hdescent : baseEnd_174626 < baseStart_174626 := by decide
  rcases family_descends (prefixWord ++ tailWord_174626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174640 : List Nat := [2, 1, 1, 1, 2, 3, 2, 8]
def baseStart_174640 : Nat := 118140960795 + 174640 * 2 ^ 59
def prefixEnd_174640 : Nat := 4983230072969 + 3 ^ 40 * 174640 * 2
def baseEnd_174640 : Nat := 26570151555941319673141

theorem tailTrace_174640 : CollatzResearch.WordTrace tailWord_174640 prefixEnd_174640 26570151555941319673141 := by
  unfold tailWord_174640
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184822043658290491264687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4246429391544387321686249 3184822043658290491264687)
  ·
    refine ⟨4777233065487435736897031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3184822043658290491264687 4777233065487435736897031)
    ·
      refine ⟨7165849598231153605345547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4777233065487435736897031 7165849598231153605345547)
      ·
        refine ⟨10748774397346730408018321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7165849598231153605345547 10748774397346730408018321)
        ·
          refine ⟨8061580798010047806013741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10748774397346730408018321 8061580798010047806013741)
          ·
            refine ⟨3023092799253767927255153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8061580798010047806013741 3023092799253767927255153)
            ·
              refine ⟨2267319599440325945441365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3023092799253767927255153 2267319599440325945441365)
              ·
                refine ⟨26570151555941319673141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2267319599440325945441365 26570151555941319673141)
                ·
                  rfl

theorem cell20_174640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_174640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174640 prefixEnd_174640 := by exact prefixLift 174640
  have htrace : WordTrace (prefixWord ++ tailWord_174640) baseStart_174640 baseEnd_174640 := by
    simpa [prefixWord, tailWord_174640, baseEnd_174640] using wordTrace_append hprefix tailTrace_174640
  have hstable : (prefixWord ++ tailWord_174640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174640).length < 2 ^ (prefixWord ++ tailWord_174640).sum := by decide
  have hdescent : baseEnd_174640 < baseStart_174640 := by decide
  rcases family_descends (prefixWord ++ tailWord_174640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174646 : List Nat := [5, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_174646 : Nat := 118140960795 + 174646 * 2 ^ 59
def prefixEnd_174646 : Nat := 4983230072969 + 3 ^ 40 * 174646 * 2
def baseEnd_174646 : Nat := 79713193231314604819399

theorem tailTrace_174646 : CollatzResearch.WordTrace tailWord_174646 prefixEnd_174646 79713193231314604819399 := by
  unfold tailWord_174646
  simp only [CollatzResearch.WordTrace]
  refine ⟨398116432830927750452987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4246575283529896004831861 398116432830927750452987)
  ·
    refine ⟨597174649246391625679481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 398116432830927750452987 597174649246391625679481)
    ·
      refine ⟨447880986934793719259611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 597174649246391625679481 447880986934793719259611)
      ·
        refine ⟨671821480402190578889417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447880986934793719259611 671821480402190578889417)
        ·
          refine ⟨503866110301642934167063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671821480402190578889417 503866110301642934167063)
          ·
            refine ⟨755799165452464401250595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503866110301642934167063 755799165452464401250595)
            ·
              refine ⟨1133698748178696601875893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755799165452464401250595 1133698748178696601875893)
              ·
                refine ⟨106284257641752806425865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1133698748178696601875893 106284257641752806425865)
                ·
                  refine ⟨79713193231314604819399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106284257641752806425865 79713193231314604819399)
                  ·
                    rfl

theorem cell20_174646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_174646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174646 prefixEnd_174646 := by exact prefixLift 174646
  have htrace : WordTrace (prefixWord ++ tailWord_174646) baseStart_174646 baseEnd_174646 := by
    simpa [prefixWord, tailWord_174646, baseEnd_174646] using wordTrace_append hprefix tailTrace_174646
  have hstable : (prefixWord ++ tailWord_174646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174646).length < 2 ^ (prefixWord ++ tailWord_174646).sum := by decide
  have hdescent : baseEnd_174646 < baseStart_174646 := by decide
  rcases family_descends (prefixWord ++ tailWord_174646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174657 : List Nat := [1, 2, 5, 1, 1, 3, 7]
def baseStart_174657 : Nat := 118140960795 + 174657 * 2 ^ 59
def prefixEnd_174657 : Nat := 4983230072969 + 3 ^ 40 * 174657 * 2
def baseEnd_174657 : Nat := 8857579325671939494743

theorem tailTrace_174657 : CollatzResearch.WordTrace tailWord_174657 prefixEnd_174657 8857579325671939494743 := by
  unfold tailWord_174657
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370264128254992885898225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4246842752169995257265483 6370264128254992885898225)
  ·
    refine ⟨4777698096191244664423669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6370264128254992885898225 4777698096191244664423669)
    ·
      refine ⟨447909196517929187289719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4777698096191244664423669 447909196517929187289719)
      ·
        refine ⟨671863794776893780934579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447909196517929187289719 671863794776893780934579)
        ·
          refine ⟨1007795692165340671401869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671863794776893780934579 1007795692165340671401869)
          ·
            refine ⟨377923384562002751775701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1007795692165340671401869 377923384562002751775701)
            ·
              refine ⟨8857579325671939494743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 377923384562002751775701 8857579325671939494743)
              ·
                rfl

theorem cell20_174657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 7].length) (baseStart_174657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174657 prefixEnd_174657 := by exact prefixLift 174657
  have htrace : WordTrace (prefixWord ++ tailWord_174657) baseStart_174657 baseEnd_174657 := by
    simpa [prefixWord, tailWord_174657, baseEnd_174657] using wordTrace_append hprefix tailTrace_174657
  have hstable : (prefixWord ++ tailWord_174657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174657).length < 2 ^ (prefixWord ++ tailWord_174657).sum := by decide
  have hdescent : baseEnd_174657 < baseStart_174657 := by decide
  rcases family_descends (prefixWord ++ tailWord_174657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174671 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_174671 : Nat := 118140960795 + 174671 * 2 ^ 59
def prefixEnd_174671 : Nat := 4983230072969 + 3 ^ 40 * 174671 * 2
def baseEnd_174671 : Nat := 79724603912525628985963

theorem tailTrace_174671 : CollatzResearch.WordTrace tailWord_174671 prefixEnd_174671 79724603912525628985963 := by
  unfold tailWord_174671
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370774750204273276907867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4247183166802848851271911 6370774750204273276907867)
  ·
    refine ⟨9556162125306409915361801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6370774750204273276907867 9556162125306409915361801)
    ·
      refine ⟨7167121593979807436521351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9556162125306409915361801 7167121593979807436521351)
      ·
        refine ⟨10750682390969711154782027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7167121593979807436521351 10750682390969711154782027)
        ·
          refine ⟨16126023586454566732173041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10750682390969711154782027 16126023586454566732173041)
          ·
            refine ⟨12094517689840925049129781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16126023586454566732173041 12094517689840925049129781)
            ·
              refine ⟨1133861033422586723355917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12094517689840925049129781 1133861033422586723355917)
              ·
                refine ⟨425197887533470021258469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1133861033422586723355917 425197887533470021258469)
                ·
                  refine ⟨79724603912525628985963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425197887533470021258469 79724603912525628985963)
                  ·
                    rfl

theorem cell20_174671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_174671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174671 prefixEnd_174671 := by exact prefixLift 174671
  have htrace : WordTrace (prefixWord ++ tailWord_174671) baseStart_174671 baseEnd_174671 := by
    simpa [prefixWord, tailWord_174671, baseEnd_174671] using wordTrace_append hprefix tailTrace_174671
  have hstable : (prefixWord ++ tailWord_174671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174671).length < 2 ^ (prefixWord ++ tailWord_174671).sum := by decide
  have hdescent : baseEnd_174671 < baseStart_174671 := by decide
  rcases family_descends (prefixWord ++ tailWord_174671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174716 : List Nat := [2, 2, 2, 1, 1, 2, 10]
def baseStart_174716 : Nat := 118140960795 + 174716 * 2 ^ 59
def prefixEnd_174716 : Nat := 4983230072969 + 3 ^ 40 * 174716 * 2
def baseEnd_174716 : Nat := 8860571459856163609531

theorem tailTrace_174716 : CollatzResearch.WordTrace tailWord_174716 prefixEnd_174716 8860571459856163609531 := by
  unfold tailWord_174716
  simp only [CollatzResearch.WordTrace]
  refine ⟨3186208017520622981148001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4248277356694163974864001 3186208017520622981148001)
  ·
    refine ⟨2389656013140467235861001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3186208017520622981148001 2389656013140467235861001)
    ·
      refine ⟨1792242009855350426895751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2389656013140467235861001 1792242009855350426895751)
      ·
        refine ⟨2688363014783025640343627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792242009855350426895751 2688363014783025640343627)
        ·
          refine ⟨4032544522174538460515441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688363014783025640343627 4032544522174538460515441)
          ·
            refine ⟨3024408391630903845386581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4032544522174538460515441 3024408391630903845386581)
            ·
              refine ⟨8860571459856163609531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3024408391630903845386581 8860571459856163609531)
              ·
                rfl

theorem cell20_174716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 10].length) (baseStart_174716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174716 prefixEnd_174716 := by exact prefixLift 174716
  have htrace : WordTrace (prefixWord ++ tailWord_174716) baseStart_174716 baseEnd_174716 := by
    simpa [prefixWord, tailWord_174716, baseEnd_174716] using wordTrace_append hprefix tailTrace_174716
  have hstable : (prefixWord ++ tailWord_174716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174716).length < 2 ^ (prefixWord ++ tailWord_174716).sum := by decide
  have hdescent : baseEnd_174716 < baseStart_174716 := by decide
  rcases family_descends (prefixWord ++ tailWord_174716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174781 : List Nat := [1, 4, 1, 2, 1, 4, 1, 4, 2]
def baseStart_174781 : Nat := 118140960795 + 174781 * 2 ^ 59
def prefixEnd_174781 : Nat := 4983230072969 + 3 ^ 40 * 174781 * 2
def baseEnd_174781 : Nat := 79774810909854135318847

theorem tailTrace_174781 : CollatzResearch.WordTrace tailWord_174781 prefixEnd_174781 79774810909854135318847 := by
  unfold tailWord_174781
  simp only [CollatzResearch.WordTrace]
  refine ⟨6374786779805762063412197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4249857853203841375608131 6374786779805762063412197)
  ·
    refine ⟨1195272521213580386889787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6374786779805762063412197 1195272521213580386889787)
    ·
      refine ⟨1792908781820370580334681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195272521213580386889787 1792908781820370580334681)
      ·
        refine ⟨1344681586365277935251011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1792908781820370580334681 1344681586365277935251011)
        ·
          refine ⟨2017022379547916902876517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344681586365277935251011 2017022379547916902876517)
          ·
            refine ⟨378191696165234419289347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2017022379547916902876517 378191696165234419289347)
            ·
              refine ⟨567287544247851628934021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378191696165234419289347 567287544247851628934021)
              ·
                refine ⟨106366414546472180425129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 567287544247851628934021 106366414546472180425129)
                ·
                  refine ⟨79774810909854135318847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106366414546472180425129 79774810909854135318847)
                  ·
                    rfl

theorem cell20_174781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_174781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174781 prefixEnd_174781 := by exact prefixLift 174781
  have htrace : WordTrace (prefixWord ++ tailWord_174781) baseStart_174781 baseEnd_174781 := by
    simpa [prefixWord, tailWord_174781, baseEnd_174781] using wordTrace_append hprefix tailTrace_174781
  have hstable : (prefixWord ++ tailWord_174781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174781).length < 2 ^ (prefixWord ++ tailWord_174781).sum := by decide
  have hdescent : baseEnd_174781 < baseStart_174781 := by decide
  rcases family_descends (prefixWord ++ tailWord_174781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174788 : List Nat := [2, 3, 3, 1, 1, 4, 1, 5]
def baseStart_174788 : Nat := 118140960795 + 174788 * 2 ^ 59
def prefixEnd_174788 : Nat := 4983230072969 + 3 ^ 40 * 174788 * 2
def baseEnd_174788 : Nat := 26592668633531074028495

theorem tailTrace_174788 : CollatzResearch.WordTrace tailWord_174788 prefixEnd_174788 26592668633531074028495 := by
  unfold tailWord_174788
  simp only [CollatzResearch.WordTrace]
  refine ⟨3187521045390201129458509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4250028060520268172611345 3187521045390201129458509)
  ·
    refine ⟨1195320392021325423546941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3187521045390201129458509 1195320392021325423546941)
    ·
      refine ⟨448245147007997033830103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1195320392021325423546941 448245147007997033830103)
      ·
        refine ⟨672367720511995550745155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448245147007997033830103 672367720511995550745155)
        ·
          refine ⟨1008551580767993326117733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672367720511995550745155 1008551580767993326117733)
          ·
            refine ⟨189103421393998748647075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1008551580767993326117733 189103421393998748647075)
            ·
              refine ⟨283655132090998122970613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189103421393998748647075 283655132090998122970613)
              ·
                refine ⟨26592668633531074028495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 283655132090998122970613 26592668633531074028495)
                ·
                  rfl

theorem cell20_174788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_174788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174788 prefixEnd_174788 := by exact prefixLift 174788
  have htrace : WordTrace (prefixWord ++ tailWord_174788) baseStart_174788 baseEnd_174788 := by
    simpa [prefixWord, tailWord_174788, baseEnd_174788] using wordTrace_append hprefix tailTrace_174788
  have hstable : (prefixWord ++ tailWord_174788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174788).length < 2 ^ (prefixWord ++ tailWord_174788).sum := by decide
  have hdescent : baseEnd_174788 < baseStart_174788 := by decide
  rcases family_descends (prefixWord ++ tailWord_174788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174799 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_174799 : Nat := 118140960795 + 174799 * 2 ^ 59
def prefixEnd_174799 : Nat := 4983230072969 + 3 ^ 40 * 174799 * 2
def baseEnd_174799 : Nat := 79783026600326072718773

theorem tailTrace_174799 : CollatzResearch.WordTrace tailWord_174799 prefixEnd_174799 79783026600326072718773 := by
  unfold tailWord_174799
  simp only [CollatzResearch.WordTrace]
  refine ⟨6375443293740551137567451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4250295529160367425044967 6375443293740551137567451)
  ·
    refine ⟨9563164940610826706351177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6375443293740551137567451 9563164940610826706351177)
    ·
      refine ⟨7172373705458120029763383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9563164940610826706351177 7172373705458120029763383)
      ·
        refine ⟨10758560558187180044645075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7172373705458120029763383 10758560558187180044645075)
        ·
          refine ⟨16137840837280770066967613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10758560558187180044645075 16137840837280770066967613)
          ·
            refine ⟨6051690313980288775112855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16137840837280770066967613 6051690313980288775112855)
            ·
              refine ⟨9077535470970433162669283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051690313980288775112855 9077535470970433162669283)
              ·
                refine ⟨13616303206455649744003925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9077535470970433162669283 13616303206455649744003925)
                ·
                  refine ⟨79783026600326072718773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13616303206455649744003925 79783026600326072718773)
                  ·
                    rfl

theorem cell20_174799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_174799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174799 prefixEnd_174799 := by exact prefixLift 174799
  have htrace : WordTrace (prefixWord ++ tailWord_174799) baseStart_174799 baseEnd_174799 := by
    simpa [prefixWord, tailWord_174799, baseEnd_174799] using wordTrace_append hprefix tailTrace_174799
  have hstable : (prefixWord ++ tailWord_174799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174799).length < 2 ^ (prefixWord ++ tailWord_174799).sum := by decide
  have hdescent : baseEnd_174799 < baseStart_174799 := by decide
  rcases family_descends (prefixWord ++ tailWord_174799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174805 : List Nat := [1, 3, 2, 5, 1, 1, 3, 4]
def baseStart_174805 : Nat := 118140960795 + 174805 * 2 ^ 59
def prefixEnd_174805 : Nat := 4983230072969 + 3 ^ 40 * 174805 * 2
def baseEnd_174805 : Nat := 26595255054605572839583

theorem tailTrace_174805 : CollatzResearch.WordTrace tailWord_174805 prefixEnd_174805 26595255054605572839583 := by
  unfold tailWord_174805
  simp only [CollatzResearch.WordTrace]
  refine ⟨6375662131718814162285869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4250441421145876108190579 6375662131718814162285869)
  ·
    refine ⟨2390873299394555310857201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6375662131718814162285869 2390873299394555310857201)
    ·
      refine ⟨1793154974545916483142901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2390873299394555310857201 1793154974545916483142901)
      ·
        refine ⟨168108278863679670294647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1793154974545916483142901 168108278863679670294647)
        ·
          refine ⟨252162418295519505441971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168108278863679670294647 252162418295519505441971)
          ·
            refine ⟨378243627443279258162957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252162418295519505441971 378243627443279258162957)
            ·
              refine ⟨141841360291229721811109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 378243627443279258162957 141841360291229721811109)
              ·
                refine ⟨26595255054605572839583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141841360291229721811109 26595255054605572839583)
                ·
                  rfl

theorem cell20_174805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 4].length) (baseStart_174805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174805 prefixEnd_174805 := by exact prefixLift 174805
  have htrace : WordTrace (prefixWord ++ tailWord_174805) baseStart_174805 baseEnd_174805 := by
    simpa [prefixWord, tailWord_174805, baseEnd_174805] using wordTrace_append hprefix tailTrace_174805
  have hstable : (prefixWord ++ tailWord_174805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174805).length < 2 ^ (prefixWord ++ tailWord_174805).sum := by decide
  have hdescent : baseEnd_174805 < baseStart_174805 := by decide
  rcases family_descends (prefixWord ++ tailWord_174805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174809 : List Nat := [1, 2, 1, 2, 3, 2, 5, 4]
def baseStart_174809 : Nat := 118140960795 + 174809 * 2 ^ 59
def prefixEnd_174809 : Nat := 4983230072969 + 3 ^ 40 * 174809 * 2
def baseEnd_174809 : Nat := 26595863624270160795133

theorem tailTrace_174809 : CollatzResearch.WordTrace tailWord_174809 prefixEnd_174809 26595863624270160795133 := by
  unfold tailWord_174809
  simp only [CollatzResearch.WordTrace]
  refine ⟨6375808023704322845431481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4250538682469548563620987 6375808023704322845431481)
  ·
    refine ⟨4781856017778242134073611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6375808023704322845431481 4781856017778242134073611)
    ·
      refine ⟨7172784026667363201110417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4781856017778242134073611 7172784026667363201110417)
      ·
        refine ⟨5379588020000522400832813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7172784026667363201110417 5379588020000522400832813)
        ·
          refine ⟨2017345507500195900312305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5379588020000522400832813 2017345507500195900312305)
          ·
            refine ⟨1513009130625146925234229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2017345507500195900312305 1513009130625146925234229)
            ·
              refine ⟨141844605996107524240709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1513009130625146925234229 141844605996107524240709)
              ·
                refine ⟨26595863624270160795133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141844605996107524240709 26595863624270160795133)
                ·
                  rfl

theorem cell20_174809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 4].length) (baseStart_174809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174809 prefixEnd_174809 := by exact prefixLift 174809
  have htrace : WordTrace (prefixWord ++ tailWord_174809) baseStart_174809 baseEnd_174809 := by
    simpa [prefixWord, tailWord_174809, baseEnd_174809] using wordTrace_append hprefix tailTrace_174809
  have hstable : (prefixWord ++ tailWord_174809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174809).length < 2 ^ (prefixWord ++ tailWord_174809).sum := by decide
  have hdescent : baseEnd_174809 < baseStart_174809 := by decide
  rcases family_descends (prefixWord ++ tailWord_174809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174819 : List Nat := [1, 1, 1, 7, 1, 1, 1, 5, 2]
def baseStart_174819 : Nat := 118140960795 + 174819 * 2 ^ 59
def prefixEnd_174819 : Nat := 4983230072969 + 3 ^ 40 * 174819 * 2
def baseEnd_174819 : Nat := 79792155145294892052025

theorem tailTrace_174819 : CollatzResearch.WordTrace tailWord_174819 prefixEnd_174819 79792155145294892052025 := by
  unfold tailWord_174819
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376172753668094553295511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4250781835778729702197007 6376172753668094553295511)
  ·
    refine ⟨9564259130502141829943267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6376172753668094553295511 9564259130502141829943267)
    ·
      refine ⟨14346388695753212744914901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9564259130502141829943267 14346388695753212744914901)
      ·
        refine ⟨336243485056715923708943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14346388695753212744914901 336243485056715923708943)
        ·
          refine ⟨504365227585073885563415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336243485056715923708943 504365227585073885563415)
          ·
            refine ⟨756547841377610828345123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504365227585073885563415 756547841377610828345123)
            ·
              refine ⟨1134821762066416242517685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756547841377610828345123 1134821762066416242517685)
              ·
                refine ⟨106389540193726522736033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1134821762066416242517685 106389540193726522736033)
                ·
                  refine ⟨79792155145294892052025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106389540193726522736033 79792155145294892052025)
                  ·
                    rfl

theorem cell20_174819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 2].length) (baseStart_174819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174819 prefixEnd_174819 := by exact prefixLift 174819
  have htrace : WordTrace (prefixWord ++ tailWord_174819) baseStart_174819 baseEnd_174819 := by
    simpa [prefixWord, tailWord_174819, baseEnd_174819] using wordTrace_append hprefix tailTrace_174819
  have hstable : (prefixWord ++ tailWord_174819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174819).length < 2 ^ (prefixWord ++ tailWord_174819).sum := by decide
  have hdescent : baseEnd_174819 < baseStart_174819 := by decide
  rcases family_descends (prefixWord ++ tailWord_174819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174840 : List Nat := [2, 1, 2, 1, 1, 2, 3, 6, 2]
def baseStart_174840 : Nat := 118140960795 + 174840 * 2 ^ 59
def prefixEnd_174840 : Nat := 4983230072969 + 3 ^ 40 * 174840 * 2
def baseEnd_174840 : Nat := 79801740117512152351939

theorem tailTrace_174840 : CollatzResearch.WordTrace tailWord_174840 prefixEnd_174840 79801740117512152351939 := by
  unfold tailWord_174840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3188469343296007569904987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4251292457728010093206649 3188469343296007569904987)
  ·
    refine ⟨4782704014944011354857481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3188469343296007569904987 4782704014944011354857481)
    ·
      refine ⟨3587028011208008516143111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4782704014944011354857481 3587028011208008516143111)
      ·
        refine ⟨5380542016812012774214667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3587028011208008516143111 5380542016812012774214667)
        ·
          refine ⟨8070813025218019161322001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5380542016812012774214667 8070813025218019161322001)
          ·
            refine ⟨6053109768913514370991501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8070813025218019161322001 6053109768913514370991501)
            ·
              refine ⟨2269916163342567889121813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6053109768913514370991501 2269916163342567889121813)
              ·
                refine ⟨106402320156682869802585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2269916163342567889121813 106402320156682869802585)
                ·
                  refine ⟨79801740117512152351939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106402320156682869802585 79801740117512152351939)
                  ·
                    rfl

theorem cell20_174840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_174840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174840 prefixEnd_174840 := by exact prefixLift 174840
  have htrace : WordTrace (prefixWord ++ tailWord_174840) baseStart_174840 baseEnd_174840 := by
    simpa [prefixWord, tailWord_174840, baseEnd_174840] using wordTrace_append hprefix tailTrace_174840
  have hstable : (prefixWord ++ tailWord_174840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174840).length < 2 ^ (prefixWord ++ tailWord_174840).sum := by decide
  have hdescent : baseEnd_174840 < baseStart_174840 := by decide
  rcases family_descends (prefixWord ++ tailWord_174840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174892 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 3]
def baseStart_174892 : Nat := 118140960795 + 174892 * 2 ^ 59
def prefixEnd_174892 : Nat := 4983230072969 + 3 ^ 40 * 174892 * 2
def baseEnd_174892 : Nat := 79825474334431082618393

theorem tailTrace_174892 : CollatzResearch.WordTrace tailWord_174892 prefixEnd_174892 79825474334431082618393 := by
  unfold tailWord_174892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189417641201814010351465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4252556854935752013801953 3189417641201814010351465)
  ·
    refine ⟨2392063230901360507763599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3189417641201814010351465 2392063230901360507763599)
    ·
      refine ⟨3588094846352040761645399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2392063230901360507763599 3588094846352040761645399)
      ·
        refine ⟨5382142269528061142468099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3588094846352040761645399 5382142269528061142468099)
        ·
          refine ⟨8073213404292091713702149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5382142269528061142468099 8073213404292091713702149)
          ·
            refine ⟨1513727513304767196319153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8073213404292091713702149 1513727513304767196319153)
            ·
              refine ⟨1135295634978575397239365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1513727513304767196319153 1135295634978575397239365)
              ·
                refine ⟨212867931558482886982381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1135295634978575397239365 212867931558482886982381)
                ·
                  refine ⟨79825474334431082618393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212867931558482886982381 79825474334431082618393)
                  ·
                    rfl

theorem cell20_174892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_174892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174892 prefixEnd_174892 := by exact prefixLift 174892
  have htrace : WordTrace (prefixWord ++ tailWord_174892) baseStart_174892 baseEnd_174892 := by
    simpa [prefixWord, tailWord_174892, baseEnd_174892] using wordTrace_append hprefix tailTrace_174892
  have hstable : (prefixWord ++ tailWord_174892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174892).length < 2 ^ (prefixWord ++ tailWord_174892).sum := by decide
  have hdescent : baseEnd_174892 < baseStart_174892 := by decide
  rcases family_descends (prefixWord ++ tailWord_174892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174946 : List Nat := [3, 3, 2, 1, 4, 1, 2, 2, 2]
def baseStart_174946 : Nat := 118140960795 + 174946 * 2 ^ 59
def prefixEnd_174946 : Nat := 4983230072969 + 3 ^ 40 * 174946 * 2
def baseEnd_174946 : Nat := 79850121405846894818173

theorem tailTrace_174946 : CollatzResearch.WordTrace tailWord_174946 prefixEnd_174946 79850121405846894818173 := by
  unfold tailWord_174946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595201206051998810792173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4253869882805330162112461 1595201206051998810792173)
  ·
    refine ⟨598200452269499554047065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1595201206051998810792173 598200452269499554047065)
    ·
      refine ⟨448650339202124665535299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 598200452269499554047065 448650339202124665535299)
      ·
        refine ⟨672975508803186998302949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448650339202124665535299 672975508803186998302949)
        ·
          refine ⟨126182907900597562181803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 672975508803186998302949 126182907900597562181803)
          ·
            refine ⟨189274361850896343272705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126182907900597562181803 189274361850896343272705)
            ·
              refine ⟨141955771388172257454529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189274361850896343272705 141955771388172257454529)
              ·
                refine ⟨106466828541129193090897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141955771388172257454529 106466828541129193090897)
                ·
                  refine ⟨79850121405846894818173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106466828541129193090897 79850121405846894818173)
                  ·
                    rfl

theorem cell20_174946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_174946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174946 prefixEnd_174946 := by exact prefixLift 174946
  have htrace : WordTrace (prefixWord ++ tailWord_174946) baseStart_174946 baseEnd_174946 := by
    simpa [prefixWord, tailWord_174946, baseEnd_174946] using wordTrace_append hprefix tailTrace_174946
  have hstable : (prefixWord ++ tailWord_174946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174946).length < 2 ^ (prefixWord ++ tailWord_174946).sum := by decide
  have hdescent : baseEnd_174946 < baseStart_174946 := by decide
  rcases family_descends (prefixWord ++ tailWord_174946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174947 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 3]
def baseStart_174947 : Nat := 118140960795 + 174947 * 2 ^ 59
def prefixEnd_174947 : Nat := 4983230072969 + 3 ^ 40 * 174947 * 2
def baseEnd_174947 : Nat := 79850577833095335784835

theorem tailTrace_174947 : CollatzResearch.WordTrace tailWord_174947 prefixEnd_174947 79850577833095335784835 := by
  unfold tailWord_174947
  simp only [CollatzResearch.WordTrace]
  refine ⟨6380841297204372413955095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4253894198136248275970063 6380841297204372413955095)
  ·
    refine ⟨9571261945806558620932643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6380841297204372413955095 9571261945806558620932643)
    ·
      refine ⟨14356892918709837931398965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9571261945806558620932643 14356892918709837931398965)
      ·
        refine ⟨1345958711129047306068653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14356892918709837931398965 1345958711129047306068653)
        ·
          refine ⟨504734516673392739775745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1345958711129047306068653 504734516673392739775745)
          ·
            refine ⟨378550887505044554831809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504734516673392739775745 378550887505044554831809)
            ·
              refine ⟨283913165628783416123857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378550887505044554831809 283913165628783416123857)
              ·
                refine ⟨212934874221587562092893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283913165628783416123857 212934874221587562092893)
                ·
                  refine ⟨79850577833095335784835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212934874221587562092893 79850577833095335784835)
                  ·
                    rfl

theorem cell20_174947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 3].length) (baseStart_174947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174947 prefixEnd_174947 := by exact prefixLift 174947
  have htrace : WordTrace (prefixWord ++ tailWord_174947) baseStart_174947 baseEnd_174947 := by
    simpa [prefixWord, tailWord_174947, baseEnd_174947] using wordTrace_append hprefix tailTrace_174947
  have hstable : (prefixWord ++ tailWord_174947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174947).length < 2 ^ (prefixWord ++ tailWord_174947).sum := by decide
  have hdescent : baseEnd_174947 < baseStart_174947 := by decide
  rcases family_descends (prefixWord ++ tailWord_174947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174961 : List Nat := [1, 2, 2, 2, 1, 6, 1, 5]
def baseStart_174961 : Nat := 118140960795 + 174961 * 2 ^ 59
def prefixEnd_174961 : Nat := 4983230072969 + 3 ^ 40 * 174961 * 2
def baseEnd_174961 : Nat := 26618989271524503106037

theorem tailTrace_174961 : CollatzResearch.WordTrace tailWord_174961 prefixEnd_174961 26618989271524503106037 := by
  unfold tailWord_174961
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381351919153652804964737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4254234612769101869976491 6381351919153652804964737)
  ·
    refine ⟨4786013939365239603723553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6381351919153652804964737 4786013939365239603723553)
    ·
      refine ⟨3589510454523929702792665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4786013939365239603723553 3589510454523929702792665)
      ·
        refine ⟨2692132840892947277094499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3589510454523929702792665 2692132840892947277094499)
        ·
          refine ⟨4038199261339420915641749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692132840892947277094499 4038199261339420915641749)
          ·
            refine ⟨189290590375285355420707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4038199261339420915641749 189290590375285355420707)
            ·
              refine ⟨283935885562928033131061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189290590375285355420707 283935885562928033131061)
              ·
                refine ⟨26618989271524503106037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 283935885562928033131061 26618989271524503106037)
                ·
                  rfl

theorem cell20_174961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 5].length) (baseStart_174961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174961 prefixEnd_174961 := by exact prefixLift 174961
  have htrace : WordTrace (prefixWord ++ tailWord_174961) baseStart_174961 baseEnd_174961 := by
    simpa [prefixWord, tailWord_174961, baseEnd_174961] using wordTrace_append hprefix tailTrace_174961
  have hstable : (prefixWord ++ tailWord_174961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174961).length < 2 ^ (prefixWord ++ tailWord_174961).sum := by decide
  have hdescent : baseEnd_174961 < baseStart_174961 := by decide
  rcases family_descends (prefixWord ++ tailWord_174961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174998 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_174998 : Nat := 118140960795 + 174998 * 2 ^ 59
def prefixEnd_174998 : Nat := 4983230072969 + 3 ^ 40 * 174998 * 2
def baseEnd_174998 : Nat := 79873855622765825084627

theorem tailTrace_174998 : CollatzResearch.WordTrace tailWord_174998 prefixEnd_174998 79873855622765825084627 := by
  unfold tailWord_174998
  simp only [CollatzResearch.WordTrace]
  refine ⟨398918838751225507753853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4255134280013072082707765 398918838751225507753853)
  ·
    refine ⟨149594564531709565407695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 398918838751225507753853 149594564531709565407695)
    ·
      refine ⟨224391846797564348111543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149594564531709565407695 224391846797564348111543)
      ·
        refine ⟨336587770196346522167315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224391846797564348111543 336587770196346522167315)
        ·
          refine ⟨504881655294519783250973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336587770196346522167315 504881655294519783250973)
          ·
            refine ⟨189330620735444918719115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 504881655294519783250973 189330620735444918719115)
            ·
              refine ⟨283995931103167378078673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189330620735444918719115 283995931103167378078673)
              ·
                refine ⟨212996948327375533559005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283995931103167378078673 212996948327375533559005)
                ·
                  refine ⟨79873855622765825084627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212996948327375533559005 79873855622765825084627)
                  ·
                    rfl

theorem cell20_174998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_174998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_174998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_174998 prefixEnd_174998 := by exact prefixLift 174998
  have htrace : WordTrace (prefixWord ++ tailWord_174998) baseStart_174998 baseEnd_174998 := by
    simpa [prefixWord, tailWord_174998, baseEnd_174998] using wordTrace_append hprefix tailTrace_174998
  have hstable : (prefixWord ++ tailWord_174998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174998).length < 2 ^ (prefixWord ++ tailWord_174998).sum := by decide
  have hdescent : baseEnd_174998 < baseStart_174998 := by decide
  rcases family_descends (prefixWord ++ tailWord_174998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175002 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_175002 : Nat := 118140960795 + 175002 * 2 ^ 59
def prefixEnd_175002 : Nat := 4983230072969 + 3 ^ 40 * 175002 * 2
def baseEnd_175002 : Nat := 79875681331759588951277

theorem tailTrace_175002 : CollatzResearch.WordTrace tailWord_175002 prefixEnd_175002 79875681331759588951277 := by
  unfold tailWord_175002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595711828001279201801815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4255231541336744538138173 1595711828001279201801815)
  ·
    refine ⟨2393567742001918802702723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1595711828001279201801815 2393567742001918802702723)
    ·
      refine ⟨3590351613002878204054085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2393567742001918802702723 3590351613002878204054085)
      ·
        refine ⟨673190927438039663260141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3590351613002878204054085 673190927438039663260141)
        ·
          refine ⟨252446597789264873722553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 673190927438039663260141 252446597789264873722553)
          ·
            refine ⟨189334948341948655291915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252446597789264873722553 189334948341948655291915)
            ·
              refine ⟨284002422512922982937873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189334948341948655291915 284002422512922982937873)
              ·
                refine ⟨213001816884692237203405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284002422512922982937873 213001816884692237203405)
                ·
                  refine ⟨79875681331759588951277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213001816884692237203405 79875681331759588951277)
                  ·
                    rfl

theorem cell20_175002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_175002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175002 prefixEnd_175002 := by exact prefixLift 175002
  have htrace : WordTrace (prefixWord ++ tailWord_175002) baseStart_175002 baseEnd_175002 := by
    simpa [prefixWord, tailWord_175002, baseEnd_175002] using wordTrace_append hprefix tailTrace_175002
  have hstable : (prefixWord ++ tailWord_175002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175002).length < 2 ^ (prefixWord ++ tailWord_175002).sum := by decide
  have hdescent : baseEnd_175002 < baseStart_175002 := by decide
  rcases family_descends (prefixWord ++ tailWord_175002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175009 : List Nat := [1, 2, 3, 4, 1, 1, 2, 4, 2]
def baseStart_175009 : Nat := 118140960795 + 175009 * 2 ^ 59
def prefixEnd_175009 : Nat := 4983230072969 + 3 ^ 40 * 175009 * 2
def baseEnd_175009 : Nat := 79878876322498675717915

theorem tailTrace_175009 : CollatzResearch.WordTrace tailWord_175009 prefixEnd_175009 79878876322498675717915 := by
  unfold tailWord_175009
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383102622979757002712081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4255401748653171335141387 6383102622979757002712081)
  ·
    refine ⟨4787326967234817752034061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6383102622979757002712081 4787326967234817752034061)
    ·
      refine ⟨1795247612713056657012773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4787326967234817752034061 1795247612713056657012773)
      ·
        refine ⟨336608927383698123189895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1795247612713056657012773 336608927383698123189895)
        ·
          refine ⟨504913391075547184784843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336608927383698123189895 504913391075547184784843)
          ·
            refine ⟨757370086613320777177265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504913391075547184784843 757370086613320777177265)
            ·
              refine ⟨568027564959990582882949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757370086613320777177265 568027564959990582882949)
              ·
                refine ⟨106505168429998234290553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 568027564959990582882949 106505168429998234290553)
                ·
                  refine ⟨79878876322498675717915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106505168429998234290553 79878876322498675717915)
                  ·
                    rfl

theorem cell20_175009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_175009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175009 prefixEnd_175009 := by exact prefixLift 175009
  have htrace : WordTrace (prefixWord ++ tailWord_175009) baseStart_175009 baseEnd_175009 := by
    simpa [prefixWord, tailWord_175009, baseEnd_175009] using wordTrace_append hprefix tailTrace_175009
  have hstable : (prefixWord ++ tailWord_175009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175009).length < 2 ^ (prefixWord ++ tailWord_175009).sum := by decide
  have hdescent : baseEnd_175009 < baseStart_175009 := by decide
  rcases family_descends (prefixWord ++ tailWord_175009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175037 : List Nat := [1, 4, 1, 2, 4, 1, 1, 6]
def baseStart_175037 : Nat := 118140960795 + 175037 * 2 ^ 59
def prefixEnd_175037 : Nat := 4983230072969 + 3 ^ 40 * 175037 * 2
def baseEnd_175037 : Nat := 26630552095151674261489

theorem tailTrace_175037 : CollatzResearch.WordTrace tailWord_175037 prefixEnd_175037 26630552095151674261489 := by
  unfold tailWord_175037
  simp only [CollatzResearch.WordTrace]
  refine ⟨6384123866878317784731365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4256082577918878523154243 6384123866878317784731365)
  ·
    refine ⟨1197023225039684584637131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6384123866878317784731365 1197023225039684584637131)
    ·
      refine ⟨1795534837559526876955697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197023225039684584637131 1795534837559526876955697)
      ·
        refine ⟨1346651128169645157716773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1795534837559526876955697 1346651128169645157716773)
        ·
          refine ⟨252497086531808467071895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1346651128169645157716773 252497086531808467071895)
          ·
            refine ⟨378745629797712700607843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252497086531808467071895 378745629797712700607843)
            ·
              refine ⟨568118444696569050911765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378745629797712700607843 568118444696569050911765)
              ·
                refine ⟨26630552095151674261489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 568118444696569050911765 26630552095151674261489)
                ·
                  rfl

theorem cell20_175037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 6].length) (baseStart_175037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175037 prefixEnd_175037 := by exact prefixLift 175037
  have htrace : WordTrace (prefixWord ++ tailWord_175037) baseStart_175037 baseEnd_175037 := by
    simpa [prefixWord, tailWord_175037, baseEnd_175037] using wordTrace_append hprefix tailTrace_175037
  have hstable : (prefixWord ++ tailWord_175037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175037).length < 2 ^ (prefixWord ++ tailWord_175037).sum := by decide
  have hdescent : baseEnd_175037 < baseStart_175037 := by decide
  rcases family_descends (prefixWord ++ tailWord_175037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175161 : List Nat := [1, 2, 1, 5, 2, 2, 2, 3, 2]
def baseStart_175161 : Nat := 118140960795 + 175161 * 2 ^ 59
def prefixEnd_175161 : Nat := 4983230072969 + 3 ^ 40 * 175161 * 2
def baseEnd_175161 : Nat := 79948253264261702650627

theorem tailTrace_175161 : CollatzResearch.WordTrace tailWord_175161 prefixEnd_175161 79948253264261702650627 := by
  unfold tailWord_175161
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388646518429086962245337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4259097678952724641496891 6388646518429086962245337)
  ·
    refine ⟨4791484888821815221684003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6388646518429086962245337 4791484888821815221684003)
    ·
      refine ⟨7187227333232722832526005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4791484888821815221684003 7187227333232722832526005)
      ·
        refine ⟨673802562490567765549313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7187227333232722832526005 673802562490567765549313)
        ·
          refine ⟨505351921867925824161985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673802562490567765549313 505351921867925824161985)
          ·
            refine ⟨379013941400944368121489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505351921867925824161985 379013941400944368121489)
            ·
              refine ⟨284260456050708276091117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379013941400944368121489 284260456050708276091117)
              ·
                refine ⟨106597671019015603534169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284260456050708276091117 106597671019015603534169)
                ·
                  refine ⟨79948253264261702650627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106597671019015603534169 79948253264261702650627)
                  ·
                    rfl

theorem cell20_175161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_175161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175161 prefixEnd_175161 := by exact prefixLift 175161
  have htrace : WordTrace (prefixWord ++ tailWord_175161) baseStart_175161 baseEnd_175161 := by
    simpa [prefixWord, tailWord_175161, baseEnd_175161] using wordTrace_append hprefix tailTrace_175161
  have hstable : (prefixWord ++ tailWord_175161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175161).length < 2 ^ (prefixWord ++ tailWord_175161).sum := by decide
  have hdescent : baseEnd_175161 < baseStart_175161 := by decide
  rcases family_descends (prefixWord ++ tailWord_175161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175175 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 3]
def baseStart_175175 : Nat := 118140960795 + 175175 * 2 ^ 59
def prefixEnd_175175 : Nat := 4983230072969 + 3 ^ 40 * 175175 * 2
def baseEnd_175175 : Nat := 79954643245739876183903

theorem tailTrace_175175 : CollatzResearch.WordTrace tailWord_175175 prefixEnd_175175 79954643245739876183903 := by
  unfold tailWord_175175
  simp only [CollatzResearch.WordTrace]
  refine ⟨6389157140378367353254979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4259438093585578235503319 6389157140378367353254979)
  ·
    refine ⟨9583735710567551029882469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6389157140378367353254979 9583735710567551029882469)
    ·
      refine ⟨1796950445731415818102963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9583735710567551029882469 1796950445731415818102963)
      ·
        refine ⟨2695425668597123727154445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796950445731415818102963 2695425668597123727154445)
        ·
          refine ⟨1010784625723921397682917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2695425668597123727154445 1010784625723921397682917)
          ·
            refine ⟨189522117323235262065547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1010784625723921397682917 189522117323235262065547)
            ·
              refine ⟨284283175984852893098321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189522117323235262065547 284283175984852893098321)
              ·
                refine ⟨213212381988639669823741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284283175984852893098321 213212381988639669823741)
                ·
                  refine ⟨79954643245739876183903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213212381988639669823741 79954643245739876183903)
                  ·
                    rfl

theorem cell20_175175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 3].length) (baseStart_175175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175175 prefixEnd_175175 := by exact prefixLift 175175
  have htrace : WordTrace (prefixWord ++ tailWord_175175) baseStart_175175 baseEnd_175175 := by
    simpa [prefixWord, tailWord_175175, baseEnd_175175] using wordTrace_append hprefix tailTrace_175175
  have hstable : (prefixWord ++ tailWord_175175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175175).length < 2 ^ (prefixWord ++ tailWord_175175).sum := by decide
  have hdescent : baseEnd_175175 < baseStart_175175 := by decide
  rcases family_descends (prefixWord ++ tailWord_175175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175182 : List Nat := [4, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_175182 : Nat := 118140960795 + 175182 * 2 ^ 59
def prefixEnd_175182 : Nat := 4983230072969 + 3 ^ 40 * 175182 * 2
def baseEnd_175182 : Nat := 79957838236478962950541

theorem tailTrace_175182 : CollatzResearch.WordTrace tailWord_175182 prefixEnd_175182 79957838236478962950541 := by
  unfold tailWord_175182
  simp only [CollatzResearch.WordTrace]
  refine ⟨798676556419125943594975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4259608300902005032506533 798676556419125943594975)
  ·
    refine ⟨1198014834628688915392463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 798676556419125943594975 1198014834628688915392463)
    ·
      refine ⟨1797022251943033373088695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198014834628688915392463 1797022251943033373088695)
      ·
        refine ⟨2695533377914550059633043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797022251943033373088695 2695533377914550059633043)
        ·
          refine ⟨4043300066871825089449565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695533377914550059633043 4043300066871825089449565)
          ·
            refine ⟨1516237525076934408543587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4043300066871825089449565 1516237525076934408543587)
            ·
              refine ⟨2274356287615401612815381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516237525076934408543587 2274356287615401612815381)
              ·
                refine ⟨106610450981971950600721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2274356287615401612815381 106610450981971950600721)
                ·
                  refine ⟨79957838236478962950541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106610450981971950600721 79957838236478962950541)
                  ·
                    rfl

theorem cell20_175182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_175182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175182 prefixEnd_175182 := by exact prefixLift 175182
  have htrace : WordTrace (prefixWord ++ tailWord_175182) baseStart_175182 baseEnd_175182 := by
    simpa [prefixWord, tailWord_175182, baseEnd_175182] using wordTrace_append hprefix tailTrace_175182
  have hstable : (prefixWord ++ tailWord_175182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175182).length < 2 ^ (prefixWord ++ tailWord_175182).sum := by decide
  have hdescent : baseEnd_175182 < baseStart_175182 := by decide
  rcases family_descends (prefixWord ++ tailWord_175182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175224 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_175224 : Nat := 118140960795 + 175224 * 2 ^ 59
def prefixEnd_175224 : Nat := 4983230072969 + 3 ^ 40 * 175224 * 2
def baseEnd_175224 : Nat := 79977008180913483550369

theorem tailTrace_175224 : CollatzResearch.WordTrace tailWord_175224 prefixEnd_175224 79977008180913483550369 := by
  unfold tailWord_175224
  simp only [CollatzResearch.WordTrace]
  refine ⟨3195472158600424360894363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4260629544800565814525817 3195472158600424360894363)
  ·
    refine ⟨4793208237900636541341545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3195472158600424360894363 4793208237900636541341545)
    ·
      refine ⟨3594906178425477406006159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4793208237900636541341545 3594906178425477406006159)
      ·
        refine ⟨5392359267638216109009239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594906178425477406006159 5392359267638216109009239)
        ·
          refine ⟨8088538901457324163513859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5392359267638216109009239 8088538901457324163513859)
          ·
            refine ⟨12132808352185986245270789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8088538901457324163513859 12132808352185986245270789)
            ·
              refine ⟨2274901566034872420988273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12132808352185986245270789 2274901566034872420988273)
              ·
                refine ⟨1706176174526154315741205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2274901566034872420988273 1706176174526154315741205)
                ·
                  refine ⟨79977008180913483550369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1706176174526154315741205 79977008180913483550369)
                  ·
                    rfl

theorem cell20_175224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_175224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175224 prefixEnd_175224 := by exact prefixLift 175224
  have htrace : WordTrace (prefixWord ++ tailWord_175224) baseStart_175224 baseEnd_175224 := by
    simpa [prefixWord, tailWord_175224, baseEnd_175224] using wordTrace_append hprefix tailTrace_175224
  have hstable : (prefixWord ++ tailWord_175224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175224).length < 2 ^ (prefixWord ++ tailWord_175224).sum := by decide
  have hdescent : baseEnd_175224 < baseStart_175224 := by decide
  rcases family_descends (prefixWord ++ tailWord_175224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175237 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 4]
def baseStart_175237 : Nat := 118140960795 + 175237 * 2 ^ 59
def prefixEnd_175237 : Nat := 4983230072969 + 3 ^ 40 * 175237 * 2
def baseEnd_175237 : Nat := 79982941735143216116983

theorem tailTrace_175237 : CollatzResearch.WordTrace tailWord_175237 prefixEnd_175237 79982941735143216116983 := by
  unfold tailWord_175237
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391418466153751942011965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4260945644102501294674643 6391418466153751942011965)
  ·
    refine ⟨2396781924807656978254487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6391418466153751942011965 2396781924807656978254487)
    ·
      refine ⟨3595172887211485467381731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2396781924807656978254487 3595172887211485467381731)
      ·
        refine ⟨5392759330817228201072597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3595172887211485467381731 5392759330817228201072597)
        ·
          refine ⟨126392796816028785962639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 5392759330817228201072597 126392796816028785962639)
          ·
            refine ⟨189589195224043178943959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126392796816028785962639 189589195224043178943959)
            ·
              refine ⟨284383792836064768415939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189589195224043178943959 284383792836064768415939)
              ·
                refine ⟨426575689254097152623909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284383792836064768415939 426575689254097152623909)
                ·
                  refine ⟨79982941735143216116983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426575689254097152623909 79982941735143216116983)
                  ·
                    rfl

theorem cell20_175237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_175237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175237 prefixEnd_175237 := by exact prefixLift 175237
  have htrace : WordTrace (prefixWord ++ tailWord_175237) baseStart_175237 baseEnd_175237 := by
    simpa [prefixWord, tailWord_175237, baseEnd_175237] using wordTrace_append hprefix tailTrace_175237
  have hstable : (prefixWord ++ tailWord_175237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175237).length < 2 ^ (prefixWord ++ tailWord_175237).sum := by decide
  have hdescent : baseEnd_175237 < baseStart_175237 := by decide
  rcases family_descends (prefixWord ++ tailWord_175237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175241 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 4]
def baseStart_175241 : Nat := 118140960795 + 175241 * 2 ^ 59
def prefixEnd_175241 : Nat := 4983230072969 + 3 ^ 40 * 175241 * 2
def baseEnd_175241 : Nat := 79984767444136979983633

theorem tailTrace_175241 : CollatzResearch.WordTrace tailWord_175241 prefixEnd_175241 79984767444136979983633 := by
  unfold tailWord_175241
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391564358139260625157577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4261042905426173750105051 6391564358139260625157577)
  ·
    refine ⟨4793673268604445468868183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6391564358139260625157577 4793673268604445468868183)
    ·
      refine ⟨7190509902906668203302275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4793673268604445468868183 7190509902906668203302275)
      ·
        refine ⟨10785764854360002304953413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190509902906668203302275 10785764854360002304953413)
        ·
          refine ⟨2022330910192500432178765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10785764854360002304953413 2022330910192500432178765)
          ·
            refine ⟨758374091322187662067037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2022330910192500432178765 758374091322187662067037)
            ·
              refine ⟨284390284245820373275139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 758374091322187662067037 284390284245820373275139)
              ·
                refine ⟨426585426368730559912709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284390284245820373275139 426585426368730559912709)
                ·
                  refine ⟨79984767444136979983633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426585426368730559912709 79984767444136979983633)
                  ·
                    rfl

theorem cell20_175241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_175241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175241 prefixEnd_175241 := by exact prefixLift 175241
  have htrace : WordTrace (prefixWord ++ tailWord_175241) baseStart_175241 baseEnd_175241 := by
    simpa [prefixWord, tailWord_175241, baseEnd_175241] using wordTrace_append hprefix tailTrace_175241
  have hstable : (prefixWord ++ tailWord_175241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175241).length < 2 ^ (prefixWord ++ tailWord_175241).sum := by decide
  have hdescent : baseEnd_175241 < baseStart_175241 := by decide
  rcases family_descends (prefixWord ++ tailWord_175241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175292 : List Nat := [2, 2, 2, 3, 2, 3, 2, 2, 2]
def baseStart_175292 : Nat := 118140960795 + 175292 * 2 ^ 59
def prefixEnd_175292 : Nat := 4983230072969 + 3 ^ 40 * 175292 * 2
def baseEnd_175292 : Nat := 80008045233807469283425

theorem tailTrace_175292 : CollatzResearch.WordTrace tailWord_175292 prefixEnd_175292 80008045233807469283425 := by
  unfold tailWord_175292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196712240477248167632065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4262282987302997556842753 3196712240477248167632065)
  ·
    refine ⟨2397534180357936125724049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3196712240477248167632065 2397534180357936125724049)
    ·
      refine ⟨1798150635268452094293037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2397534180357936125724049 1798150635268452094293037)
      ·
        refine ⟨674306488225669535359889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1798150635268452094293037 674306488225669535359889)
        ·
          refine ⟨505729866169252151519917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674306488225669535359889 505729866169252151519917)
          ·
            refine ⟨189648699813469556819969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 505729866169252151519917 189648699813469556819969)
            ·
              refine ⟨142236524860102167614977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189648699813469556819969 142236524860102167614977)
              ·
                refine ⟨106677393645076625711233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142236524860102167614977 106677393645076625711233)
                ·
                  refine ⟨80008045233807469283425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106677393645076625711233 80008045233807469283425)
                  ·
                    rfl

theorem cell20_175292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_175292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175292 prefixEnd_175292 := by exact prefixLift 175292
  have htrace : WordTrace (prefixWord ++ tailWord_175292) baseStart_175292 baseEnd_175292 := by
    simpa [prefixWord, tailWord_175292, baseEnd_175292] using wordTrace_append hprefix tailTrace_175292
  have hstable : (prefixWord ++ tailWord_175292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175292).length < 2 ^ (prefixWord ++ tailWord_175292).sum := by decide
  have hdescent : baseEnd_175292 < baseStart_175292 := by decide
  rcases family_descends (prefixWord ++ tailWord_175292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175293 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_175293 : Nat := 118140960795 + 175293 * 2 ^ 59
def prefixEnd_175293 : Nat := 4983230072969 + 3 ^ 40 * 175293 * 2
def baseEnd_175293 : Nat := 80008501661055910250087

theorem tailTrace_175293 : CollatzResearch.WordTrace tailWord_175293 prefixEnd_175293 80008501661055910250087 := by
  unfold tailWord_175293
  simp only [CollatzResearch.WordTrace]
  refine ⟨6393460953950873506050533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4262307302633915670700355 6393460953950873506050533)
  ·
    refine ⟨1198773928865788782384475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6393460953950873506050533 1198773928865788782384475)
    ·
      refine ⟨1798160893298683173576713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198773928865788782384475 1798160893298683173576713)
      ·
        refine ⟨1348620669974012380182535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1798160893298683173576713 1348620669974012380182535)
        ·
          refine ⟨2022931004961018570273803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348620669974012380182535 2022931004961018570273803)
          ·
            refine ⟨3034396507441527855410705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022931004961018570273803 3034396507441527855410705)
            ·
              refine ⟨2275797380581145891558029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3034396507441527855410705 2275797380581145891558029)
              ·
                refine ⟨853424017717929709334261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2275797380581145891558029 853424017717929709334261)
                ·
                  refine ⟨80008501661055910250087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 853424017717929709334261 80008501661055910250087)
                  ·
                    rfl

theorem cell20_175293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_175293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175293 prefixEnd_175293 := by exact prefixLift 175293
  have htrace : WordTrace (prefixWord ++ tailWord_175293) baseStart_175293 baseEnd_175293 := by
    simpa [prefixWord, tailWord_175293, baseEnd_175293] using wordTrace_append hprefix tailTrace_175293
  have hstable : (prefixWord ++ tailWord_175293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175293).length < 2 ^ (prefixWord ++ tailWord_175293).sum := by decide
  have hdescent : baseEnd_175293 < baseStart_175293 := by decide
  rcases family_descends (prefixWord ++ tailWord_175293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175307 : List Nat := [1, 1, 1, 1, 3, 2, 2, 9]
def baseStart_175307 : Nat := 118140960795 + 175307 * 2 ^ 59
def prefixEnd_175307 : Nat := 4983230072969 + 3 ^ 40 * 175307 * 2
def baseEnd_175307 : Nat := 26671630547511361261121

theorem tailTrace_175307 : CollatzResearch.WordTrace tailWord_175307 prefixEnd_175307 26671630547511361261121 := by
  unfold tailWord_175307
  simp only [CollatzResearch.WordTrace]
  refine ⟨6393971575900153897060175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4262647717266769264706783 6393971575900153897060175)
  ·
    refine ⟨9590957363850230845590263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6393971575900153897060175 9590957363850230845590263)
    ·
      refine ⟨14386436045775346268385395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9590957363850230845590263 14386436045775346268385395)
      ·
        refine ⟨21579654068663019402578093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14386436045775346268385395 21579654068663019402578093)
        ·
          refine ⟨8092370275748632275966785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21579654068663019402578093 8092370275748632275966785)
          ·
            refine ⟨6069277706811474206975089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8092370275748632275966785 6069277706811474206975089)
            ·
              refine ⟨4551958280108605655231317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6069277706811474206975089 4551958280108605655231317)
              ·
                refine ⟨26671630547511361261121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4551958280108605655231317 26671630547511361261121)
                ·
                  rfl

theorem cell20_175307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_175307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175307 prefixEnd_175307 := by exact prefixLift 175307
  have htrace : WordTrace (prefixWord ++ tailWord_175307) baseStart_175307 baseEnd_175307 := by
    simpa [prefixWord, tailWord_175307, baseEnd_175307] using wordTrace_append hprefix tailTrace_175307
  have hstable : (prefixWord ++ tailWord_175307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175307).length < 2 ^ (prefixWord ++ tailWord_175307).sum := by decide
  have hdescent : baseEnd_175307 < baseStart_175307 := by decide
  rcases family_descends (prefixWord ++ tailWord_175307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175317 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 6]
def baseStart_175317 : Nat := 118140960795 + 175317 * 2 ^ 59
def prefixEnd_175317 : Nat := 4983230072969 + 3 ^ 40 * 175317 * 2
def baseEnd_175317 : Nat := 80019455915018493449989

theorem tailTrace_175317 : CollatzResearch.WordTrace tailWord_175317 prefixEnd_175317 80019455915018493449989 := by
  unfold tailWord_175317
  simp only [CollatzResearch.WordTrace]
  refine ⟨6394336305863925604924205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4262890870575950403282803 6394336305863925604924205)
  ·
    refine ⟨2397876114698972101846577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6394336305863925604924205 2397876114698972101846577)
    ·
      refine ⟨1798407086024229076384933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2397876114698972101846577 1798407086024229076384933)
      ·
        refine ⟨337201328629542951822175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1798407086024229076384933 337201328629542951822175)
        ·
          refine ⟨505801992944314427733263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337201328629542951822175 505801992944314427733263)
          ·
            refine ⟨758702989416471641599895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505801992944314427733263 758702989416471641599895)
            ·
              refine ⟨1138054484124707462399843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758702989416471641599895 1138054484124707462399843)
              ·
                refine ⟨1707081726187061193599765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138054484124707462399843 1707081726187061193599765)
                ·
                  refine ⟨80019455915018493449989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1707081726187061193599765 80019455915018493449989)
                  ·
                    rfl

theorem cell20_175317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_175317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175317 prefixEnd_175317 := by exact prefixLift 175317
  have htrace : WordTrace (prefixWord ++ tailWord_175317) baseStart_175317 baseEnd_175317 := by
    simpa [prefixWord, tailWord_175317, baseEnd_175317] using wordTrace_append hprefix tailTrace_175317
  have hstable : (prefixWord ++ tailWord_175317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175317).length < 2 ^ (prefixWord ++ tailWord_175317).sum := by decide
  have hdescent : baseEnd_175317 < baseStart_175317 := by decide
  rcases family_descends (prefixWord ++ tailWord_175317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175389 : List Nat := [1, 4, 2, 3, 1, 1, 3, 3, 2]
def baseStart_175389 : Nat := 118140960795 + 175389 * 2 ^ 59
def prefixEnd_175389 : Nat := 4983230072969 + 3 ^ 40 * 175389 * 2
def baseEnd_175389 : Nat := 80052318676906243049695

theorem tailTrace_175389 : CollatzResearch.WordTrace tailWord_175389 prefixEnd_175389 80052318676906243049695 := by
  unfold tailWord_175389
  simp only [CollatzResearch.WordTrace]
  refine ⟨6396962361603081901545221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4264641574402054601030147 6396962361603081901545221)
  ·
    refine ⟨1199430442800577856539729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6396962361603081901545221 1199430442800577856539729)
    ·
      refine ⟨899572832100433392404797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1199430442800577856539729 899572832100433392404797)
      ·
        refine ⟨337339812037662522151799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 899572832100433392404797 337339812037662522151799)
        ·
          refine ⟨506009718056493783227699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337339812037662522151799 506009718056493783227699)
          ·
            refine ⟨759014577084740674841549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506009718056493783227699 759014577084740674841549)
            ·
              refine ⟨284630466406777753065581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 759014577084740674841549 284630466406777753065581)
              ·
                refine ⟨106736424902541657399593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284630466406777753065581 106736424902541657399593)
                ·
                  refine ⟨80052318676906243049695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106736424902541657399593 80052318676906243049695)
                  ·
                    rfl

theorem cell20_175389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_175389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175389 prefixEnd_175389 := by exact prefixLift 175389
  have htrace : WordTrace (prefixWord ++ tailWord_175389) baseStart_175389 baseEnd_175389 := by
    simpa [prefixWord, tailWord_175389, baseEnd_175389] using wordTrace_append hprefix tailTrace_175389
  have hstable : (prefixWord ++ tailWord_175389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175389).length < 2 ^ (prefixWord ++ tailWord_175389).sum := by decide
  have hdescent : baseEnd_175389 < baseStart_175389 := by decide
  rcases family_descends (prefixWord ++ tailWord_175389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175400 : List Nat := [2, 1, 5, 1, 2, 1, 8]
def baseStart_175400 : Nat := 118140960795 + 175400 * 2 ^ 59
def prefixEnd_175400 : Nat := 4983230072969 + 3 ^ 40 * 175400 * 2
def baseEnd_175400 : Nat := 8895259930737677075887

theorem tailTrace_175400 : CollatzResearch.WordTrace tailWord_175400 prefixEnd_175400 8895259930737677075887 := by
  unfold tailWord_175400
  simp only [CollatzResearch.WordTrace]
  refine ⟨3198681782281615390097827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4264909043042153853463769 3198681782281615390097827)
  ·
    refine ⟨4798022673422423085146741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3198681782281615390097827 4798022673422423085146741)
    ·
      refine ⟨449814625633352164232507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4798022673422423085146741 449814625633352164232507)
      ·
        refine ⟨674721938450028246348761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449814625633352164232507 674721938450028246348761)
        ·
          refine ⟨506041453837521184761571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674721938450028246348761 506041453837521184761571)
          ·
            refine ⟨759062180756281777142357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506041453837521184761571 759062180756281777142357)
            ·
              refine ⟨8895259930737677075887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 759062180756281777142357 8895259930737677075887)
              ·
                rfl

theorem cell20_175400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 8].length) (baseStart_175400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175400 prefixEnd_175400 := by exact prefixLift 175400
  have htrace : WordTrace (prefixWord ++ tailWord_175400) baseStart_175400 baseEnd_175400 := by
    simpa [prefixWord, tailWord_175400, baseEnd_175400] using wordTrace_append hprefix tailTrace_175400
  have hstable : (prefixWord ++ tailWord_175400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175400).length < 2 ^ (prefixWord ++ tailWord_175400).sum := by decide
  have hdescent : baseEnd_175400 < baseStart_175400 := by decide
  rcases family_descends (prefixWord ++ tailWord_175400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175407 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 3]
def baseStart_175407 : Nat := 118140960795 + 175407 * 2 ^ 59
def prefixEnd_175407 : Nat := 4983230072969 + 3 ^ 40 * 175407 * 2
def baseEnd_175407 : Nat := 80060534367378180449621

theorem tailTrace_175407 : CollatzResearch.WordTrace tailWord_175407 prefixEnd_175407 80060534367378180449621 := by
  unfold tailWord_175407
  simp only [CollatzResearch.WordTrace]
  refine ⟨6397618875537870975700475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4265079250358580650466983 6397618875537870975700475)
  ·
    refine ⟨9596428313306806463550713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6397618875537870975700475 9596428313306806463550713)
    ·
      refine ⟨7197321234980104847663035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9596428313306806463550713 7197321234980104847663035)
      ·
        refine ⟨10795981852470157271494553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7197321234980104847663035 10795981852470157271494553)
        ·
          refine ⟨8096986389352617953620915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10795981852470157271494553 8096986389352617953620915)
          ·
            refine ⟨12145479584028926930431373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8096986389352617953620915 12145479584028926930431373)
            ·
              refine ⟨4554554844010847598911765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12145479584028926930431373 4554554844010847598911765)
              ·
                refine ⟨213494758313008481198989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4554554844010847598911765 213494758313008481198989)
                ·
                  refine ⟨80060534367378180449621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213494758313008481198989 80060534367378180449621)
                  ·
                    rfl

theorem cell20_175407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 3].length) (baseStart_175407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175407 prefixEnd_175407 := by exact prefixLift 175407
  have htrace : WordTrace (prefixWord ++ tailWord_175407) baseStart_175407 baseEnd_175407 := by
    simpa [prefixWord, tailWord_175407, baseEnd_175407] using wordTrace_append hprefix tailTrace_175407
  have hstable : (prefixWord ++ tailWord_175407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175407).length < 2 ^ (prefixWord ++ tailWord_175407).sum := by decide
  have hdescent : baseEnd_175407 < baseStart_175407 := by decide
  rcases family_descends (prefixWord ++ tailWord_175407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175410 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_175410 : Nat := 118140960795 + 175410 * 2 ^ 59
def prefixEnd_175410 : Nat := 4983230072969 + 3 ^ 40 * 175410 * 2
def baseEnd_175410 : Nat := 80061903649123503349609

theorem tailTrace_175410 : CollatzResearch.WordTrace tailWord_175410 prefixEnd_175410 80061903649123503349609 := by
  unfold tailWord_175410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599432073631750622014921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4265152196351334992039789 1599432073631750622014921)
  ·
    refine ⟨1199574055223812966511191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1599432073631750622014921 1199574055223812966511191)
    ·
      refine ⟨1799361082835719449766787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1199574055223812966511191 1799361082835719449766787)
      ·
        refine ⟨2699041624253579174650181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799361082835719449766787 2699041624253579174650181)
        ·
          refine ⟨506070304547546095246909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2699041624253579174650181 506070304547546095246909)
          ·
            refine ⟨189776364205329785717591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506070304547546095246909 189776364205329785717591)
            ·
              refine ⟨284664546307994678576387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189776364205329785717591 284664546307994678576387)
              ·
                refine ⟨426996819461992017864581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284664546307994678576387 426996819461992017864581)
                ·
                  refine ⟨80061903649123503349609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426996819461992017864581 80061903649123503349609)
                  ·
                    rfl

theorem cell20_175410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_175410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175410 prefixEnd_175410 := by exact prefixLift 175410
  have htrace : WordTrace (prefixWord ++ tailWord_175410) baseStart_175410 baseEnd_175410 := by
    simpa [prefixWord, tailWord_175410, baseEnd_175410] using wordTrace_append hprefix tailTrace_175410
  have hstable : (prefixWord ++ tailWord_175410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175410).length < 2 ^ (prefixWord ++ tailWord_175410).sum := by decide
  have hdescent : baseEnd_175410 < baseStart_175410 := by decide
  rcases family_descends (prefixWord ++ tailWord_175410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175417 : List Nat := [1, 2, 1, 6, 2, 1, 2, 5]
def baseStart_175417 : Nat := 118140960795 + 175417 * 2 ^ 59
def prefixEnd_175417 : Nat := 4983230072969 + 3 ^ 40 * 175417 * 2
def baseEnd_175417 : Nat := 26688366213287530038749

theorem tailTrace_175417 : CollatzResearch.WordTrace tailWord_175417 prefixEnd_175417 26688366213287530038749 := by
  unfold tailWord_175417
  simp only [CollatzResearch.WordTrace]
  refine ⟨6397983605501642683564505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4265322403667761789043003 6397983605501642683564505)
  ·
    refine ⟨4798487704126232012673379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6397983605501642683564505 4798487704126232012673379)
    ·
      refine ⟨7197731556189348019010069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4798487704126232012673379 7197731556189348019010069)
      ·
        refine ⟨337393666696375688391097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7197731556189348019010069 337393666696375688391097)
        ·
          refine ⟨253045250022281766293323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337393666696375688391097 253045250022281766293323)
          ·
            refine ⟨379567875033422649439985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253045250022281766293323 379567875033422649439985)
            ·
              refine ⟨284675906275066987079989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379567875033422649439985 284675906275066987079989)
              ·
                refine ⟨26688366213287530038749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 284675906275066987079989 26688366213287530038749)
                ·
                  rfl

theorem cell20_175417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 5].length) (baseStart_175417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175417 prefixEnd_175417 := by exact prefixLift 175417
  have htrace : WordTrace (prefixWord ++ tailWord_175417) baseStart_175417 baseEnd_175417 := by
    simpa [prefixWord, tailWord_175417, baseEnd_175417] using wordTrace_append hprefix tailTrace_175417
  have hstable : (prefixWord ++ tailWord_175417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175417).length < 2 ^ (prefixWord ++ tailWord_175417).sum := by decide
  have hdescent : baseEnd_175417 < baseStart_175417 := by decide
  rcases family_descends (prefixWord ++ tailWord_175417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175459 : List Nat := [1, 1, 1, 5, 2, 10]
def baseStart_175459 : Nat := 118140960795 + 175459 * 2 ^ 59
def prefixEnd_175459 : Nat := 4983230072969 + 3 ^ 40 * 175459 * 2
def baseEnd_175459 : Nat := 2966084021640633730225

theorem tailTrace_175459 : CollatzResearch.WordTrace tailWord_175459 prefixEnd_175459 2966084021640633730225 := by
  unfold tailWord_175459
  simp only [CollatzResearch.WordTrace]
  refine ⟨6399515471349483856593431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4266343647566322571062287 6399515471349483856593431)
  ·
    refine ⟨9599273207024225784890147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6399515471349483856593431 9599273207024225784890147)
    ·
      refine ⟨14398909810536338677335221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9599273207024225784890147 14398909810536338677335221)
      ·
        refine ⟨1349897794737781751000177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14398909810536338677335221 1349897794737781751000177)
        ·
          refine ⟨1012423346053336313250133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1349897794737781751000177 1012423346053336313250133)
          ·
            refine ⟨2966084021640633730225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1012423346053336313250133 2966084021640633730225)
            ·
              rfl

theorem cell20_175459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 10].length) (baseStart_175459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175459 prefixEnd_175459 := by exact prefixLift 175459
  have htrace : WordTrace (prefixWord ++ tailWord_175459) baseStart_175459 baseEnd_175459 := by
    simpa [prefixWord, tailWord_175459, baseEnd_175459] using wordTrace_append hprefix tailTrace_175459
  have hstable : (prefixWord ++ tailWord_175459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175459).length < 2 ^ (prefixWord ++ tailWord_175459).sum := by decide
  have hdescent : baseEnd_175459 < baseStart_175459 := by decide
  rcases family_descends (prefixWord ++ tailWord_175459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175483 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 3]
def baseStart_175483 : Nat := 118140960795 + 175483 * 2 ^ 59
def prefixEnd_175483 : Nat := 4983230072969 + 3 ^ 40 * 175483 * 2
def baseEnd_175483 : Nat := 80095222838259693915977

theorem tailTrace_175483 : CollatzResearch.WordTrace tailWord_175483 prefixEnd_175483 80095222838259693915977 := by
  unfold tailWord_175483
  simp only [CollatzResearch.WordTrace]
  refine ⟨6400390823262535955467103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4266927215508357303644735 6400390823262535955467103)
  ·
    refine ⟨9600586234893803933200655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6400390823262535955467103 9600586234893803933200655)
    ·
      refine ⟨14400879352340705899800983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9600586234893803933200655 14400879352340705899800983)
      ·
        refine ⟨21601319028511058849701475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14400879352340705899800983 21601319028511058849701475)
        ·
          refine ⟨32401978542766588274552213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21601319028511058849701475 32401978542766588274552213)
          ·
            refine ⟨1518842744192183825369635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32401978542766588274552213 1518842744192183825369635)
            ·
              refine ⟨2278264116288275738054453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518842744192183825369635 2278264116288275738054453)
              ·
                refine ⟨213587260902025850442605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2278264116288275738054453 213587260902025850442605)
                ·
                  refine ⟨80095222838259693915977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213587260902025850442605 80095222838259693915977)
                  ·
                    rfl

theorem cell20_175483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 3].length) (baseStart_175483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175483 prefixEnd_175483 := by exact prefixLift 175483
  have htrace : WordTrace (prefixWord ++ tailWord_175483) baseStart_175483 baseEnd_175483 := by
    simpa [prefixWord, tailWord_175483, baseEnd_175483] using wordTrace_append hprefix tailTrace_175483
  have hstable : (prefixWord ++ tailWord_175483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175483).length < 2 ^ (prefixWord ++ tailWord_175483).sum := by decide
  have hdescent : baseEnd_175483 < baseStart_175483 := by decide
  rcases family_descends (prefixWord ++ tailWord_175483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175517 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 3]
def baseStart_175517 : Nat := 118140960795 + 175517 * 2 ^ 59
def prefixEnd_175517 : Nat := 4983230072969 + 3 ^ 40 * 175517 * 2
def baseEnd_175517 : Nat := 80110741364706686782505

theorem tailTrace_175517 : CollatzResearch.WordTrace tailWord_175517 prefixEnd_175517 80110741364706686782505 := by
  unfold tailWord_175517
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401630905139359762204805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4267753936759573174803203 6401630905139359762204805)
  ·
    refine ⟨1200305794713629955413401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6401630905139359762204805 1200305794713629955413401)
    ·
      refine ⟨900229346035222466560051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1200305794713629955413401 900229346035222466560051)
      ·
        refine ⟨1350344019052833699840077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900229346035222466560051 1350344019052833699840077)
        ·
          refine ⟨506379007144812637440029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1350344019052833699840077 506379007144812637440029)
          ·
            refine ⟨189892127679304739040011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506379007144812637440029 189892127679304739040011)
            ·
              refine ⟨284838191518957108560017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189892127679304739040011 284838191518957108560017)
              ·
                refine ⟨213628643639217831420013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284838191518957108560017 213628643639217831420013)
                ·
                  refine ⟨80110741364706686782505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213628643639217831420013 80110741364706686782505)
                  ·
                    rfl

theorem cell20_175517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_175517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175517 prefixEnd_175517 := by exact prefixLift 175517
  have htrace : WordTrace (prefixWord ++ tailWord_175517) baseStart_175517 baseEnd_175517 := by
    simpa [prefixWord, tailWord_175517, baseEnd_175517] using wordTrace_append hprefix tailTrace_175517
  have hstable : (prefixWord ++ tailWord_175517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175517).length < 2 ^ (prefixWord ++ tailWord_175517).sum := by decide
  have hdescent : baseEnd_175517 < baseStart_175517 := by decide
  rcases family_descends (prefixWord ++ tailWord_175517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175548 : List Nat := [2, 2, 2, 4, 2, 2, 2, 4]
def baseStart_175548 : Nat := 118140960795 + 175548 * 2 ^ 59
def prefixEnd_175548 : Nat := 4983230072969 + 3 ^ 40 * 175548 * 2
def baseEnd_175548 : Nat := 26708296869802785583015

theorem tailTrace_175548 : CollatzResearch.WordTrace tailWord_175548 prefixEnd_175548 26708296869802785583015 := by
  unfold tailWord_175548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201380784013526028291649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4268507712018034704388865 3201380784013526028291649)
  ·
    refine ⟨2401035588010144521218737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3201380784013526028291649 2401035588010144521218737)
    ·
      refine ⟨1800776691007608390914053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2401035588010144521218737 1800776691007608390914053)
      ·
        refine ⟨337645629563926573296385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1800776691007608390914053 337645629563926573296385)
        ·
          refine ⟨253234222172944929972289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337645629563926573296385 253234222172944929972289)
          ·
            refine ⟨189925666629708697479217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253234222172944929972289 189925666629708697479217)
            ·
              refine ⟨142444249972281523109413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189925666629708697479217 142444249972281523109413)
              ·
                refine ⟨26708296869802785583015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142444249972281523109413 26708296869802785583015)
                ·
                  rfl

theorem cell20_175548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_175548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175548 prefixEnd_175548 := by exact prefixLift 175548
  have htrace : WordTrace (prefixWord ++ tailWord_175548) baseStart_175548 baseEnd_175548 := by
    simpa [prefixWord, tailWord_175548, baseEnd_175548] using wordTrace_append hprefix tailTrace_175548
  have hstable : (prefixWord ++ tailWord_175548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175548).length < 2 ^ (prefixWord ++ tailWord_175548).sum := by decide
  have hdescent : baseEnd_175548 < baseStart_175548 := by decide
  rcases family_descends (prefixWord ++ tailWord_175548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175552 : List Nat := [2, 1, 1, 2, 3, 1, 6, 4]
def baseStart_175552 : Nat := 118140960795 + 175552 * 2 ^ 59
def prefixEnd_175552 : Nat := 4983230072969 + 3 ^ 40 * 175552 * 2
def baseEnd_175552 : Nat := 26708905439467373538565

theorem tailTrace_175552 : CollatzResearch.WordTrace tailWord_175552 prefixEnd_175552 26708905439467373538565 := by
  unfold tailWord_175552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201453730006280369864455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4268604973341707159819273 3201453730006280369864455)
  ·
    refine ⟨4802180595009420554796683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3201453730006280369864455 4802180595009420554796683)
    ·
      refine ⟨7203270892514130832195025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4802180595009420554796683 7203270892514130832195025)
      ·
        refine ⟨5402453169385598124146269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7203270892514130832195025 5402453169385598124146269)
        ·
          refine ⟨2025919938519599296554851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5402453169385598124146269 2025919938519599296554851)
          ·
            refine ⟨3038879907779398944832277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2025919938519599296554851 3038879907779398944832277)
            ·
              refine ⟨142447495677159325539013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3038879907779398944832277 142447495677159325539013)
              ·
                refine ⟨26708905439467373538565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142447495677159325539013 26708905439467373538565)
                ·
                  rfl

theorem cell20_175552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_175552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175552 prefixEnd_175552 := by exact prefixLift 175552
  have htrace : WordTrace (prefixWord ++ tailWord_175552) baseStart_175552 baseEnd_175552 := by
    simpa [prefixWord, tailWord_175552, baseEnd_175552] using wordTrace_append hprefix tailTrace_175552
  have hstable : (prefixWord ++ tailWord_175552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175552).length < 2 ^ (prefixWord ++ tailWord_175552).sum := by decide
  have hdescent : baseEnd_175552 < baseStart_175552 := by decide
  rcases family_descends (prefixWord ++ tailWord_175552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175562 : List Nat := [3, 1, 2, 1, 2, 3, 3, 3, 2]
def baseStart_175562 : Nat := 118140960795 + 175562 * 2 ^ 59
def prefixEnd_175562 : Nat := 4983230072969 + 3 ^ 40 * 175562 * 2
def baseEnd_175562 : Nat := 80131280590886530282321

theorem tailTrace_175562 : CollatzResearch.WordTrace tailWord_175562 prefixEnd_175562 80131280590886530282321 := by
  unfold tailWord_175562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600818047494083111898235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4268848126650888298395293 1600818047494083111898235)
  ·
    refine ⟨2401227071241124667847353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1600818047494083111898235 2401227071241124667847353)
    ·
      refine ⟨1800920303430843500885515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2401227071241124667847353 1800920303430843500885515)
      ·
        refine ⟨2701380455146265251328273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800920303430843500885515 2701380455146265251328273)
        ·
          refine ⟨2026035341359698938496205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2701380455146265251328273 2026035341359698938496205)
          ·
            refine ⟨759763253009887101936077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2026035341359698938496205 759763253009887101936077)
            ·
              refine ⟨284911219878707663226029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 759763253009887101936077 284911219878707663226029)
              ·
                refine ⟨106841707454515373709761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284911219878707663226029 106841707454515373709761)
                ·
                  refine ⟨80131280590886530282321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106841707454515373709761 80131280590886530282321)
                  ·
                    rfl

theorem cell20_175562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_175562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175562 prefixEnd_175562 := by exact prefixLift 175562
  have htrace : WordTrace (prefixWord ++ tailWord_175562) baseStart_175562 baseEnd_175562 := by
    simpa [prefixWord, tailWord_175562, baseEnd_175562] using wordTrace_append hprefix tailTrace_175562
  have hstable : (prefixWord ++ tailWord_175562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175562).length < 2 ^ (prefixWord ++ tailWord_175562).sum := by decide
  have hdescent : baseEnd_175562 < baseStart_175562 := by decide
  rcases family_descends (prefixWord ++ tailWord_175562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175566 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_175566 : Nat := 118140960795 + 175566 * 2 ^ 59
def prefixEnd_175566 : Nat := 4983230072969 + 3 ^ 40 * 175566 * 2
def baseEnd_175566 : Nat := 80133106299880294148971

theorem tailTrace_175566 : CollatzResearch.WordTrace tailWord_175566 prefixEnd_175566 80133106299880294148971 := by
  unfold tailWord_175566
  simp only [CollatzResearch.WordTrace]
  refine ⟨800427260245230141342319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4268945387974560753825701 800427260245230141342319)
  ·
    refine ⟨1200640890367845212013479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 800427260245230141342319 1200640890367845212013479)
    ·
      refine ⟨1800961335551767818020219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1200640890367845212013479 1800961335551767818020219)
      ·
        refine ⟨2701442003327651727030329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800961335551767818020219 2701442003327651727030329)
        ·
          refine ⟨2026081502495738795272747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2701442003327651727030329 2026081502495738795272747)
          ·
            refine ⟨3039122253743608192909121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026081502495738795272747 3039122253743608192909121)
            ·
              refine ⟨2279341690307706144681841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3039122253743608192909121 2279341690307706144681841)
              ·
                refine ⟨1709506267730779608511381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2279341690307706144681841 1709506267730779608511381)
                ·
                  refine ⟨80133106299880294148971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1709506267730779608511381 80133106299880294148971)
                  ·
                    rfl

theorem cell20_175566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_175566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175566 prefixEnd_175566 := by exact prefixLift 175566
  have htrace : WordTrace (prefixWord ++ tailWord_175566) baseStart_175566 baseEnd_175566 := by
    simpa [prefixWord, tailWord_175566, baseEnd_175566] using wordTrace_append hprefix tailTrace_175566
  have hstable : (prefixWord ++ tailWord_175566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175566).length < 2 ^ (prefixWord ++ tailWord_175566).sum := by decide
  have hdescent : baseEnd_175566 < baseStart_175566 := by decide
  rcases family_descends (prefixWord ++ tailWord_175566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175621 : List Nat := [1, 3, 1, 1, 2, 2, 1, 7, 2]
def baseStart_175621 : Nat := 118140960795 + 175621 * 2 ^ 59
def prefixEnd_175621 : Nat := 4983230072969 + 3 ^ 40 * 175621 * 2
def baseEnd_175621 : Nat := 80158209798544547315413

theorem tailTrace_175621 : CollatzResearch.WordTrace tailWord_175621 prefixEnd_175621 80158209798544547315413 := by
  unfold tailWord_175621
  simp only [CollatzResearch.WordTrace]
  refine ⟨6405424096762585523990717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4270282731175057015993811 6405424096762585523990717)
  ·
    refine ⟨2402034036285969571496519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6405424096762585523990717 2402034036285969571496519)
    ·
      refine ⟨3603051054428954357244779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2402034036285969571496519 3603051054428954357244779)
      ·
        refine ⟨5404576581643431535867169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3603051054428954357244779 5404576581643431535867169)
        ·
          refine ⟨4053432436232573651900377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5404576581643431535867169 4053432436232573651900377)
          ·
            refine ⟨3040074327174430238925283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4053432436232573651900377 3040074327174430238925283)
            ·
              refine ⟨4560111490761645358387925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040074327174430238925283 4560111490761645358387925)
              ·
                refine ⟨106877613064726063087217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4560111490761645358387925 106877613064726063087217)
                ·
                  refine ⟨80158209798544547315413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106877613064726063087217 80158209798544547315413)
                  ·
                    rfl

theorem cell20_175621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_175621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175621 prefixEnd_175621 := by exact prefixLift 175621
  have htrace : WordTrace (prefixWord ++ tailWord_175621) baseStart_175621 baseEnd_175621 := by
    simpa [prefixWord, tailWord_175621, baseEnd_175621] using wordTrace_append hprefix tailTrace_175621
  have hstable : (prefixWord ++ tailWord_175621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175621).length < 2 ^ (prefixWord ++ tailWord_175621).sum := by decide
  have hdescent : baseEnd_175621 < baseStart_175621 := by decide
  rcases family_descends (prefixWord ++ tailWord_175621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175628 : List Nat := [2, 2, 1, 2, 6, 7]
def baseStart_175628 : Nat := 118140960795 + 175628 * 2 ^ 59
def prefixEnd_175628 : Nat := 4983230072969 + 3 ^ 40 * 175628 * 2
def baseEnd_175628 : Nat := 2968940918121616077113

theorem tailTrace_175628 : CollatzResearch.WordTrace tailWord_175628 prefixEnd_175628 2968940918121616077113 := by
  unfold tailWord_175628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3202839703868612859747769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4270452938491483812997025 3202839703868612859747769)
  ·
    refine ⟨2402129777901459644810827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3202839703868612859747769 2402129777901459644810827)
    ·
      refine ⟨3603194666852189467216241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2402129777901459644810827 3603194666852189467216241)
      ·
        refine ⟨2702396000139142100412181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3603194666852189467216241 2702396000139142100412181)
        ·
          refine ⟨126674812506522285956821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2702396000139142100412181 126674812506522285956821)
          ·
            refine ⟨2968940918121616077113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 126674812506522285956821 2968940918121616077113)
            ·
              rfl

theorem cell20_175628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 7].length) (baseStart_175628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175628 prefixEnd_175628 := by exact prefixLift 175628
  have htrace : WordTrace (prefixWord ++ tailWord_175628) baseStart_175628 baseEnd_175628 := by
    simpa [prefixWord, tailWord_175628, baseEnd_175628] using wordTrace_append hprefix tailTrace_175628
  have hstable : (prefixWord ++ tailWord_175628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175628).length < 2 ^ (prefixWord ++ tailWord_175628).sum := by decide
  have hdescent : baseEnd_175628 < baseStart_175628 := by decide
  rcases family_descends (prefixWord ++ tailWord_175628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175635 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 3]
def baseStart_175635 : Nat := 118140960795 + 175635 * 2 ^ 59
def prefixEnd_175635 : Nat := 4983230072969 + 3 ^ 40 * 175635 * 2
def baseEnd_175635 : Nat := 80164599780022720848689

theorem tailTrace_175635 : CollatzResearch.WordTrace tailWord_175635 prefixEnd_175635 80164599780022720848689 := by
  unfold tailWord_175635
  simp only [CollatzResearch.WordTrace]
  refine ⟨6405934718711865915000359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4270623145807910610000239 6405934718711865915000359)
  ·
    refine ⟨9608902078067798872500539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6405934718711865915000359 9608902078067798872500539)
    ·
      refine ⟨14413353117101698308750809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9608902078067798872500539 14413353117101698308750809)
      ·
        refine ⟨10810014837826273731563107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14413353117101698308750809 10810014837826273731563107)
        ·
          refine ⟨16215022256739410597344661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10810014837826273731563107 16215022256739410597344661)
          ·
            refine ⟨760079168284659871750531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16215022256739410597344661 760079168284659871750531)
            ·
              refine ⟨1140118752426989807625797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760079168284659871750531 1140118752426989807625797)
              ·
                refine ⟨213772266080060588929837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1140118752426989807625797 213772266080060588929837)
                ·
                  refine ⟨80164599780022720848689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213772266080060588929837 80164599780022720848689)
                  ·
                    rfl

theorem cell20_175635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 3].length) (baseStart_175635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175635 prefixEnd_175635 := by exact prefixLift 175635
  have htrace : WordTrace (prefixWord ++ tailWord_175635) baseStart_175635 baseEnd_175635 := by
    simpa [prefixWord, tailWord_175635, baseEnd_175635] using wordTrace_append hprefix tailTrace_175635
  have hstable : (prefixWord ++ tailWord_175635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175635).length < 2 ^ (prefixWord ++ tailWord_175635).sum := by decide
  have hdescent : baseEnd_175635 < baseStart_175635 := by decide
  rcases family_descends (prefixWord ++ tailWord_175635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175642 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_175642 : Nat := 118140960795 + 175642 * 2 ^ 59
def prefixEnd_175642 : Nat := 4983230072969 + 3 ^ 40 * 175642 * 2
def baseEnd_175642 : Nat := 80167794770761807615327

theorem tailTrace_175642 : CollatzResearch.WordTrace tailWord_175642 prefixEnd_175642 80167794770761807615327 := by
  unfold tailWord_175642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601547507421626527626295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4270793353124337407003453 1601547507421626527626295)
  ·
    refine ⟨2402321261132439791439443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1601547507421626527626295 2402321261132439791439443)
    ·
      refine ⟨3603481891698659687159165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2402321261132439791439443 3603481891698659687159165)
      ·
        refine ⟨1351305709386997382684687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3603481891698659687159165 1351305709386997382684687)
        ·
          refine ⟨2026958564080496074027031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351305709386997382684687 2026958564080496074027031)
          ·
            refine ⟨3040437846120744111040547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026958564080496074027031 3040437846120744111040547)
            ·
              refine ⟨4560656769181116166560821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040437846120744111040547 4560656769181116166560821)
              ·
                refine ⟨427561572110729640615077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4560656769181116166560821 427561572110729640615077)
                ·
                  refine ⟨80167794770761807615327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 427561572110729640615077 80167794770761807615327)
                  ·
                    rfl

theorem cell20_175642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_175642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175642 prefixEnd_175642 := by exact prefixLift 175642
  have htrace : WordTrace (prefixWord ++ tailWord_175642) baseStart_175642 baseEnd_175642 := by
    simpa [prefixWord, tailWord_175642, baseEnd_175642] using wordTrace_append hprefix tailTrace_175642
  have hstable : (prefixWord ++ tailWord_175642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175642).length < 2 ^ (prefixWord ++ tailWord_175642).sum := by decide
  have hdescent : baseEnd_175642 < baseStart_175642 := by decide
  rcases family_descends (prefixWord ++ tailWord_175642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175697 : List Nat := [1, 2, 2, 1, 3, 2, 1, 6, 2]
def baseStart_175697 : Nat := 118140960795 + 175697 * 2 ^ 59
def prefixEnd_175697 : Nat := 4983230072969 + 3 ^ 40 * 175697 * 2
def baseEnd_175697 : Nat := 80192898269426060781769

theorem tailTrace_175697 : CollatzResearch.WordTrace tailWord_175697 prefixEnd_175697 80192898269426060781769 := by
  unfold tailWord_175697
  simp only [CollatzResearch.WordTrace]
  refine ⟨6408196044487250503757345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4272130696324833669171563 6408196044487250503757345)
  ·
    refine ⟨4806147033365437877818009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6408196044487250503757345 4806147033365437877818009)
    ·
      refine ⟨3604610275024078408363507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4806147033365437877818009 3604610275024078408363507)
      ·
        refine ⟨5406915412536117612545261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3604610275024078408363507 5406915412536117612545261)
        ·
          refine ⟨2027593279701044104704473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5406915412536117612545261 2027593279701044104704473)
          ·
            refine ⟨1520694959775783078528355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2027593279701044104704473 1520694959775783078528355)
            ·
              refine ⟨2281042439663674617792533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520694959775783078528355 2281042439663674617792533)
              ·
                refine ⟨106923864359234747709025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2281042439663674617792533 106923864359234747709025)
                ·
                  refine ⟨80192898269426060781769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106923864359234747709025 80192898269426060781769)
                  ·
                    rfl

theorem cell20_175697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_175697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175697 prefixEnd_175697 := by exact prefixLift 175697
  have htrace : WordTrace (prefixWord ++ tailWord_175697) baseStart_175697 baseEnd_175697 := by
    simpa [prefixWord, tailWord_175697, baseEnd_175697] using wordTrace_append hprefix tailTrace_175697
  have hstable : (prefixWord ++ tailWord_175697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175697).length < 2 ^ (prefixWord ++ tailWord_175697).sum := by decide
  have hdescent : baseEnd_175697 < baseStart_175697 := by decide
  rcases family_descends (prefixWord ++ tailWord_175697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175749 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 3]
def baseStart_175749 : Nat := 118140960795 + 175749 * 2 ^ 59
def prefixEnd_175749 : Nat := 4983230072969 + 3 ^ 40 * 175749 * 2
def baseEnd_175749 : Nat := 80216632486344991048223

theorem tailTrace_175749 : CollatzResearch.WordTrace tailWord_175749 prefixEnd_175749 80216632486344991048223 := by
  unfold tailWord_175749
  simp only [CollatzResearch.WordTrace]
  refine ⟨6410092640298863384650301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4273395093532575589766867 6410092640298863384650301)
  ·
    refine ⟨2403784740112073769243863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6410092640298863384650301 2403784740112073769243863)
    ·
      refine ⟨3605677110168110653865795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2403784740112073769243863 3605677110168110653865795)
      ·
        refine ⟨5408515665252165980798693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605677110168110653865795 5408515665252165980798693)
        ·
          refine ⟨1014096687234781121399755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5408515665252165980798693 1014096687234781121399755)
          ·
            refine ⟨1521145030852171682099633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014096687234781121399755 1521145030852171682099633)
            ·
              refine ⟨1140858773139128761574725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521145030852171682099633 1140858773139128761574725)
              ·
                refine ⟨213911019963586642795261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1140858773139128761574725 213911019963586642795261)
                ·
                  refine ⟨80216632486344991048223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213911019963586642795261 80216632486344991048223)
                  ·
                    rfl

theorem cell20_175749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_175749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175749 prefixEnd_175749 := by exact prefixLift 175749
  have htrace : WordTrace (prefixWord ++ tailWord_175749) baseStart_175749 baseEnd_175749 := by
    simpa [prefixWord, tailWord_175749, baseEnd_175749] using wordTrace_append hprefix tailTrace_175749
  have hstable : (prefixWord ++ tailWord_175749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175749).length < 2 ^ (prefixWord ++ tailWord_175749).sum := by decide
  have hdescent : baseEnd_175749 < baseStart_175749 := by decide
  rcases family_descends (prefixWord ++ tailWord_175749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175762 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_175762 : Nat := 118140960795 + 175762 * 2 ^ 59
def prefixEnd_175762 : Nat := 4983230072969 + 3 ^ 40 * 175762 * 2
def baseEnd_175762 : Nat := 80222566040574723614837

theorem tailTrace_175762 : CollatzResearch.WordTrace tailWord_175762 prefixEnd_175762 80222566040574723614837 := by
  unfold tailWord_175762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1602641697312941651218385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4273711192834511069915693 1602641697312941651218385)
  ·
    refine ⟨1201981272984706238413789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1602641697312941651218385 1201981272984706238413789)
    ·
      refine ⟨450742977369264839405171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1201981272984706238413789 450742977369264839405171)
      ·
        refine ⟨676114466053897259107757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450742977369264839405171 676114466053897259107757)
        ·
          refine ⟨253542924770211472165409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 676114466053897259107757 253542924770211472165409)
          ·
            refine ⟨190157193577658604124057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253542924770211472165409 190157193577658604124057)
            ·
              refine ⟨142617895183243953093043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190157193577658604124057 142617895183243953093043)
              ·
                refine ⟨213926842774865929639565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142617895183243953093043 213926842774865929639565)
                ·
                  refine ⟨80222566040574723614837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213926842774865929639565 80222566040574723614837)
                  ·
                    rfl

theorem cell20_175762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_175762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175762 prefixEnd_175762 := by exact prefixLift 175762
  have htrace : WordTrace (prefixWord ++ tailWord_175762) baseStart_175762 baseEnd_175762 := by
    simpa [prefixWord, tailWord_175762, baseEnd_175762] using wordTrace_append hprefix tailTrace_175762
  have hstable : (prefixWord ++ tailWord_175762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175762).length < 2 ^ (prefixWord ++ tailWord_175762).sum := by decide
  have hdescent : baseEnd_175762 < baseStart_175762 := by decide
  rcases family_descends (prefixWord ++ tailWord_175762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175804 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 3]
def baseStart_175804 : Nat := 118140960795 + 175804 * 2 ^ 59
def prefixEnd_175804 : Nat := 4983230072969 + 3 ^ 40 * 175804 * 2
def baseEnd_175804 : Nat := 80241735985009244214665

theorem tailTrace_175804 : CollatzResearch.WordTrace tailWord_175804 prefixEnd_175804 80241735985009244214665 := by
  unfold tailWord_175804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3206049327549803888951233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4274732436733071851934977 3206049327549803888951233)
  ·
    refine ⟨2404536995662352916713425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3206049327549803888951233 2404536995662352916713425)
    ·
      refine ⟨1803402746746764687535069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2404536995662352916713425 1803402746746764687535069)
      ·
        refine ⟨676276030030036757825651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1803402746746764687535069 676276030030036757825651)
        ·
          refine ⟨1014414045045055136738477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676276030030036757825651 1014414045045055136738477)
          ·
            refine ⟨380405266891895676276929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1014414045045055136738477 380405266891895676276929)
            ·
              refine ⟨285303950168921757207697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380405266891895676276929 285303950168921757207697)
              ·
                refine ⟨213977962626691317905773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285303950168921757207697 213977962626691317905773)
                ·
                  refine ⟨80241735985009244214665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213977962626691317905773 80241735985009244214665)
                  ·
                    rfl

theorem cell20_175804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_175804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175804 prefixEnd_175804 := by exact prefixLift 175804
  have htrace : WordTrace (prefixWord ++ tailWord_175804) baseStart_175804 baseEnd_175804 := by
    simpa [prefixWord, tailWord_175804, baseEnd_175804] using wordTrace_append hprefix tailTrace_175804
  have hstable : (prefixWord ++ tailWord_175804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175804).length < 2 ^ (prefixWord ++ tailWord_175804).sum := by decide
  have hdescent : baseEnd_175804 < baseStart_175804 := by decide
  rcases family_descends (prefixWord ++ tailWord_175804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175810 : List Nat := [3, 5, 1, 2, 2, 1, 1, 5]
def baseStart_175810 : Nat := 118140960795 + 175810 * 2 ^ 59
def prefixEnd_175810 : Nat := 4983230072969 + 3 ^ 40 * 175810 * 2
def baseEnd_175810 : Nat := 26748158182833296671547

theorem tailTrace_175810 : CollatzResearch.WordTrace tailWord_175810 prefixEnd_175810 26748158182833296671547 := by
  unfold tailWord_175810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1603079373269467700655221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4274878328718580535080589 1603079373269467700655221)
  ·
    refine ⟨150288691244012596936427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1603079373269467700655221 150288691244012596936427)
    ·
      refine ⟨225433036866018895404641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150288691244012596936427 225433036866018895404641)
      ·
        refine ⟨169074777649514171553481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225433036866018895404641 169074777649514171553481)
        ·
          refine ⟨126806083237135628665111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169074777649514171553481 126806083237135628665111)
          ·
            refine ⟨190209124855703442997667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126806083237135628665111 190209124855703442997667)
            ·
              refine ⟨285313687283555164496501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190209124855703442997667 285313687283555164496501)
              ·
                refine ⟨26748158182833296671547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 285313687283555164496501 26748158182833296671547)
                ·
                  rfl

theorem cell20_175810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_175810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175810 prefixEnd_175810 := by exact prefixLift 175810
  have htrace : WordTrace (prefixWord ++ tailWord_175810) baseStart_175810 baseEnd_175810 := by
    simpa [prefixWord, tailWord_175810, baseEnd_175810] using wordTrace_append hprefix tailTrace_175810
  have hstable : (prefixWord ++ tailWord_175810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175810).length < 2 ^ (prefixWord ++ tailWord_175810).sum := by decide
  have hdescent : baseEnd_175810 < baseStart_175810 := by decide
  rcases family_descends (prefixWord ++ tailWord_175810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175814 : List Nat := [6, 1, 2, 1, 1, 1, 3, 5]
def baseStart_175814 : Nat := 118140960795 + 175814 * 2 ^ 59
def prefixEnd_175814 : Nat := 4983230072969 + 3 ^ 40 * 175814 * 2
def baseEnd_175814 : Nat := 26748766752497884627097

theorem tailTrace_175814 : CollatzResearch.WordTrace tailWord_175814 prefixEnd_175814 26748766752497884627097 := by
  unfold tailWord_175814
  simp only [CollatzResearch.WordTrace]
  refine ⟨200389480783230608930203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4274975590042252990510997 200389480783230608930203)
  ·
    refine ⟨300584221174845913395305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200389480783230608930203 300584221174845913395305)
    ·
      refine ⟨225438165881134435046479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300584221174845913395305 225438165881134435046479)
      ·
        refine ⟨338157248821701652569719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225438165881134435046479 338157248821701652569719)
        ·
          refine ⟨507235873232552478854579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338157248821701652569719 507235873232552478854579)
          ·
            refine ⟨760853809848828718281869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507235873232552478854579 760853809848828718281869)
            ·
              refine ⟨285320178693310769355701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 760853809848828718281869 285320178693310769355701)
              ·
                refine ⟨26748766752497884627097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 285320178693310769355701 26748766752497884627097)
                ·
                  rfl

theorem cell20_175814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_175814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175814 prefixEnd_175814 := by exact prefixLift 175814
  have htrace : WordTrace (prefixWord ++ tailWord_175814) baseStart_175814 baseEnd_175814 := by
    simpa [prefixWord, tailWord_175814, baseEnd_175814] using wordTrace_append hprefix tailTrace_175814
  have hstable : (prefixWord ++ tailWord_175814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175814).length < 2 ^ (prefixWord ++ tailWord_175814).sum := by decide
  have hdescent : baseEnd_175814 < baseStart_175814 := by decide
  rcases family_descends (prefixWord ++ tailWord_175814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175821 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 3]
def baseStart_175821 : Nat := 118140960795 + 175821 * 2 ^ 59
def prefixEnd_175821 : Nat := 4983230072969 + 3 ^ 40 * 175821 * 2
def baseEnd_175821 : Nat := 80249495248232740647929

theorem tailTrace_175821 : CollatzResearch.WordTrace tailWord_175821 prefixEnd_175821 80249495248232740647929 := by
  unfold tailWord_175821
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412718696038019681271317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4275145797358679787514211 6412718696038019681271317)
  ·
    refine ⟨300596188876782172559593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6412718696038019681271317 300596188876782172559593)
    ·
      refine ⟨225447141657586629419695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300596188876782172559593 225447141657586629419695)
      ·
        refine ⟨338170712486379944129543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225447141657586629419695 338170712486379944129543)
        ·
          refine ⟨507256068729569916194315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338170712486379944129543 507256068729569916194315)
          ·
            refine ⟨760884103094354874291473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507256068729569916194315 760884103094354874291473)
            ·
              refine ⟨570663077320766155718605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760884103094354874291473 570663077320766155718605)
              ·
                refine ⟨213998653995287308394477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570663077320766155718605 213998653995287308394477)
                ·
                  refine ⟨80249495248232740647929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213998653995287308394477 80249495248232740647929)
                  ·
                    rfl

theorem cell20_175821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_175821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175821 prefixEnd_175821 := by exact prefixLift 175821
  have htrace : WordTrace (prefixWord ++ tailWord_175821) baseStart_175821 baseEnd_175821 := by
    simpa [prefixWord, tailWord_175821, baseEnd_175821] using wordTrace_append hprefix tailTrace_175821
  have hstable : (prefixWord ++ tailWord_175821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175821).length < 2 ^ (prefixWord ++ tailWord_175821).sum := by decide
  have hdescent : baseEnd_175821 < baseStart_175821 := by decide
  rcases family_descends (prefixWord ++ tailWord_175821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175825 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 3]
def baseStart_175825 : Nat := 118140960795 + 175825 * 2 ^ 59
def prefixEnd_175825 : Nat := 4983230072969 + 3 ^ 40 * 175825 * 2
def baseEnd_175825 : Nat := 80251320957226504514579

theorem tailTrace_175825 : CollatzResearch.WordTrace tailWord_175825 prefixEnd_175825 80251320957226504514579 := by
  unfold tailWord_175825
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412864588023528364416929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4275243058682352242944619 6412864588023528364416929)
  ·
    refine ⟨4809648441017646273312697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6412864588023528364416929 4809648441017646273312697)
    ·
      refine ⟨3607236330763234704984523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4809648441017646273312697 3607236330763234704984523)
      ·
        refine ⟨5410854496144852057476785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607236330763234704984523 5410854496144852057476785)
        ·
          refine ⟨4058140872108639043107589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5410854496144852057476785 4058140872108639043107589)
          ·
            refine ⟨760901413520369820582673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4058140872108639043107589 760901413520369820582673)
            ·
              refine ⟨570676060140277365437005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760901413520369820582673 570676060140277365437005)
              ·
                refine ⟨214003522552604012038877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570676060140277365437005 214003522552604012038877)
                ·
                  refine ⟨80251320957226504514579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214003522552604012038877 80251320957226504514579)
                  ·
                    rfl

theorem cell20_175825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_175825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175825 prefixEnd_175825 := by exact prefixLift 175825
  have htrace : WordTrace (prefixWord ++ tailWord_175825) baseStart_175825 baseEnd_175825 := by
    simpa [prefixWord, tailWord_175825, baseEnd_175825] using wordTrace_append hprefix tailTrace_175825
  have hstable : (prefixWord ++ tailWord_175825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175825).length < 2 ^ (prefixWord ++ tailWord_175825).sum := by decide
  have hdescent : baseEnd_175825 < baseStart_175825 := by decide
  rcases family_descends (prefixWord ++ tailWord_175825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175832 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_175832 : Nat := 118140960795 + 175832 * 2 ^ 59
def prefixEnd_175832 : Nat := 4983230072969 + 3 ^ 40 * 175832 * 2
def baseEnd_175832 : Nat := 80254515947965591281217

theorem tailTrace_175832 : CollatzResearch.WordTrace tailWord_175832 prefixEnd_175832 80254515947965591281217 := by
  unfold tailWord_175832
  simp only [CollatzResearch.WordTrace]
  refine ⟨3206559949499084279960875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4275413265998779039947833 3206559949499084279960875)
  ·
    refine ⟨4809839924248626419941313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3206559949499084279960875 4809839924248626419941313)
    ·
      refine ⟨3607379943186469814955985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4809839924248626419941313 3607379943186469814955985)
      ·
        refine ⟨2705534957389852361216989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3607379943186469814955985 2705534957389852361216989)
        ·
          refine ⟨1014575609021194635456371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2705534957389852361216989 1014575609021194635456371)
          ·
            refine ⟨1521863413531791953184557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014575609021194635456371 1521863413531791953184557)
            ·
              refine ⟨570698780074421982444209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1521863413531791953184557 570698780074421982444209)
              ·
                refine ⟨428024085055816486833157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570698780074421982444209 428024085055816486833157)
                ·
                  refine ⟨80254515947965591281217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 428024085055816486833157 80254515947965591281217)
                  ·
                    rfl

theorem cell20_175832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_175832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175832 prefixEnd_175832 := by exact prefixLift 175832
  have htrace : WordTrace (prefixWord ++ tailWord_175832) baseStart_175832 baseEnd_175832 := by
    simpa [prefixWord, tailWord_175832, baseEnd_175832] using wordTrace_append hprefix tailTrace_175832
  have hstable : (prefixWord ++ tailWord_175832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175832).length < 2 ^ (prefixWord ++ tailWord_175832).sum := by decide
  have hdescent : baseEnd_175832 < baseStart_175832 := by decide
  rcases family_descends (prefixWord ++ tailWord_175832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175863 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 3]
def baseStart_175863 : Nat := 118140960795 + 175863 * 2 ^ 59
def prefixEnd_175863 : Nat := 4983230072969 + 3 ^ 40 * 175863 * 2
def baseEnd_175863 : Nat := 80268665192667261247757

theorem tailTrace_175863 : CollatzResearch.WordTrace tailWord_175863 prefixEnd_175863 80268665192667261247757 := by
  unfold tailWord_175863
  simp only [CollatzResearch.WordTrace]
  refine ⟨6414250561885860854300243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4276167041257240569533495 6414250561885860854300243)
  ·
    refine ⟨9621375842828791281450365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6414250561885860854300243 9621375842828791281450365)
    ·
      refine ⟨3608015941060796730543887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9621375842828791281450365 3608015941060796730543887)
      ·
        refine ⟨5412023911591195095815831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608015941060796730543887 5412023911591195095815831)
        ·
          refine ⟨8118035867386792643723747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412023911591195095815831 8118035867386792643723747)
          ·
            refine ⟨12177053801080188965585621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8118035867386792643723747 12177053801080188965585621)
            ·
              refine ⟨285399698462816928880913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12177053801080188965585621 285399698462816928880913)
              ·
                refine ⟨214049773847112696660685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285399698462816928880913 214049773847112696660685)
                ·
                  refine ⟨80268665192667261247757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214049773847112696660685 80268665192667261247757)
                  ·
                    rfl

theorem cell20_175863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 3].length) (baseStart_175863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175863 prefixEnd_175863 := by exact prefixLift 175863
  have htrace : WordTrace (prefixWord ++ tailWord_175863) baseStart_175863 baseEnd_175863 := by
    simpa [prefixWord, tailWord_175863, baseEnd_175863] using wordTrace_append hprefix tailTrace_175863
  have hstable : (prefixWord ++ tailWord_175863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175863).length < 2 ^ (prefixWord ++ tailWord_175863).sum := by decide
  have hdescent : baseEnd_175863 < baseStart_175863 := by decide
  rcases family_descends (prefixWord ++ tailWord_175863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175880 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 3]
def baseStart_175880 : Nat := 118140960795 + 175880 * 2 ^ 59
def prefixEnd_175880 : Nat := 4983230072969 + 3 ^ 40 * 175880 * 2
def baseEnd_175880 : Nat := 80276424455890757681021

theorem tailTrace_175880 : CollatzResearch.WordTrace tailWord_175880 prefixEnd_175880 80276424455890757681021 := by
  unfold tailWord_175880
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207435301412136378834547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4276580401882848505112729 3207435301412136378834547)
  ·
    refine ⟨4811152952118204568251821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3207435301412136378834547 4811152952118204568251821)
    ·
      refine ⟨1804182357044326713094433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4811152952118204568251821 1804182357044326713094433)
      ·
        refine ⟨1353136767783245034820825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1804182357044326713094433 1353136767783245034820825)
        ·
          refine ⟨1014852575837433776115619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1353136767783245034820825 1014852575837433776115619)
          ·
            refine ⟨1522278863756150664173429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014852575837433776115619 1522278863756150664173429)
            ·
              refine ⟨142713643477139124766259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1522278863756150664173429 142713643477139124766259)
              ·
                refine ⟨214070465215708687149389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142713643477139124766259 214070465215708687149389)
                ·
                  refine ⟨80276424455890757681021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214070465215708687149389 80276424455890757681021)
                  ·
                    rfl

theorem cell20_175880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_175880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175880 prefixEnd_175880 := by exact prefixLift 175880
  have htrace : WordTrace (prefixWord ++ tailWord_175880) baseStart_175880 baseEnd_175880 := by
    simpa [prefixWord, tailWord_175880, baseEnd_175880] using wordTrace_append hprefix tailTrace_175880
  have hstable : (prefixWord ++ tailWord_175880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175880).length < 2 ^ (prefixWord ++ tailWord_175880).sum := by decide
  have hdescent : baseEnd_175880 < baseStart_175880 := by decide
  rcases family_descends (prefixWord ++ tailWord_175880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175890 : List Nat := [3, 2, 4, 1, 1, 3, 2, 4]
def baseStart_175890 : Nat := 118140960795 + 175890 * 2 ^ 59
def prefixEnd_175890 : Nat := 4983230072969 + 3 ^ 40 * 175890 * 2
def baseEnd_175890 : Nat := 26760329576125055782549

theorem tailTrace_175890 : CollatzResearch.WordTrace tailWord_175890 prefixEnd_175890 26760329576125055782549 := by
  unfold tailWord_175890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1603808833197011116383281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4276823555192029643688749 1603808833197011116383281)
  ·
    refine ⟨1202856624897758337287461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1603808833197011116383281 1202856624897758337287461)
    ·
      refine ⟨225535617168329688241399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1202856624897758337287461 225535617168329688241399)
      ·
        refine ⟨338303425752494532362099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225535617168329688241399 338303425752494532362099)
        ·
          refine ⟨507455138628741798543149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338303425752494532362099 507455138628741798543149)
          ·
            refine ⟨190295676985778174453681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 507455138628741798543149 190295676985778174453681)
            ·
              refine ⟨142721757739333630840261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190295676985778174453681 142721757739333630840261)
              ·
                refine ⟨26760329576125055782549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142721757739333630840261 26760329576125055782549)
                ·
                  rfl

theorem cell20_175890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_175890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175890 prefixEnd_175890 := by exact prefixLift 175890
  have htrace : WordTrace (prefixWord ++ tailWord_175890) baseStart_175890 baseEnd_175890 := by
    simpa [prefixWord, tailWord_175890, baseEnd_175890] using wordTrace_append hprefix tailTrace_175890
  have hstable : (prefixWord ++ tailWord_175890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175890).length < 2 ^ (prefixWord ++ tailWord_175890).sum := by decide
  have hdescent : baseEnd_175890 < baseStart_175890 := by decide
  rcases family_descends (prefixWord ++ tailWord_175890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175891 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_175891 : Nat := 118140960795 + 175891 * 2 ^ 59
def prefixEnd_175891 : Nat := 4983230072969 + 3 ^ 40 * 175891 * 2
def baseEnd_175891 : Nat := 80281445155623608314309

theorem tailTrace_175891 : CollatzResearch.WordTrace tailWord_175891 prefixEnd_175891 80281445155623608314309 := by
  unfold tailWord_175891
  simp only [CollatzResearch.WordTrace]
  refine ⟨6415271805784421636319527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4276847870522947757546351 6415271805784421636319527)
  ·
    refine ⟨9622907708676632454479291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6415271805784421636319527 9622907708676632454479291)
    ·
      refine ⟨14434361563014948681718937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9622907708676632454479291 14434361563014948681718937)
      ·
        refine ⟨10825771172261211511289203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14434361563014948681718937 10825771172261211511289203)
        ·
          refine ⟨16238656758391817266933805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10825771172261211511289203 16238656758391817266933805)
          ·
            refine ⟨6089496284396931475100177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16238656758391817266933805 6089496284396931475100177)
            ·
              refine ⟨4567122213297698606325133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6089496284396931475100177 4567122213297698606325133)
              ·
                refine ⟨1712670829986636977371925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4567122213297698606325133 1712670829986636977371925)
                ·
                  refine ⟨80281445155623608314309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1712670829986636977371925 80281445155623608314309)
                  ·
                    rfl

theorem cell20_175891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_175891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175891 prefixEnd_175891 := by exact prefixLift 175891
  have htrace : WordTrace (prefixWord ++ tailWord_175891) baseStart_175891 baseEnd_175891 := by
    simpa [prefixWord, tailWord_175891, baseEnd_175891] using wordTrace_append hprefix tailTrace_175891
  have hstable : (prefixWord ++ tailWord_175891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175891).length < 2 ^ (prefixWord ++ tailWord_175891).sum := by decide
  have hdescent : baseEnd_175891 < baseStart_175891 := by decide
  rcases family_descends (prefixWord ++ tailWord_175891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175935 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 3]
def baseStart_175935 : Nat := 118140960795 + 175935 * 2 ^ 59
def prefixEnd_175935 : Nat := 4983230072969 + 3 ^ 40 * 175935 * 2
def baseEnd_175935 : Nat := 80301527954555010847463

theorem tailTrace_175935 : CollatzResearch.WordTrace tailWord_175935 prefixEnd_175935 80301527954555010847463 := by
  unfold tailWord_175935
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416876617625017150921259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4277917745083344767280839 6416876617625017150921259)
  ·
    refine ⟨9625314926437525726381889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6416876617625017150921259 9625314926437525726381889)
    ·
      refine ⟨7218986194828144294786417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9625314926437525726381889 7218986194828144294786417)
      ·
        refine ⟨5414239646121108221089813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7218986194828144294786417 5414239646121108221089813)
        ·
          refine ⟨253792483411926947863585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5414239646121108221089813 253792483411926947863585)
          ·
            refine ⟨190344362558945210897689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253792483411926947863585 190344362558945210897689)
            ·
              refine ⟨142758271919208908173267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190344362558945210897689 142758271919208908173267)
              ·
                refine ⟨214137407878813362259901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142758271919208908173267 214137407878813362259901)
                ·
                  refine ⟨80301527954555010847463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214137407878813362259901 80301527954555010847463)
                  ·
                    rfl

theorem cell20_175935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 3].length) (baseStart_175935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175935 prefixEnd_175935 := by exact prefixLift 175935
  have htrace : WordTrace (prefixWord ++ tailWord_175935) baseStart_175935 baseEnd_175935 := by
    simpa [prefixWord, tailWord_175935, baseEnd_175935] using wordTrace_append hprefix tailTrace_175935
  have hstable : (prefixWord ++ tailWord_175935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175935).length < 2 ^ (prefixWord ++ tailWord_175935).sum := by decide
  have hdescent : baseEnd_175935 < baseStart_175935 := by decide
  rcases family_descends (prefixWord ++ tailWord_175935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175939 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 3]
def baseStart_175939 : Nat := 118140960795 + 175939 * 2 ^ 59
def prefixEnd_175939 : Nat := 4983230072969 + 3 ^ 40 * 175939 * 2
def baseEnd_175939 : Nat := 80303353663548774714113

theorem tailTrace_175939 : CollatzResearch.WordTrace tailWord_175939 prefixEnd_175939 80303353663548774714113 := by
  unfold tailWord_175939
  simp only [CollatzResearch.WordTrace]
  refine ⟨6417022509610525834066871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4278015006407017222711247 6417022509610525834066871)
  ·
    refine ⟨9625533764415788751100307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6417022509610525834066871 9625533764415788751100307)
    ·
      refine ⟨14438300646623683126650461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9625533764415788751100307 14438300646623683126650461)
      ·
        refine ⟨5414362742483881172493923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14438300646623683126650461 5414362742483881172493923)
        ·
          refine ⟨8121544113725821758740885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5414362742483881172493923 8121544113725821758740885)
          ·
            refine ⟨380697380330897894940979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8121544113725821758740885 380697380330897894940979)
            ·
              refine ⟨571046070496346842411469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380697380330897894940979 571046070496346842411469)
              ·
                refine ⟨214142276436130065904301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 571046070496346842411469 214142276436130065904301)
                ·
                  refine ⟨80303353663548774714113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214142276436130065904301 80303353663548774714113)
                  ·
                    rfl

theorem cell20_175939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 3].length) (baseStart_175939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175939 prefixEnd_175939 := by exact prefixLift 175939
  have htrace : WordTrace (prefixWord ++ tailWord_175939) baseStart_175939 baseEnd_175939 := by
    simpa [prefixWord, tailWord_175939, baseEnd_175939] using wordTrace_append hprefix tailTrace_175939
  have hstable : (prefixWord ++ tailWord_175939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175939).length < 2 ^ (prefixWord ++ tailWord_175939).sum := by decide
  have hdescent : baseEnd_175939 < baseStart_175939 := by decide
  rcases family_descends (prefixWord ++ tailWord_175939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175953 : List Nat := [1, 2, 2, 1, 5, 1, 2, 6]
def baseStart_175953 : Nat := 118140960795 + 175953 * 2 ^ 59
def prefixEnd_175953 : Nat := 4983230072969 + 3 ^ 40 * 175953 * 2
def baseEnd_175953 : Nat := 26769914548342316082463

theorem tailTrace_175953 : CollatzResearch.WordTrace tailWord_175953 prefixEnd_175953 26769914548342316082463 := by
  unfold tailWord_175953
  simp only [CollatzResearch.WordTrace]
  refine ⟨6417533131559806225076513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4278355421039870816717675 6417533131559806225076513)
  ·
    refine ⟨4813149848669854668807385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6417533131559806225076513 4813149848669854668807385)
    ·
      refine ⟨3609862386502391001605539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4813149848669854668807385 3609862386502391001605539)
      ·
        refine ⟨5414793579753586502408309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3609862386502391001605539 5414793579753586502408309)
        ·
          refine ⟨507636898101898734600779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5414793579753586502408309 507636898101898734600779)
          ·
            refine ⟨761455347152848101901169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507636898101898734600779 761455347152848101901169)
            ·
              refine ⟨571091510364636076425877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 761455347152848101901169 571091510364636076425877)
              ·
                refine ⟨26769914548342316082463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 571091510364636076425877 26769914548342316082463)
                ·
                  rfl

theorem cell20_175953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_175953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175953 prefixEnd_175953 := by exact prefixLift 175953
  have htrace : WordTrace (prefixWord ++ tailWord_175953) baseStart_175953 baseEnd_175953 := by
    simpa [prefixWord, tailWord_175953, baseEnd_175953] using wordTrace_append hprefix tailTrace_175953
  have hstable : (prefixWord ++ tailWord_175953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175953).length < 2 ^ (prefixWord ++ tailWord_175953).sum := by decide
  have hdescent : baseEnd_175953 < baseStart_175953 := by decide
  rcases family_descends (prefixWord ++ tailWord_175953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175980 : List Nat := [2, 2, 1, 1, 4, 2, 4, 2, 2]
def baseStart_175980 : Nat := 118140960795 + 175980 * 2 ^ 59
def prefixEnd_175980 : Nat := 4983230072969 + 3 ^ 40 * 175980 * 2
def baseEnd_175980 : Nat := 80322067180734854347279

theorem tailTrace_175980 : CollatzResearch.WordTrace tailWord_175980 prefixEnd_175980 80322067180734854347279 := by
  unfold tailWord_175980
  simp only [CollatzResearch.WordTrace]
  refine ⟨3209258951230994918154697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4279011934974659890872929 3209258951230994918154697)
  ·
    refine ⟨2406944213423246188616023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3209258951230994918154697 2406944213423246188616023)
    ·
      refine ⟨3610416320134869282924035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2406944213423246188616023 3610416320134869282924035)
      ·
        refine ⟨5415624480202303924386053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3610416320134869282924035 5415624480202303924386053)
        ·
          refine ⟨1015429590037931985822385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5415624480202303924386053 1015429590037931985822385)
          ·
            refine ⟨761572192528448989366789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1015429590037931985822385 761572192528448989366789)
            ·
              refine ⟨142794786099084185506273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 761572192528448989366789 142794786099084185506273)
              ·
                refine ⟨107096089574313139129705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142794786099084185506273 107096089574313139129705)
                ·
                  refine ⟨80322067180734854347279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107096089574313139129705 80322067180734854347279)
                  ·
                    rfl

theorem cell20_175980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_175980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_175980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_175980 prefixEnd_175980 := by exact prefixLift 175980
  have htrace : WordTrace (prefixWord ++ tailWord_175980) baseStart_175980 baseEnd_175980 := by
    simpa [prefixWord, tailWord_175980, baseEnd_175980] using wordTrace_append hprefix tailTrace_175980
  have hstable : (prefixWord ++ tailWord_175980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175980).length < 2 ^ (prefixWord ++ tailWord_175980).sum := by decide
  have hdescent : baseEnd_175980 < baseStart_175980 := by decide
  rcases family_descends (prefixWord ++ tailWord_175980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176018 : List Nat := [3, 2, 3, 2, 1, 1, 1, 5, 2]
def baseStart_176018 : Nat := 118140960795 + 176018 * 2 ^ 59
def prefixEnd_176018 : Nat := 4983230072969 + 3 ^ 40 * 176018 * 2
def baseEnd_176018 : Nat := 80339411416175611080457

theorem tailTrace_176018 : CollatzResearch.WordTrace tailWord_176018 prefixEnd_176018 80339411416175611080457 := by
  unfold tailWord_176018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604975969081080581548177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4279935917549548217461805 1604975969081080581548177)
  ·
    refine ⟨1203731976810810436161133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1604975969081080581548177 1203731976810810436161133)
    ·
      refine ⟨451399491304053913560425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1203731976810810436161133 451399491304053913560425)
      ·
        refine ⟨338549618478040435170319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451399491304053913560425 338549618478040435170319)
        ·
          refine ⟨507824427717060652755479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338549618478040435170319 507824427717060652755479)
          ·
            refine ⟨761736641575590979133219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507824427717060652755479 761736641575590979133219)
            ·
              refine ⟨1142604962363386468699829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761736641575590979133219 1142604962363386468699829)
              ·
                refine ⟨107119215221567481440609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1142604962363386468699829 107119215221567481440609)
                ·
                  refine ⟨80339411416175611080457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107119215221567481440609 80339411416175611080457)
                  ·
                    rfl

theorem cell20_176018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_176018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176018 prefixEnd_176018 := by exact prefixLift 176018
  have htrace : WordTrace (prefixWord ++ tailWord_176018) baseStart_176018 baseEnd_176018 := by
    simpa [prefixWord, tailWord_176018, baseEnd_176018] using wordTrace_append hprefix tailTrace_176018
  have hstable : (prefixWord ++ tailWord_176018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176018).length < 2 ^ (prefixWord ++ tailWord_176018).sum := by decide
  have hdescent : baseEnd_176018 < baseStart_176018 := by decide
  rcases family_descends (prefixWord ++ tailWord_176018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176029 : List Nat := [1, 4, 2, 1, 2, 3, 7]
def baseStart_176029 : Nat := 118140960795 + 176029 * 2 ^ 59
def prefixEnd_176029 : Nat := 4983230072969 + 3 ^ 40 * 176029 * 2
def baseEnd_176029 : Nat := 8927159123989829079305

theorem tailTrace_176029 : CollatzResearch.WordTrace tailWord_176029 prefixEnd_176029 8927159123989829079305 := by
  unfold tailWord_176029
  simp only [CollatzResearch.WordTrace]
  refine ⟨6420305079284471204843141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4280203386189647469895427 6420305079284471204843141)
  ·
    refine ⟨1203807202365838350908089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6420305079284471204843141 1203807202365838350908089)
    ·
      refine ⟨902855401774378763181067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1203807202365838350908089 902855401774378763181067)
      ·
        refine ⟨1354283102661568144771601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902855401774378763181067 1354283102661568144771601)
        ·
          refine ⟨1015712326996176108578701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1354283102661568144771601 1015712326996176108578701)
          ·
            refine ⟨380892122623566040717013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1015712326996176108578701 380892122623566040717013)
            ·
              refine ⟨8927159123989829079305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 380892122623566040717013 8927159123989829079305)
              ·
                rfl

theorem cell20_176029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 7].length) (baseStart_176029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176029 prefixEnd_176029 := by exact prefixLift 176029
  have htrace : WordTrace (prefixWord ++ tailWord_176029) baseStart_176029 baseEnd_176029 := by
    simpa [prefixWord, tailWord_176029, baseEnd_176029] using wordTrace_append hprefix tailTrace_176029
  have hstable : (prefixWord ++ tailWord_176029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176029).length < 2 ^ (prefixWord ++ tailWord_176029).sum := by decide
  have hdescent : baseEnd_176029 < baseStart_176029 := by decide
  rcases family_descends (prefixWord ++ tailWord_176029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176039 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 4]
def baseStart_176039 : Nat := 118140960795 + 176039 * 2 ^ 59
def prefixEnd_176039 : Nat := 4983230072969 + 3 ^ 40 * 176039 * 2
def baseEnd_176039 : Nat := 80348996388392871380371

theorem tailTrace_176039 : CollatzResearch.WordTrace tailWord_176039 prefixEnd_176039 80348996388392871380371 := by
  unfold tailWord_176039
  simp only [CollatzResearch.WordTrace]
  refine ⟨6420669809248242912707171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4280446539498828608471447 6420669809248242912707171)
  ·
    refine ⟨9631004713872364369060757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6420669809248242912707171 9631004713872364369060757)
    ·
      refine ⟨451453345962767079799723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9631004713872364369060757 451453345962767079799723)
      ·
        refine ⟨677180018944150619699585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451453345962767079799723 677180018944150619699585)
        ·
          refine ⟨507885014208112964774689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677180018944150619699585 507885014208112964774689)
          ·
            refine ⟨380913760656084723581017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507885014208112964774689 380913760656084723581017)
            ·
              refine ⟨285685320492063542685763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380913760656084723581017 285685320492063542685763)
              ·
                refine ⟨428527980738095314028645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285685320492063542685763 428527980738095314028645)
                ·
                  refine ⟨80348996388392871380371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 428527980738095314028645 80348996388392871380371)
                  ·
                    rfl

theorem cell20_176039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_176039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176039 prefixEnd_176039 := by exact prefixLift 176039
  have htrace : WordTrace (prefixWord ++ tailWord_176039) baseStart_176039 baseEnd_176039 := by
    simpa [prefixWord, tailWord_176039, baseEnd_176039] using wordTrace_append hprefix tailTrace_176039
  have hstable : (prefixWord ++ tailWord_176039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176039).length < 2 ^ (prefixWord ++ tailWord_176039).sum := by decide
  have hdescent : baseEnd_176039 < baseStart_176039 := by decide
  rcases family_descends (prefixWord ++ tailWord_176039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176074 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_176074 : Nat := 118140960795 + 176074 * 2 ^ 59
def prefixEnd_176074 : Nat := 4983230072969 + 3 ^ 40 * 176074 * 2
def baseEnd_176074 : Nat := 80364971342088305213561

theorem tailTrace_176074 : CollatzResearch.WordTrace tailWord_176074 prefixEnd_176074 80364971342088305213561 := by
  unfold tailWord_176074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605486591030360972557819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4281297576080962593487517 1605486591030360972557819)
  ·
    refine ⟨2408229886545541458836729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1605486591030360972557819 2408229886545541458836729)
    ·
      refine ⟨1806172414909156094127547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2408229886545541458836729 1806172414909156094127547)
      ·
        refine ⟨2709258622363734141191321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806172414909156094127547 2709258622363734141191321)
        ·
          refine ⟨2031943966772800605893491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2709258622363734141191321 2031943966772800605893491)
          ·
            refine ⟨3047915950159200908840237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031943966772800605893491 3047915950159200908840237)
            ·
              refine ⟨1142968481309700340815089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3047915950159200908840237 1142968481309700340815089)
              ·
                refine ⟨857226360982275255611317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142968481309700340815089 857226360982275255611317)
                ·
                  refine ⟨80364971342088305213561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 857226360982275255611317 80364971342088305213561)
                  ·
                    rfl

theorem cell20_176074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_176074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176074 prefixEnd_176074 := by exact prefixLift 176074
  have htrace : WordTrace (prefixWord ++ tailWord_176074) baseStart_176074 baseEnd_176074 := by
    simpa [prefixWord, tailWord_176074, baseEnd_176074] using wordTrace_append hprefix tailTrace_176074
  have hstable : (prefixWord ++ tailWord_176074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176074).length < 2 ^ (prefixWord ++ tailWord_176074).sum := by decide
  have hdescent : baseEnd_176074 < baseStart_176074 := by decide
  rcases family_descends (prefixWord ++ tailWord_176074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176149 : List Nat := [1, 3, 2, 1, 5, 2, 2, 2, 2]
def baseStart_176149 : Nat := 118140960795 + 176149 * 2 ^ 59
def prefixEnd_176149 : Nat := 4983230072969 + 3 ^ 40 * 176149 * 2
def baseEnd_176149 : Nat := 80399203385721377713255

theorem tailTrace_176149 : CollatzResearch.WordTrace tailWord_176149 prefixEnd_176149 80399203385721377713255 := by
  unfold tailWord_176149
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424681838849731699211501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4283121225899821132807667 6424681838849731699211501)
  ·
    refine ⟨2409255689568649387204313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6424681838849731699211501 2409255689568649387204313)
    ·
      refine ⟨1806941767176487040403235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2409255689568649387204313 1806941767176487040403235)
      ·
        refine ⟨2710412650764730560604853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806941767176487040403235 2710412650764730560604853)
        ·
          refine ⟨254101186009193490056705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2710412650764730560604853 254101186009193490056705)
          ·
            refine ⟨190575889506895117542529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254101186009193490056705 190575889506895117542529)
            ·
              refine ⟨142931917130171338156897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190575889506895117542529 142931917130171338156897)
              ·
                refine ⟨107198937847628503617673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142931917130171338156897 107198937847628503617673)
                ·
                  refine ⟨80399203385721377713255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107198937847628503617673 80399203385721377713255)
                  ·
                    rfl

theorem cell20_176149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_176149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176149 prefixEnd_176149 := by exact prefixLift 176149
  have htrace : WordTrace (prefixWord ++ tailWord_176149) baseStart_176149 baseEnd_176149 := by
    simpa [prefixWord, tailWord_176149, baseEnd_176149] using wordTrace_append hprefix tailTrace_176149
  have hstable : (prefixWord ++ tailWord_176149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176149).length < 2 ^ (prefixWord ++ tailWord_176149).sum := by decide
  have hdescent : baseEnd_176149 < baseStart_176149 := by decide
  rcases family_descends (prefixWord ++ tailWord_176149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176174 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_176174 : Nat := 118140960795 + 176174 * 2 ^ 59
def prefixEnd_176174 : Nat := 4983230072969 + 3 ^ 40 * 176174 * 2
def baseEnd_176174 : Nat := 80410614066932401879819

theorem tailTrace_176174 : CollatzResearch.WordTrace tailWord_176174 prefixEnd_176174 80410614066932401879819 := by
  unfold tailWord_176174
  simp only [CollatzResearch.WordTrace]
  refine ⟨803199207969895121108947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4283729109172773979247717 803199207969895121108947)
  ·
    refine ⟨1204798811954842681663421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 803199207969895121108947 1204798811954842681663421)
    ·
      refine ⟨451799554483066005623783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1204798811954842681663421 451799554483066005623783)
      ·
        refine ⟨677699331724599008435675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451799554483066005623783 677699331724599008435675)
        ·
          refine ⟨1016548997586898512653513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677699331724599008435675 1016548997586898512653513)
          ·
            refine ⟨762411748190173884490135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1016548997586898512653513 762411748190173884490135)
            ·
              refine ⟨1143617622285260826735203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762411748190173884490135 1143617622285260826735203)
              ·
                refine ⟨1715426433427891240102805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143617622285260826735203 1715426433427891240102805)
                ·
                  refine ⟨80410614066932401879819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1715426433427891240102805 80410614066932401879819)
                  ·
                    rfl

theorem cell20_176174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_176174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176174 prefixEnd_176174 := by exact prefixLift 176174
  have htrace : WordTrace (prefixWord ++ tailWord_176174) baseStart_176174 baseEnd_176174 := by
    simpa [prefixWord, tailWord_176174, baseEnd_176174] using wordTrace_append hprefix tailTrace_176174
  have hstable : (prefixWord ++ tailWord_176174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176174).length < 2 ^ (prefixWord ++ tailWord_176174).sum := by decide
  have hdescent : baseEnd_176174 < baseStart_176174 := by decide
  rcases family_descends (prefixWord ++ tailWord_176174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176188 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_176188 : Nat := 118140960795 + 176188 * 2 ^ 59
def prefixEnd_176188 : Nat := 4983230072969 + 3 ^ 40 * 176188 * 2
def baseEnd_176188 : Nat := 80417004048410575413095

theorem tailTrace_176188 : CollatzResearch.WordTrace tailWord_176188 prefixEnd_176188 80417004048410575413095 := by
  unfold tailWord_176188
  simp only [CollatzResearch.WordTrace]
  refine ⟨3213052142854220679940609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4284069523805627573254145 3213052142854220679940609)
  ·
    refine ⟨2409789107140665509955457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3213052142854220679940609 2409789107140665509955457)
    ·
      refine ⟨1807341830355499132466593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2409789107140665509955457 1807341830355499132466593)
      ·
        refine ⟨1355506372766624349349945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1807341830355499132466593 1355506372766624349349945)
        ·
          refine ⟨1016629779574968262012459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1355506372766624349349945 1016629779574968262012459)
          ·
            refine ⟨1524944669362452393018689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016629779574968262012459 1524944669362452393018689)
            ·
              refine ⟨1143708502021839294764017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1524944669362452393018689 1143708502021839294764017)
              ·
                refine ⟨857781376516379471073013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1143708502021839294764017 857781376516379471073013)
                ·
                  refine ⟨80417004048410575413095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 857781376516379471073013 80417004048410575413095)
                  ·
                    rfl

theorem cell20_176188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_176188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176188 prefixEnd_176188 := by exact prefixLift 176188
  have htrace : WordTrace (prefixWord ++ tailWord_176188) baseStart_176188 baseEnd_176188 := by
    simpa [prefixWord, tailWord_176188, baseEnd_176188] using wordTrace_append hprefix tailTrace_176188
  have hstable : (prefixWord ++ tailWord_176188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176188).length < 2 ^ (prefixWord ++ tailWord_176188).sum := by decide
  have hdescent : baseEnd_176188 < baseStart_176188 := by decide
  rcases family_descends (prefixWord ++ tailWord_176188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176198 : List Nat := [6, 1, 1, 1, 1, 1, 9]
def baseStart_176198 : Nat := 118140960795 + 176198 * 2 ^ 59
def prefixEnd_176198 : Nat := 4983230072969 + 3 ^ 40 * 176198 * 2
def baseEnd_176198 : Nat := 8935729813432776119969

theorem tailTrace_176198 : CollatzResearch.WordTrace tailWord_176198 prefixEnd_176198 8935729813432776119969 := by
  unfold tailWord_176198
  simp only [CollatzResearch.WordTrace]
  refine ⟨200827156739756658367039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4284312677114808711830165 200827156739756658367039)
  ·
    refine ⟨301240735109634987550559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200827156739756658367039 301240735109634987550559)
    ·
      refine ⟨451861102664452481325839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301240735109634987550559 451861102664452481325839)
      ·
        refine ⟨677791653996678721988759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451861102664452481325839 677791653996678721988759)
        ·
          refine ⟨1016687480995018082983139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677791653996678721988759 1016687480995018082983139)
          ·
            refine ⟨1525031221492527124474709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016687480995018082983139 1525031221492527124474709)
            ·
              refine ⟨8935729813432776119969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1525031221492527124474709 8935729813432776119969)
              ·
                rfl

theorem cell20_176198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 9].length) (baseStart_176198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176198 prefixEnd_176198 := by exact prefixLift 176198
  have htrace : WordTrace (prefixWord ++ tailWord_176198) baseStart_176198 baseEnd_176198 := by
    simpa [prefixWord, tailWord_176198, baseEnd_176198] using wordTrace_append hprefix tailTrace_176198
  have hstable : (prefixWord ++ tailWord_176198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176198).length < 2 ^ (prefixWord ++ tailWord_176198).sum := by decide
  have hdescent : baseEnd_176198 < baseStart_176198 := by decide
  rcases family_descends (prefixWord ++ tailWord_176198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176205 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 5]
def baseStart_176205 : Nat := 118140960795 + 176205 * 2 ^ 59
def prefixEnd_176205 : Nat := 4983230072969 + 3 ^ 40 * 176205 * 2
def baseEnd_176205 : Nat := 80424763311634071846359

theorem tailTrace_176205 : CollatzResearch.WordTrace tailWord_176205 prefixEnd_176205 80424763311634071846359 := by
  unfold tailWord_176205
  simp only [CollatzResearch.WordTrace]
  refine ⟨6426724326646853263250069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4284482884431235508833379 6426724326646853263250069)
  ·
    refine ⟨301252702811571246714847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6426724326646853263250069 301252702811571246714847)
    ·
      refine ⟨451879054217356870072271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301252702811571246714847 451879054217356870072271)
      ·
        refine ⟨677818581326035305108407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451879054217356870072271 677818581326035305108407)
        ·
          refine ⟨1016727871989052957662611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677818581326035305108407 1016727871989052957662611)
          ·
            refine ⟨1525091807983579436493917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016727871989052957662611 1525091807983579436493917)
            ·
              refine ⟨571909427993842288685219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1525091807983579436493917 571909427993842288685219)
              ·
                refine ⟨857864141990763433027829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571909427993842288685219 857864141990763433027829)
                ·
                  refine ⟨80424763311634071846359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 857864141990763433027829 80424763311634071846359)
                  ·
                    rfl

theorem cell20_176205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_176205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176205 prefixEnd_176205 := by exact prefixLift 176205
  have htrace : WordTrace (prefixWord ++ tailWord_176205) baseStart_176205 baseEnd_176205 := by
    simpa [prefixWord, tailWord_176205, baseEnd_176205] using wordTrace_append hprefix tailTrace_176205
  have hstable : (prefixWord ++ tailWord_176205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176205).length < 2 ^ (prefixWord ++ tailWord_176205).sum := by decide
  have hdescent : baseEnd_176205 < baseStart_176205 := by decide
  rcases family_descends (prefixWord ++ tailWord_176205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176233 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_176233 : Nat := 118140960795 + 176233 * 2 ^ 59
def prefixEnd_176233 : Nat := 4983230072969 + 3 ^ 40 * 176233 * 2
def baseEnd_176233 : Nat := 80437543274590418912911

theorem tailTrace_176233 : CollatzResearch.WordTrace tailWord_176233 prefixEnd_176233 80437543274590418912911 := by
  unfold tailWord_176233
  simp only [CollatzResearch.WordTrace]
  refine ⟨6427745570545414045269353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4285163713696942696846235 6427745570545414045269353)
  ·
    refine ⟨4820809177909060533952015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6427745570545414045269353 4820809177909060533952015)
    ·
      refine ⟨7231213766863590800928023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4820809177909060533952015 7231213766863590800928023)
      ·
        refine ⟨10846820650295386201392035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7231213766863590800928023 10846820650295386201392035)
        ·
          refine ⟨16270230975443079302088053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10846820650295386201392035 16270230975443079302088053)
          ·
            refine ⟨1525334153947788684570755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16270230975443079302088053 1525334153947788684570755)
            ·
              refine ⟨2288001230921683026856133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525334153947788684570755 2288001230921683026856133)
              ·
                refine ⟨429000230797815567535525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2288001230921683026856133 429000230797815567535525)
                ·
                  refine ⟨80437543274590418912911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 429000230797815567535525 80437543274590418912911)
                  ·
                    rfl

theorem cell20_176233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_176233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176233 prefixEnd_176233 := by exact prefixLift 176233
  have htrace : WordTrace (prefixWord ++ tailWord_176233) baseStart_176233 baseEnd_176233 := by
    simpa [prefixWord, tailWord_176233, baseEnd_176233] using wordTrace_append hprefix tailTrace_176233
  have hstable : (prefixWord ++ tailWord_176233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176233).length < 2 ^ (prefixWord ++ tailWord_176233).sum := by decide
  have hdescent : baseEnd_176233 < baseStart_176233 := by decide
  rcases family_descends (prefixWord ++ tailWord_176233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176236 : List Nat := [2, 2, 1, 1, 3, 5, 2, 4]
def baseStart_176236 : Nat := 118140960795 + 176236 * 2 ^ 59
def prefixEnd_176236 : Nat := 4983230072969 + 3 ^ 40 * 176236 * 2
def baseEnd_176236 : Nat := 26812970852111913937633

theorem tailTrace_176236 : CollatzResearch.WordTrace tailWord_176236 prefixEnd_176236 26812970852111913937633 := by
  unfold tailWord_176236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3213927494767272778814281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4285236659689697038419041 3213927494767272778814281)
  ·
    refine ⟨2410445621075454584110711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3213927494767272778814281 2410445621075454584110711)
    ·
      refine ⟨3615668431613181876166067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410445621075454584110711 3615668431613181876166067)
      ·
        refine ⟨5423502647419772814249101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615668431613181876166067 5423502647419772814249101)
        ·
          refine ⟨2033813492782414805343413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5423502647419772814249101 2033813492782414805343413)
          ·
            refine ⟨190670014948351388000945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2033813492782414805343413 190670014948351388000945)
            ·
              refine ⟨143002511211263541000709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190670014948351388000945 143002511211263541000709)
              ·
                refine ⟨26812970852111913937633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143002511211263541000709 26812970852111913937633)
                ·
                  rfl

theorem cell20_176236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_176236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176236 prefixEnd_176236 := by exact prefixLift 176236
  have htrace : WordTrace (prefixWord ++ tailWord_176236) baseStart_176236 baseEnd_176236 := by
    simpa [prefixWord, tailWord_176236, baseEnd_176236] using wordTrace_append hprefix tailTrace_176236
  have hstable : (prefixWord ++ tailWord_176236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176236).length < 2 ^ (prefixWord ++ tailWord_176236).sum := by decide
  have hdescent : baseEnd_176236 < baseStart_176236 := by decide
  rcases family_descends (prefixWord ++ tailWord_176236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176246 : List Nat := [5, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_176246 : Nat := 118140960795 + 176246 * 2 ^ 59
def prefixEnd_176246 : Nat := 4983230072969 + 3 ^ 40 * 176246 * 2
def baseEnd_176246 : Nat := 80443476828820151479525

theorem tailTrace_176246 : CollatzResearch.WordTrace tailWord_176246 prefixEnd_176246 80443476828820151479525 := by
  unfold tailWord_176246
  simp only [CollatzResearch.WordTrace]
  refine ⟨401763732468644829093287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4285479812998878176995061 401763732468644829093287)
  ·
    refine ⟨602645598702967243639931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 401763732468644829093287 602645598702967243639931)
    ·
      refine ⟨903968398054450865459897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 602645598702967243639931 903968398054450865459897)
      ·
        refine ⟨677976298540838149094923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 903968398054450865459897 677976298540838149094923)
        ·
          refine ⟨1016964447811257223642385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677976298540838149094923 1016964447811257223642385)
          ·
            refine ⟨762723335858442917731789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1016964447811257223642385 762723335858442917731789)
            ·
              refine ⟨286021250946916094149421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 762723335858442917731789 286021250946916094149421)
              ·
                refine ⟨107257969105093535306033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286021250946916094149421 107257969105093535306033)
                ·
                  refine ⟨80443476828820151479525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107257969105093535306033 80443476828820151479525)
                  ·
                    rfl

theorem cell20_176246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_176246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176246 prefixEnd_176246 := by exact prefixLift 176246
  have htrace : WordTrace (prefixWord ++ tailWord_176246) baseStart_176246 baseEnd_176246 := by
    simpa [prefixWord, tailWord_176246, baseEnd_176246] using wordTrace_append hprefix tailTrace_176246
  have hstable : (prefixWord ++ tailWord_176246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176246).length < 2 ^ (prefixWord ++ tailWord_176246).sum := by decide
  have hdescent : baseEnd_176246 < baseStart_176246 := by decide
  rcases family_descends (prefixWord ++ tailWord_176246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176308 : List Nat := [2, 5, 3, 1, 2, 7]
def baseStart_176308 : Nat := 118140960795 + 176308 * 2 ^ 59
def prefixEnd_176308 : Nat := 4983230072969 + 3 ^ 40 * 176308 * 2
def baseEnd_176308 : Nat := 2980436122897166348615

theorem tailTrace_176308 : CollatzResearch.WordTrace tailWord_176308 prefixEnd_176308 2980436122897166348615 := by
  unfold tailWord_176308
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215240522636850927124789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4286987363515801236166385 3215240522636850927124789)
  ·
    refine ⟨301428798997204774417949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3215240522636850927124789 301428798997204774417949)
    ·
      refine ⟨113035799623951790406731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301428798997204774417949 113035799623951790406731)
      ·
        refine ⟨169553699435927685610097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113035799623951790406731 169553699435927685610097)
        ·
          refine ⟨127165274576945764207573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169553699435927685610097 127165274576945764207573)
          ·
            refine ⟨2980436122897166348615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 127165274576945764207573 2980436122897166348615)
            ·
              rfl

theorem cell20_176308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 7].length) (baseStart_176308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176308 prefixEnd_176308 := by exact prefixLift 176308
  have htrace : WordTrace (prefixWord ++ tailWord_176308) baseStart_176308 baseEnd_176308 := by
    simpa [prefixWord, tailWord_176308, baseEnd_176308] using wordTrace_append hprefix tailTrace_176308
  have hstable : (prefixWord ++ tailWord_176308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176308).length < 2 ^ (prefixWord ++ tailWord_176308).sum := by decide
  have hdescent : baseEnd_176308 < baseStart_176308 := by decide
  rcases family_descends (prefixWord ++ tailWord_176308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176316 : List Nat := [2, 2, 2, 3, 11]
def baseStart_176316 : Nat := 118140960795 + 176316 * 2 ^ 59
def prefixEnd_176316 : Nat := 4983230072969 + 3 ^ 40 * 176316 * 2
def baseEnd_176316 : Nat := 993523786866802705505

theorem tailTrace_176316 : CollatzResearch.WordTrace tailWord_176316 prefixEnd_176316 993523786866802705505 := by
  unfold tailWord_176316
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215386414622359610270401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4287181886163146147027201 3215386414622359610270401)
  ·
    refine ⟨2411539810966769707702801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3215386414622359610270401 2411539810966769707702801)
    ·
      refine ⟨1808654858225077280777101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2411539810966769707702801 1808654858225077280777101)
      ·
        refine ⟨678245571834403980291413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1808654858225077280777101 678245571834403980291413)
        ·
          refine ⟨993523786866802705505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 678245571834403980291413 993523786866802705505)
          ·
            rfl

theorem cell20_176316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 11].length) (baseStart_176316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176316 prefixEnd_176316 := by exact prefixLift 176316
  have htrace : WordTrace (prefixWord ++ tailWord_176316) baseStart_176316 baseEnd_176316 := by
    simpa [prefixWord, tailWord_176316, baseEnd_176316] using wordTrace_append hprefix tailTrace_176316
  have hstable : (prefixWord ++ tailWord_176316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176316).length < 2 ^ (prefixWord ++ tailWord_176316).sum := by decide
  have hdescent : baseEnd_176316 < baseStart_176316 := by decide
  rcases family_descends (prefixWord ++ tailWord_176316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
