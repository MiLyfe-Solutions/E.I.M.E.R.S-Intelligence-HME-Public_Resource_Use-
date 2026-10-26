import V185TrunkScan23Chunk0283

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1678927 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 3]
def baseStart_1678927 : Nat := 118140960795 + 1678927 * 2 ^ 59
def prefixEnd_1678927 : Nat := 4983230072969 + 3 ^ 40 * 1678927 * 2
def baseEnd_1678927 : Nat := 862096534811257924091261

theorem tailTrace_1678927 : CollatzResearch.WordTrace tailWord_1678927 prefixEnd_1678927 862096534811257924091261 := by
  unfold tailWord_1678927
  simp only [CollatzResearch.WordTrace]
  refine ⟨61235498388541691748339035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40823665592361127832226023 61235498388541691748339035)
  ·
    refine ⟨91853247582812537622508553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61235498388541691748339035 91853247582812537622508553)
    ·
      refine ⟨68889935687109403216881415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91853247582812537622508553 68889935687109403216881415)
      ·
        refine ⟨103334903530664104825322123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68889935687109403216881415 103334903530664104825322123)
        ·
          refine ⟨155002355295996157237983185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103334903530664104825322123 155002355295996157237983185)
          ·
            refine ⟨116251766471997117928487389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155002355295996157237983185 116251766471997117928487389)
            ·
              refine ⟨43594412426998919223182771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116251766471997117928487389 43594412426998919223182771)
              ·
                refine ⟨65391618640498378834774157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43594412426998919223182771 65391618640498378834774157)
                ·
                  refine ⟨24521856990186892063040309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65391618640498378834774157 24521856990186892063040309)
                  ·
                    refine ⟨2298924092830021130910029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24521856990186892063040309 2298924092830021130910029)
                    ·
                      refine ⟨862096534811257924091261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2298924092830021130910029 862096534811257924091261)
                      ·
                        rfl

theorem cell23_1678927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 3].length) (baseStart_1678927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678927 prefixEnd_1678927 := by exact prefixLift 1678927
  have htrace : WordTrace (prefixWord ++ tailWord_1678927) baseStart_1678927 baseEnd_1678927 := by
    simpa [prefixWord, tailWord_1678927, baseEnd_1678927] using wordTrace_append hprefix tailTrace_1678927
  have hstable : (prefixWord ++ tailWord_1678927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678927).length < 2 ^ (prefixWord ++ tailWord_1678927).sum := by decide
  have hdescent : baseEnd_1678927 < baseStart_1678927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678997 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_1678997 : Nat := 118140960795 + 1678997 * 2 ^ 59
def prefixEnd_1678997 : Nat := 4983230072969 + 3 ^ 40 * 1678997 * 2
def baseEnd_1678997 : Nat := 862132478457072650215939

theorem tailTrace_1678997 : CollatzResearch.WordTrace tailWord_1678997 prefixEnd_1678997 862132478457072650215939 := by
  unfold tailWord_1678997
  simp only [CollatzResearch.WordTrace]
  refine ⟨61238051498288093703387245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40825367665525395802258163 61238051498288093703387245)
  ·
    refine ⟨22964269311858035138770217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61238051498288093703387245 22964269311858035138770217)
    ·
      refine ⟨17223201983893526354077663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22964269311858035138770217 17223201983893526354077663)
      ·
        refine ⟨25834802975840289531116495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17223201983893526354077663 25834802975840289531116495)
        ·
          refine ⟨38752204463760434296674743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25834802975840289531116495 38752204463760434296674743)
          ·
            refine ⟨58128306695640651445012115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38752204463760434296674743 58128306695640651445012115)
            ·
              refine ⟨87192460043460977167518173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58128306695640651445012115 87192460043460977167518173)
              ·
                refine ⟨32697172516297866437819315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87192460043460977167518173 32697172516297866437819315)
                ·
                  refine ⟨49045758774446799656728973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32697172516297866437819315 49045758774446799656728973)
                  ·
                    refine ⟨18392159540417549871273365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49045758774446799656728973 18392159540417549871273365)
                    ·
                      refine ⟨862132478457072650215939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18392159540417549871273365 862132478457072650215939)
                      ·
                        rfl

theorem cell23_1678997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_1678997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678997 prefixEnd_1678997 := by exact prefixLift 1678997
  have htrace : WordTrace (prefixWord ++ tailWord_1678997) baseStart_1678997 baseEnd_1678997 := by
    simpa [prefixWord, tailWord_1678997, baseEnd_1678997] using wordTrace_append hprefix tailTrace_1678997
  have hstable : (prefixWord ++ tailWord_1678997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678997).length < 2 ^ (prefixWord ++ tailWord_1678997).sum := by decide
  have hdescent : baseEnd_1678997 < baseStart_1678997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679021 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_1679021 : Nat := 118140960795 + 1679021 * 2 ^ 59
def prefixEnd_1679021 : Nat := 4983230072969 + 3 ^ 40 * 1679021 * 2
def baseEnd_1679021 : Nat := 862144801992780556315829

theorem tailTrace_1679021 : CollatzResearch.WordTrace tailWord_1679021 prefixEnd_1679021 862144801992780556315829 := by
  unfold tailWord_1679021
  simp only [CollatzResearch.WordTrace]
  refine ⟨61238926850201145802260917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40825951233467430534840611 61238926850201145802260917)
  ·
    refine ⟨5741149392206357418961961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61238926850201145802260917 5741149392206357418961961)
    ·
      refine ⟨4305862044154768064221471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5741149392206357418961961 4305862044154768064221471)
      ·
        refine ⟨6458793066232152096332207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4305862044154768064221471 6458793066232152096332207)
        ·
          refine ⟨9688189599348228144498311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6458793066232152096332207 9688189599348228144498311)
          ·
            refine ⟨14532284399022342216747467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9688189599348228144498311 14532284399022342216747467)
            ·
              refine ⟨21798426598533513325121201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14532284399022342216747467 21798426598533513325121201)
              ·
                refine ⟨16348819948900134993840901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21798426598533513325121201 16348819948900134993840901)
                ·
                  refine ⟨3065403740418775311345169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16348819948900134993840901 3065403740418775311345169)
                  ·
                    refine ⟨2299052805314081483508877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3065403740418775311345169 2299052805314081483508877)
                    ·
                      refine ⟨862144801992780556315829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299052805314081483508877 862144801992780556315829)
                      ·
                        rfl

theorem cell23_1679021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_1679021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679021 prefixEnd_1679021 := by exact prefixLift 1679021
  have htrace : WordTrace (prefixWord ++ tailWord_1679021) baseStart_1679021 baseEnd_1679021 := by
    simpa [prefixWord, tailWord_1679021, baseEnd_1679021] using wordTrace_append hprefix tailTrace_1679021
  have hstable : (prefixWord ++ tailWord_1679021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679021).length < 2 ^ (prefixWord ++ tailWord_1679021).sum := by decide
  have hdescent : baseEnd_1679021 < baseStart_1679021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679038 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_1679038 : Nat := 118140960795 + 1679038 * 2 ^ 59
def prefixEnd_1679038 : Nat := 4983230072969 + 3 ^ 40 * 1679038 * 2
def baseEnd_1679038 : Nat := 862153531163906989803251

theorem tailTrace_1679038 : CollatzResearch.WordTrace tailWord_1679038 prefixEnd_1679038 862153531163906989803251 := by
  unfold tailWord_1679038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654943361392444713203721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40826364594093038470419845 7654943361392444713203721)
  ·
    refine ⟨5741207521044333534902791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7654943361392444713203721 5741207521044333534902791)
    ·
      refine ⟨8611811281566500302354187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5741207521044333534902791 8611811281566500302354187)
      ·
        refine ⟨12917716922349750453531281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8611811281566500302354187 12917716922349750453531281)
        ·
          refine ⟨9688287691762312840148461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12917716922349750453531281 9688287691762312840148461)
          ·
            refine ⟨3633107884410867315055673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9688287691762312840148461 3633107884410867315055673)
            ·
              refine ⟨2724830913308150486291755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3633107884410867315055673 2724830913308150486291755)
              ·
                refine ⟨4087246369962225729437633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724830913308150486291755 4087246369962225729437633)
                ·
                  refine ⟨3065434777471669297078225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4087246369962225729437633 3065434777471669297078225)
                  ·
                    refine ⟨2299076083103751972808669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3065434777471669297078225 2299076083103751972808669)
                    ·
                      refine ⟨862153531163906989803251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299076083103751972808669 862153531163906989803251)
                      ·
                        rfl

theorem cell23_1679038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_1679038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679038 prefixEnd_1679038 := by exact prefixLift 1679038
  have htrace : WordTrace (prefixWord ++ tailWord_1679038) baseStart_1679038 baseEnd_1679038 := by
    simpa [prefixWord, tailWord_1679038, baseEnd_1679038] using wordTrace_append hprefix tailTrace_1679038
  have hstable : (prefixWord ++ tailWord_1679038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679038).length < 2 ^ (prefixWord ++ tailWord_1679038).sum := by decide
  have hdescent : baseEnd_1679038 < baseStart_1679038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679067 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 12]
def baseStart_1679067 : Nat := 118140960795 + 1679067 * 2 ^ 59
def prefixEnd_1679067 : Nat := 4983230072969 + 3 ^ 40 * 1679067 * 2
def baseEnd_1679067 : Nat := 287389474034295792113539

theorem tailTrace_1679067 : CollatzResearch.WordTrace tailWord_1679067 prefixEnd_1679067 287389474034295792113539 := by
  unfold tailWord_1679067
  simp only [CollatzResearch.WordTrace]
  refine ⟨61240604608034495658435455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40827069738689663772290303 61240604608034495658435455)
  ·
    refine ⟨91860906912051743487653183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61240604608034495658435455 91860906912051743487653183)
    ·
      refine ⟨137791360368077615231479775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91860906912051743487653183 137791360368077615231479775)
      ·
        refine ⟨206687040552116422847219663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137791360368077615231479775 206687040552116422847219663)
        ·
          refine ⟨310030560828174634270829495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206687040552116422847219663 310030560828174634270829495)
          ·
            refine ⟨465045841242261951406244243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310030560828174634270829495 465045841242261951406244243)
            ·
              refine ⟨697568761863392927109366365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465045841242261951406244243 697568761863392927109366365)
              ·
                refine ⟨261588285698772347666012387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 697568761863392927109366365 261588285698772347666012387)
                ·
                  refine ⟨392382428548158521499018581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261588285698772347666012387 392382428548158521499018581)
                  ·
                    refine ⟨287389474034295792113539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 392382428548158521499018581 287389474034295792113539)
                    ·
                      rfl

theorem cell23_1679067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 12].length) (baseStart_1679067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679067 prefixEnd_1679067 := by exact prefixLift 1679067
  have htrace : WordTrace (prefixWord ++ tailWord_1679067) baseStart_1679067 baseEnd_1679067 := by
    simpa [prefixWord, tailWord_1679067, baseEnd_1679067] using wordTrace_append hprefix tailTrace_1679067
  have hstable : (prefixWord ++ tailWord_1679067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679067).length < 2 ^ (prefixWord ++ tailWord_1679067).sum := by decide
  have hdescent : baseEnd_1679067 < baseStart_1679067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679084 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_1679084 : Nat := 118140960795 + 1679084 * 2 ^ 59
def prefixEnd_1679084 : Nat := 4983230072969 + 3 ^ 40 * 1679084 * 2
def baseEnd_1679084 : Nat := 287392383758004603276013

theorem tailTrace_1679084 : CollatzResearch.WordTrace tailWord_1679084 prefixEnd_1679084 287392383758004603276013 := by
  unfold tailWord_1679084
  simp only [CollatzResearch.WordTrace]
  refine ⟨30620612324486453780902153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40827483099315271707869537 30620612324486453780902153)
  ·
    refine ⟨22965459243364840335676615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30620612324486453780902153 22965459243364840335676615)
    ·
      refine ⟨34448188865047260503514923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22965459243364840335676615 34448188865047260503514923)
      ·
        refine ⟨51672283297570890755272385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34448188865047260503514923 51672283297570890755272385)
        ·
          refine ⟨38754212473178168066454289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51672283297570890755272385 38754212473178168066454289)
          ·
            refine ⟨29065659354883626049840717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38754212473178168066454289 29065659354883626049840717)
            ·
              refine ⟨10899622258081359768690269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29065659354883626049840717 10899622258081359768690269)
              ·
                refine ⟨4087358346780509913258851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10899622258081359768690269 4087358346780509913258851)
                ·
                  refine ⟨6131037520170764869888277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4087358346780509913258851 6131037520170764869888277)
                  ·
                    refine ⟨287392383758004603276013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6131037520170764869888277 287392383758004603276013)
                    ·
                      rfl

theorem cell23_1679084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_1679084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679084 prefixEnd_1679084 := by exact prefixLift 1679084
  have htrace : WordTrace (prefixWord ++ tailWord_1679084) baseStart_1679084 baseEnd_1679084 := by
    simpa [prefixWord, tailWord_1679084, baseEnd_1679084] using wordTrace_append hprefix tailTrace_1679084
  have hstable : (prefixWord ++ tailWord_1679084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679084).length < 2 ^ (prefixWord ++ tailWord_1679084).sum := by decide
  have hdescent : baseEnd_1679084 < baseStart_1679084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679108 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1679108 : Nat := 118140960795 + 1679108 * 2 ^ 59
def prefixEnd_1679108 : Nat := 4983230072969 + 3 ^ 40 * 1679108 * 2
def baseEnd_1679108 : Nat := 862189474809721715927929

theorem tailTrace_1679108 : CollatzResearch.WordTrace tailWord_1679108 prefixEnd_1679108 862189474809721715927929 := by
  unfold tailWord_1679108
  simp only [CollatzResearch.WordTrace]
  refine ⟨30621050000442979830338989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40828066667257306440451985 30621050000442979830338989)
  ·
    refine ⟨11482893750166117436377121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30621050000442979830338989 11482893750166117436377121)
    ·
      refine ⟨8612170312624588077282841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11482893750166117436377121 8612170312624588077282841)
      ·
        refine ⟨6459127734468441057962131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8612170312624588077282841 6459127734468441057962131)
        ·
          refine ⟨9688691601702661586943197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6459127734468441057962131 9688691601702661586943197)
          ·
            refine ⟨3633259350638498095103699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9688691601702661586943197 3633259350638498095103699)
            ·
              refine ⟨5449889025957747142655549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633259350638498095103699 5449889025957747142655549)
              ·
                refine ⟨2043708384734155178495831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5449889025957747142655549 2043708384734155178495831)
                ·
                  refine ⟨3065562577101232767743747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043708384734155178495831 3065562577101232767743747)
                  ·
                    refine ⟨4598343865651849151615621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3065562577101232767743747 4598343865651849151615621)
                    ·
                      refine ⟨862189474809721715927929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4598343865651849151615621 862189474809721715927929)
                      ·
                        rfl

theorem cell23_1679108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1679108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679108 prefixEnd_1679108 := by exact prefixLift 1679108
  have htrace : WordTrace (prefixWord ++ tailWord_1679108) baseStart_1679108 baseEnd_1679108 := by
    simpa [prefixWord, tailWord_1679108, baseEnd_1679108] using wordTrace_append hprefix tailTrace_1679108
  have hstable : (prefixWord ++ tailWord_1679108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679108).length < 2 ^ (prefixWord ++ tailWord_1679108).sum := by decide
  have hdescent : baseEnd_1679108 < baseStart_1679108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679114 : List Nat := [3, 1, 2, 2, 1, 4, 10]
def baseStart_1679114 : Nat := 118140960795 + 1679114 * 2 ^ 59
def prefixEnd_1679114 : Nat := 4983230072969 + 3 ^ 40 * 1679114 * 2
def baseEnd_1679114 : Nat := 10644352539427761635221

theorem tailTrace_1679114 : CollatzResearch.WordTrace tailWord_1679114 prefixEnd_1679114 10644352539427761635221 := by
  unfold tailWord_1679114
  simp only [CollatzResearch.WordTrace]
  refine ⟨15310579709716055671349099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40828212559242815123597597 15310579709716055671349099)
  ·
    refine ⟨22965869564574083507023649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15310579709716055671349099 22965869564574083507023649)
    ·
      refine ⟨17224402173430562630267737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22965869564574083507023649 17224402173430562630267737)
      ·
        refine ⟨12918301630072921972700803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17224402173430562630267737 12918301630072921972700803)
        ·
          refine ⟨19377452445109382959051205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12918301630072921972700803 19377452445109382959051205)
          ·
            refine ⟨3633272333458009304822101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19377452445109382959051205 3633272333458009304822101)
            ·
              refine ⟨10644352539427761635221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3633272333458009304822101 10644352539427761635221)
              ·
                rfl

theorem cell23_1679114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 10].length) (baseStart_1679114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679114 prefixEnd_1679114 := by exact prefixLift 1679114
  have htrace : WordTrace (prefixWord ++ tailWord_1679114) baseStart_1679114 baseEnd_1679114 := by
    simpa [prefixWord, tailWord_1679114, baseEnd_1679114] using wordTrace_append hprefix tailTrace_1679114
  have hstable : (prefixWord ++ tailWord_1679114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679114).length < 2 ^ (prefixWord ++ tailWord_1679114).sum := by decide
  have hdescent : baseEnd_1679114 < baseStart_1679114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679118 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_1679118 : Nat := 118140960795 + 1679118 * 2 ^ 59
def prefixEnd_1679118 : Nat := 4983230072969 + 3 ^ 40 * 1679118 * 2
def baseEnd_1679118 : Nat := 287398203205422225600961

theorem tailTrace_1679118 : CollatzResearch.WordTrace tailWord_1679118 prefixEnd_1679118 287398203205422225600961 := by
  unfold tailWord_1679118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7655308091356216421067751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40828309820566487579028005 7655308091356216421067751)
  ·
    refine ⟨11482962137034324631601627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7655308091356216421067751 11482962137034324631601627)
    ·
      refine ⟨17224443205551486947402441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11482962137034324631601627 17224443205551486947402441)
      ·
        refine ⟨12918332404163615210551831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17224443205551486947402441 12918332404163615210551831)
        ·
          refine ⟨19377498606245422815827747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12918332404163615210551831 19377498606245422815827747)
          ·
            refine ⟨29066247909368134223741621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19377498606245422815827747 29066247909368134223741621)
            ·
              refine ⟨2724960741503262583475777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29066247909368134223741621 2724960741503262583475777)
              ·
                refine ⟨2043720556127446937606833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2724960741503262583475777 2043720556127446937606833)
                ·
                  refine ⟨1532790417095585203205125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2043720556127446937606833 1532790417095585203205125)
                  ·
                    refine ⟨287398203205422225600961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1532790417095585203205125 287398203205422225600961)
                    ·
                      rfl

theorem cell23_1679118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_1679118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679118 prefixEnd_1679118 := by exact prefixLift 1679118
  have htrace : WordTrace (prefixWord ++ tailWord_1679118) baseStart_1679118 baseEnd_1679118 := by
    simpa [prefixWord, tailWord_1679118, baseEnd_1679118] using wordTrace_append hprefix tailTrace_1679118
  have hstable : (prefixWord ++ tailWord_1679118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679118).length < 2 ^ (prefixWord ++ tailWord_1679118).sum := by decide
  have hdescent : baseEnd_1679118 < baseStart_1679118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679125 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 3, 2, 2]
def baseStart_1679125 : Nat := 118140960795 + 1679125 * 2 ^ 59
def prefixEnd_1679125 : Nat := 4983230072969 + 3 ^ 40 * 1679125 * 2
def baseEnd_1679125 : Nat := 862198203980848149415351

theorem tailTrace_1679125 : CollatzResearch.WordTrace tailWord_1679125 prefixEnd_1679125 862198203980848149415351 := by
  unfold tailWord_1679125
  simp only [CollatzResearch.WordTrace]
  refine ⟨61242720041824371564046829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40828480027882914376031219 61242720041824371564046829)
  ·
    refine ⟨22966020015684139336517561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61242720041824371564046829 22966020015684139336517561)
    ·
      refine ⟨17224515011763104502388171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22966020015684139336517561 17224515011763104502388171)
      ·
        refine ⟨25836772517644656753582257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17224515011763104502388171 25836772517644656753582257)
        ·
          refine ⟨19377579388233492565186693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25836772517644656753582257 19377579388233492565186693)
          ·
            refine ⟨3633296135293779855972505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19377579388233492565186693 3633296135293779855972505)
            ·
              refine ⟨2724972101470334891979379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3633296135293779855972505 2724972101470334891979379)
              ·
                refine ⟨4087458152205502337969069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724972101470334891979379 4087458152205502337969069)
                ·
                  refine ⟨1532796807077063376738401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4087458152205502337969069 1532796807077063376738401)
                  ·
                    refine ⟨1149597605307797532553801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1532796807077063376738401 1149597605307797532553801)
                    ·
                      refine ⟨862198203980848149415351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149597605307797532553801 862198203980848149415351)
                      ·
                        rfl

theorem cell23_1679125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_1679125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679125 prefixEnd_1679125 := by exact prefixLift 1679125
  have htrace : WordTrace (prefixWord ++ tailWord_1679125) baseStart_1679125 baseEnd_1679125 := by
    simpa [prefixWord, tailWord_1679125, baseEnd_1679125] using wordTrace_append hprefix tailTrace_1679125
  have hstable : (prefixWord ++ tailWord_1679125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679125).length < 2 ^ (prefixWord ++ tailWord_1679125).sum := by decide
  have hdescent : baseEnd_1679125 < baseStart_1679125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679184 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_1679184 : Nat := 118140960795 + 1679184 * 2 ^ 59
def prefixEnd_1679184 : Nat := 4983230072969 + 3 ^ 40 * 1679184 * 2
def baseEnd_1679184 : Nat := 862228499339463418577579

theorem tailTrace_1679184 : CollatzResearch.WordTrace tailWord_1679184 prefixEnd_1679184 862228499339463418577579 := by
  unfold tailWord_1679184
  simp only [CollatzResearch.WordTrace]
  refine ⟨30622435974305312320222303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40829914632407083093629737 30622435974305312320222303)
  ·
    refine ⟨45933653961457968480333455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30622435974305312320222303 45933653961457968480333455)
    ·
      refine ⟨68900480942186952720500183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45933653961457968480333455 68900480942186952720500183)
      ·
        refine ⟨103350721413280429080750275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68900480942186952720500183 103350721413280429080750275)
        ·
          refine ⟨155026082119920643621125413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103350721413280429080750275 155026082119920643621125413)
          ·
            refine ⟨29067390397485120678961015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155026082119920643621125413 29067390397485120678961015)
            ·
              refine ⟨43601085596227681018441523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29067390397485120678961015 43601085596227681018441523)
              ·
                refine ⟨65401628394341521527662285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43601085596227681018441523 65401628394341521527662285)
                ·
                  refine ⟨24525610647878070572873357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65401628394341521527662285 24525610647878070572873357)
                  ·
                    refine ⟨9197103992954276464827509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24525610647878070572873357 9197103992954276464827509)
                    ·
                      refine ⟨862228499339463418577579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9197103992954276464827509 862228499339463418577579)
                      ·
                        rfl

theorem cell23_1679184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_1679184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679184 prefixEnd_1679184 := by exact prefixLift 1679184
  have htrace : WordTrace (prefixWord ++ tailWord_1679184) baseStart_1679184 baseEnd_1679184 := by
    simpa [prefixWord, tailWord_1679184, baseEnd_1679184] using wordTrace_append hprefix tailTrace_1679184
  have hstable : (prefixWord ++ tailWord_1679184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679184).length < 2 ^ (prefixWord ++ tailWord_1679184).sum := by decide
  have hdescent : baseEnd_1679184 < baseStart_1679184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679202 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_1679202 : Nat := 118140960795 + 1679202 * 2 ^ 59
def prefixEnd_1679202 : Nat := 4983230072969 + 3 ^ 40 * 1679202 * 2
def baseEnd_1679202 : Nat := 862237741991244348152497

theorem tailTrace_1679202 : CollatzResearch.WordTrace tailWord_1679202 prefixEnd_1679202 862237741991244348152497 := by
  unfold tailWord_1679202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15311382115636353428649965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40830352308363609143066573 15311382115636353428649965)
  ·
    refine ⟨5741768293363632535743737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15311382115636353428649965 5741768293363632535743737)
    ·
      refine ⟨4306326220022724401807803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5741768293363632535743737 4306326220022724401807803)
      ·
        refine ⟨6459489330034086602711705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4306326220022724401807803 6459489330034086602711705)
        ·
          refine ⟨4844616997525564952033779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6459489330034086602711705 4844616997525564952033779)
          ·
            refine ⟨7266925496288347428050669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844616997525564952033779 7266925496288347428050669)
            ·
              refine ⟨2725097061108130285519001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7266925496288347428050669 2725097061108130285519001)
              ·
                refine ⟨2043822795831097714139251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2725097061108130285519001 2043822795831097714139251)
                ·
                  refine ⟨3065734193746646571208877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043822795831097714139251 3065734193746646571208877)
                  ·
                    refine ⟨1149650322654992464203329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3065734193746646571208877 1149650322654992464203329)
                    ·
                      refine ⟨862237741991244348152497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149650322654992464203329 862237741991244348152497)
                      ·
                        rfl

theorem cell23_1679202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_1679202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679202 prefixEnd_1679202 := by exact prefixLift 1679202
  have htrace : WordTrace (prefixWord ++ tailWord_1679202) baseStart_1679202 baseEnd_1679202 := by
    simpa [prefixWord, tailWord_1679202, baseEnd_1679202] using wordTrace_append hprefix tailTrace_1679202
  have hstable : (prefixWord ++ tailWord_1679202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679202).length < 2 ^ (prefixWord ++ tailWord_1679202).sum := by decide
  have hdescent : baseEnd_1679202 < baseStart_1679202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679224 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_1679224 : Nat := 118140960795 + 1679224 * 2 ^ 59
def prefixEnd_1679224 : Nat := 4983230072969 + 3 ^ 40 * 1679224 * 2
def baseEnd_1679224 : Nat := 862249038565643262077395

theorem tailTrace_1679224 : CollatzResearch.WordTrace tailWord_1679224 prefixEnd_1679224 862249038565643262077395 := by
  unfold tailWord_1679224
  simp only [CollatzResearch.WordTrace]
  refine ⟨30623165434232855735950363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40830887245643807647933817 30623165434232855735950363)
  ·
    refine ⟨45934748151349283603925545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30623165434232855735950363 45934748151349283603925545)
    ·
      refine ⟨34451061113511962702944159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45934748151349283603925545 34451061113511962702944159)
      ·
        refine ⟨51676591670267944054416239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34451061113511962702944159 51676591670267944054416239)
        ·
          refine ⟨77514887505401916081624359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51676591670267944054416239 77514887505401916081624359)
          ·
            refine ⟨116272331258102874122436539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77514887505401916081624359 116272331258102874122436539)
            ·
              refine ⟨174408496887154311183654809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116272331258102874122436539 174408496887154311183654809)
              ·
                refine ⟨130806372665365733387741107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174408496887154311183654809 130806372665365733387741107)
                ·
                  refine ⟨196209558998048600081611661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130806372665365733387741107 196209558998048600081611661)
                  ·
                    refine ⟨73578584624268225030604373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196209558998048600081611661 73578584624268225030604373)
                    ·
                      refine ⟨862249038565643262077395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 73578584624268225030604373 862249038565643262077395)
                      ·
                        rfl

theorem cell23_1679224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_1679224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679224 prefixEnd_1679224 := by exact prefixLift 1679224
  have htrace : WordTrace (prefixWord ++ tailWord_1679224) baseStart_1679224 baseEnd_1679224 := by
    simpa [prefixWord, tailWord_1679224, baseEnd_1679224] using wordTrace_append hprefix tailTrace_1679224
  have hstable : (prefixWord ++ tailWord_1679224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679224).length < 2 ^ (prefixWord ++ tailWord_1679224).sum := by decide
  have hdescent : baseEnd_1679224 < baseStart_1679224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679231 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 3]
def baseStart_1679231 : Nat := 118140960795 + 1679231 * 2 ^ 59
def prefixEnd_1679231 : Nat := 4983230072969 + 3 ^ 40 * 1679231 * 2
def baseEnd_1679231 : Nat := 862252632930224734689863

theorem tailTrace_1679231 : CollatzResearch.WordTrace tailWord_1679231 prefixEnd_1679231 862252632930224734689863 := by
  unfold tailWord_1679231
  simp only [CollatzResearch.WordTrace]
  refine ⟨61246586179440351667405547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40831057452960234444937031 61246586179440351667405547)
  ·
    refine ⟨91869879269160527501108321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61246586179440351667405547 91869879269160527501108321)
    ·
      refine ⟨68902409451870395625831241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91869879269160527501108321 68902409451870395625831241)
      ·
        refine ⟨51676807088902796719373431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68902409451870395625831241 51676807088902796719373431)
        ·
          refine ⟨77515210633354195079060147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51676807088902796719373431 77515210633354195079060147)
          ·
            refine ⟨116272815950031292618590221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77515210633354195079060147 116272815950031292618590221)
            ·
              refine ⟨43602305981261734731971333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116272815950031292618590221 43602305981261734731971333)
              ·
                refine ⟨8175432371486575262244625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43602305981261734731971333 8175432371486575262244625)
                ·
                  refine ⟨6131574278614931446683469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8175432371486575262244625 6131574278614931446683469)
                  ·
                    refine ⟨2299340354480599292506301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6131574278614931446683469 2299340354480599292506301)
                    ·
                      refine ⟨862252632930224734689863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299340354480599292506301 862252632930224734689863)
                      ·
                        rfl

theorem cell23_1679231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_1679231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679231 prefixEnd_1679231 := by exact prefixLift 1679231
  have htrace : WordTrace (prefixWord ++ tailWord_1679231) baseStart_1679231 baseEnd_1679231 := by
    simpa [prefixWord, tailWord_1679231, baseEnd_1679231] using wordTrace_append hprefix tailTrace_1679231
  have hstable : (prefixWord ++ tailWord_1679231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679231).length < 2 ^ (prefixWord ++ tailWord_1679231).sum := by decide
  have hdescent : baseEnd_1679231 < baseStart_1679231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679268 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_1679268 : Nat := 118140960795 + 1679268 * 2 ^ 59
def prefixEnd_1679268 : Nat := 4983230072969 + 3 ^ 40 * 1679268 * 2
def baseEnd_1679268 : Nat := 287423877238147029975731

theorem tailTrace_1679268 : CollatzResearch.WordTrace tailWord_1679268 prefixEnd_1679268 287423877238147029975731 := by
  unfold tailWord_1679268
  simp only [CollatzResearch.WordTrace]
  refine ⟨30623967840153153493251229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40831957120204204657668305 30623967840153153493251229)
  ·
    refine ⟨11483987940057432559969211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30623967840153153493251229 11483987940057432559969211)
    ·
      refine ⟨17225981910086148839953817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11483987940057432559969211 17225981910086148839953817)
      ·
        refine ⟨12919486432564611629965363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17225981910086148839953817 12919486432564611629965363)
        ·
          refine ⟨19379229648846917444948045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12919486432564611629965363 19379229648846917444948045)
          ·
            refine ⟨7267211118317594041855517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19379229648846917444948045 7267211118317594041855517)
            ·
              refine ⟨2725204169369097765695819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7267211118317594041855517 2725204169369097765695819)
              ·
                refine ⟨4087806254053646648543729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725204169369097765695819 4087806254053646648543729)
                ·
                  refine ⟨3065854690540234986407797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4087806254053646648543729 3065854690540234986407797)
                  ·
                    refine ⟨287423877238147029975731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3065854690540234986407797 287423877238147029975731)
                    ·
                      rfl

theorem cell23_1679268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_1679268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679268 prefixEnd_1679268 := by exact prefixLift 1679268
  have htrace : WordTrace (prefixWord ++ tailWord_1679268) baseStart_1679268 baseEnd_1679268 := by
    simpa [prefixWord, tailWord_1679268, baseEnd_1679268] using wordTrace_append hprefix tailTrace_1679268
  have hstable : (prefixWord ++ tailWord_1679268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679268).length < 2 ^ (prefixWord ++ tailWord_1679268).sum := by decide
  have hdescent : baseEnd_1679268 < baseStart_1679268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679288 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 4, 4, 2]
def baseStart_1679288 : Nat := 118140960795 + 1679288 * 2 ^ 59
def prefixEnd_1679288 : Nat := 4983230072969 + 3 ^ 40 * 1679288 * 2
def baseEnd_1679288 : Nat := 862281901327531011677101

theorem tailTrace_1679288 : CollatzResearch.WordTrace tailWord_1679288 prefixEnd_1679288 862281901327531011677101 := by
  unfold tailWord_1679288
  simp only [CollatzResearch.WordTrace]
  refine ⟨30624332570116925201115259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40832443426822566934820345 30624332570116925201115259)
  ·
    refine ⟨45936498855175387801672889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30624332570116925201115259 45936498855175387801672889)
    ·
      refine ⟨34452374141381540851254667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45936498855175387801672889 34452374141381540851254667)
      ·
        refine ⟨51678561212072311276882001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34452374141381540851254667 51678561212072311276882001)
        ·
          refine ⟨38758920909054233457661501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51678561212072311276882001 38758920909054233457661501)
          ·
            refine ⟨14534595340895337546623063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38758920909054233457661501 14534595340895337546623063)
            ·
              refine ⟨21801893011343006319934595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14534595340895337546623063 21801893011343006319934595)
              ·
                refine ⟨32702839517014509479901893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21801893011343006319934595 32702839517014509479901893)
                ·
                  refine ⟨6131782409440220527481605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32702839517014509479901893 6131782409440220527481605)
                  ·
                    refine ⟨1149709201770041348902801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6131782409440220527481605 1149709201770041348902801)
                    ·
                      refine ⟨862281901327531011677101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149709201770041348902801 862281901327531011677101)
                      ·
                        rfl

theorem cell23_1679288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_1679288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679288 prefixEnd_1679288 := by exact prefixLift 1679288
  have htrace : WordTrace (prefixWord ++ tailWord_1679288) baseStart_1679288 baseEnd_1679288 := by
    simpa [prefixWord, tailWord_1679288, baseEnd_1679288] using wordTrace_append hprefix tailTrace_1679288
  have hstable : (prefixWord ++ tailWord_1679288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679288).length < 2 ^ (prefixWord ++ tailWord_1679288).sum := by decide
  have hdescent : baseEnd_1679288 < baseStart_1679288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679291 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 3]
def baseStart_1679291 : Nat := 118140960795 + 1679291 * 2 ^ 59
def prefixEnd_1679291 : Nat := 4983230072969 + 3 ^ 40 * 1679291 * 2
def baseEnd_1679291 : Nat := 862283441769494499939587

theorem tailTrace_1679291 : CollatzResearch.WordTrace tailWord_1679291 prefixEnd_1679291 862283441769494499939587 := by
  unfold tailWord_1679291
  simp only [CollatzResearch.WordTrace]
  refine ⟨61248774559222981914589727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40832516372815321276393151 61248774559222981914589727)
  ·
    refine ⟨91873161838834472871884591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61248774559222981914589727 91873161838834472871884591)
    ·
      refine ⟨137809742758251709307826887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91873161838834472871884591 137809742758251709307826887)
      ·
        refine ⟨206714614137377563961740331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137809742758251709307826887 206714614137377563961740331)
        ·
          refine ⟨310071921206066345942610497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206714614137377563961740331 310071921206066345942610497)
          ·
            refine ⟨232553940904549759456957873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310071921206066345942610497 232553940904549759456957873)
            ·
              refine ⟨174415455678412319592718405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232553940904549759456957873 174415455678412319592718405)
              ·
                refine ⟨32702897939702309923634701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174415455678412319592718405 32702897939702309923634701)
                ·
                  refine ⟨12263586727388366221363013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32702897939702309923634701 12263586727388366221363013)
                  ·
                    refine ⟨2299422511385318666505565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12263586727388366221363013 2299422511385318666505565)
                    ·
                      refine ⟨862283441769494499939587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299422511385318666505565 862283441769494499939587)
                      ·
                        rfl

theorem cell23_1679291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 3].length) (baseStart_1679291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679291 prefixEnd_1679291 := by exact prefixLift 1679291
  have htrace : WordTrace (prefixWord ++ tailWord_1679291) baseStart_1679291 baseEnd_1679291 := by
    simpa [prefixWord, tailWord_1679291, baseEnd_1679291] using wordTrace_append hprefix tailTrace_1679291
  have hstable : (prefixWord ++ tailWord_1679291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679291).length < 2 ^ (prefixWord ++ tailWord_1679291).sum := by decide
  have hdescent : baseEnd_1679291 < baseStart_1679291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679308 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1679308 : Nat := 118140960795 + 1679308 * 2 ^ 59
def prefixEnd_1679308 : Nat := 4983230072969 + 3 ^ 40 * 1679308 * 2
def baseEnd_1679308 : Nat := 862292170940620933427009

theorem tailTrace_1679308 : CollatzResearch.WordTrace tailWord_1679308 prefixEnd_1679308 862292170940620933427009 := by
  unfold tailWord_1679308
  simp only [CollatzResearch.WordTrace]
  refine ⟨30624697300080696908979289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40832929733440929211972385 30624697300080696908979289)
  ·
    refine ⟨22968522975060522681734467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30624697300080696908979289 22968522975060522681734467)
    ·
      refine ⟨34452784462590784022601701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22968522975060522681734467 34452784462590784022601701)
      ·
        refine ⟨6459897086735772004237819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34452784462590784022601701 6459897086735772004237819)
        ·
          refine ⟨9689845630103658006356729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6459897086735772004237819 9689845630103658006356729)
          ·
            refine ⟨7267384222577743504767547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9689845630103658006356729 7267384222577743504767547)
            ·
              refine ⟨10901076333866615257151321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7267384222577743504767547 10901076333866615257151321)
              ·
                refine ⟨8175807250399961442863491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10901076333866615257151321 8175807250399961442863491)
                ·
                  refine ⟨12263710875599942164295237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175807250399961442863491 12263710875599942164295237)
                  ·
                    refine ⟨2299445789174989155805357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12263710875599942164295237 2299445789174989155805357)
                    ·
                      refine ⟨862292170940620933427009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299445789174989155805357 862292170940620933427009)
                      ·
                        rfl

theorem cell23_1679308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1679308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679308 prefixEnd_1679308 := by exact prefixLift 1679308
  have htrace : WordTrace (prefixWord ++ tailWord_1679308) baseStart_1679308 baseEnd_1679308 := by
    simpa [prefixWord, tailWord_1679308, baseEnd_1679308] using wordTrace_append hprefix tailTrace_1679308
  have hstable : (prefixWord ++ tailWord_1679308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679308).length < 2 ^ (prefixWord ++ tailWord_1679308).sum := by decide
  have hdescent : baseEnd_1679308 < baseStart_1679308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679355 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 3, 1, 3]
def baseStart_1679355 : Nat := 118140960795 + 1679355 * 2 ^ 59
def prefixEnd_1679355 : Nat := 4983230072969 + 3 ^ 40 * 1679355 * 2
def baseEnd_1679355 : Nat := 862316304531382249539293

theorem tailTrace_1679355 : CollatzResearch.WordTrace tailWord_1679355 prefixEnd_1679355 862316304531382249539293 := by
  unfold tailWord_1679355
  simp only [CollatzResearch.WordTrace]
  refine ⟨61251108830991120844919519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40834072553994080563279679 61251108830991120844919519)
  ·
    refine ⟨91876663246486681267379279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61251108830991120844919519 91876663246486681267379279)
    ·
      refine ⟨137814994869730021901068919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91876663246486681267379279 137814994869730021901068919)
      ·
        refine ⟨206722492304595032851603379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137814994869730021901068919 206722492304595032851603379)
        ·
          refine ⟨310083738456892549277405069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206722492304595032851603379 310083738456892549277405069)
          ·
            refine ⟨116281401921334705979026901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310083738456892549277405069 116281401921334705979026901)
            ·
              refine ⟨2725345357531282171383443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 116281401921334705979026901 2725345357531282171383443)
              ·
                refine ⟨4088018036296923257075165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725345357531282171383443 4088018036296923257075165)
                ·
                  refine ⟨1533006763611346221403187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4088018036296923257075165 1533006763611346221403187)
                  ·
                    refine ⟨2299510145417019332104781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1533006763611346221403187 2299510145417019332104781)
                    ·
                      refine ⟨862316304531382249539293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299510145417019332104781 862316304531382249539293)
                      ·
                        rfl

theorem cell23_1679355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 1, 3].length) (baseStart_1679355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679355 prefixEnd_1679355 := by exact prefixLift 1679355
  have htrace : WordTrace (prefixWord ++ tailWord_1679355) baseStart_1679355 baseEnd_1679355 := by
    simpa [prefixWord, tailWord_1679355, baseEnd_1679355] using wordTrace_append hprefix tailTrace_1679355
  have hstable : (prefixWord ++ tailWord_1679355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679355).length < 2 ^ (prefixWord ++ tailWord_1679355).sum := by decide
  have hdescent : baseEnd_1679355 < baseStart_1679355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679388 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_1679388 : Nat := 118140960795 + 1679388 * 2 ^ 59
def prefixEnd_1679388 : Nat := 4983230072969 + 3 ^ 40 * 1679388 * 2
def baseEnd_1679388 : Nat := 287444416464326873475547

theorem tailTrace_1679388 : CollatzResearch.WordTrace tailWord_1679388 prefixEnd_1679388 287444416464326873475547 := by
  unfold tailWord_1679388
  simp only [CollatzResearch.WordTrace]
  refine ⟨30626156219935783740435409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40834874959914378320580545 30626156219935783740435409)
  ·
    refine ⟨22969617164951837805326557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30626156219935783740435409 22969617164951837805326557)
    ·
      refine ⟨8613606436856939176997459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22969617164951837805326557 8613606436856939176997459)
      ·
        refine ⟨12920409655285408765496189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8613606436856939176997459 12920409655285408765496189)
        ·
          refine ⟨4845153620732028287061071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12920409655285408765496189 4845153620732028287061071)
          ·
            refine ⟨7267730431098042430591607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845153620732028287061071 7267730431098042430591607)
            ·
              refine ⟨10901595646647063645887411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7267730431098042430591607 10901595646647063645887411)
              ·
                refine ⟨16352393469970595468831117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10901595646647063645887411 16352393469970595468831117)
                ·
                  refine ⟨6132147551238973300811669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16352393469970595468831117 6132147551238973300811669)
                  ·
                    refine ⟨287444416464326873475547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6132147551238973300811669 287444416464326873475547)
                    ·
                      rfl

theorem cell23_1679388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_1679388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679388 prefixEnd_1679388 := by exact prefixLift 1679388
  have htrace : WordTrace (prefixWord ++ tailWord_1679388) baseStart_1679388 baseEnd_1679388 := by
    simpa [prefixWord, tailWord_1679388, baseEnd_1679388] using wordTrace_append hprefix tailTrace_1679388
  have hstable : (prefixWord ++ tailWord_1679388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679388).length < 2 ^ (prefixWord ++ tailWord_1679388).sum := by decide
  have hdescent : baseEnd_1679388 < baseStart_1679388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679406 : List Nat := [4, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_1679406 : Nat := 118140960795 + 1679406 * 2 ^ 59
def prefixEnd_1679406 : Nat := 4983230072969 + 3 ^ 40 * 1679406 * 2
def baseEnd_1679406 : Nat := 862342492044761550001559

theorem tailTrace_1679406 : CollatzResearch.WordTrace tailWord_1679406 prefixEnd_1679406 862342492044761550001559 := by
  unfold tailWord_1679406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7656621119225794569378259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40835312635870904370017381 7656621119225794569378259)
  ·
    refine ⟨11484931678838691854067389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7656621119225794569378259 11484931678838691854067389)
    ·
      refine ⟨4306849379564509445275271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11484931678838691854067389 4306849379564509445275271)
      ·
        refine ⟨6460274069346764167912907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4306849379564509445275271 6460274069346764167912907)
        ·
          refine ⟨9690411104020146251869361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460274069346764167912907 9690411104020146251869361)
          ·
            refine ⟨7267808328015109688902021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9690411104020146251869361 7267808328015109688902021)
            ·
              refine ⟨1362714061502833066669129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7267808328015109688902021 1362714061502833066669129)
              ·
                refine ⟨1022035546127124800001847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362714061502833066669129 1022035546127124800001847)
                ·
                  refine ⟨1533053319190687200002771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022035546127124800001847 1533053319190687200002771)
                  ·
                    refine ⟨2299579978786030800004157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1533053319190687200002771 2299579978786030800004157)
                    ·
                      refine ⟨862342492044761550001559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299579978786030800004157 862342492044761550001559)
                      ·
                        rfl

theorem cell23_1679406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_1679406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679406 prefixEnd_1679406 := by exact prefixLift 1679406
  have htrace : WordTrace (prefixWord ++ tailWord_1679406) baseStart_1679406 baseEnd_1679406 := by
    simpa [prefixWord, tailWord_1679406, baseEnd_1679406] using wordTrace_append hprefix tailTrace_1679406
  have hstable : (prefixWord ++ tailWord_1679406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679406).length < 2 ^ (prefixWord ++ tailWord_1679406).sum := by decide
  have hdescent : baseEnd_1679406 < baseStart_1679406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679422 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1679422 : Nat := 118140960795 + 1679422 * 2 ^ 59
def prefixEnd_1679422 : Nat := 4983230072969 + 3 ^ 40 * 1679422 * 2
def baseEnd_1679422 : Nat := 287450235911744495800495

theorem tailTrace_1679422 : CollatzResearch.WordTrace tailWord_1679422 prefixEnd_1679422 287450235911744495800495 := by
  unfold tailWord_1679422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7656694065218548910951065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40835701681165594191739013 7656694065218548910951065)
  ·
    refine ⟨5742520548913911683213299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7656694065218548910951065 5742520548913911683213299)
    ·
      refine ⟨8613780823370867524819949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5742520548913911683213299 8613780823370867524819949)
      ·
        refine ⟨3230167808764075321807481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8613780823370867524819949 3230167808764075321807481)
        ·
          refine ⟨2422625856573056491355611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3230167808764075321807481 2422625856573056491355611)
          ·
            refine ⟨3633938784859584737033417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422625856573056491355611 3633938784859584737033417)
            ·
              refine ⟨2725454088644688552775063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3633938784859584737033417 2725454088644688552775063)
              ·
                refine ⟨4088181132967032829162595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725454088644688552775063 4088181132967032829162595)
                ·
                  refine ⟨6132271699450549243743893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088181132967032829162595 6132271699450549243743893)
                  ·
                    refine ⟨287450235911744495800495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6132271699450549243743893 287450235911744495800495)
                    ·
                      rfl

theorem cell23_1679422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1679422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679422 prefixEnd_1679422 := by exact prefixLift 1679422
  have htrace : WordTrace (prefixWord ++ tailWord_1679422) baseStart_1679422 baseEnd_1679422 := by
    simpa [prefixWord, tailWord_1679422, baseEnd_1679422] using wordTrace_append hprefix tailTrace_1679422
  have hstable : (prefixWord ++ tailWord_1679422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679422).length < 2 ^ (prefixWord ++ tailWord_1679422).sum := by decide
  have hdescent : baseEnd_1679422 < baseStart_1679422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679425 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1679425 : Nat := 118140960795 + 1679425 * 2 ^ 59
def prefixEnd_1679425 : Nat := 4983230072969 + 3 ^ 40 * 1679425 * 2
def baseEnd_1679425 : Nat := 862352248177196975663971

theorem tailTrace_1679425 : CollatzResearch.WordTrace tailWord_1679425 prefixEnd_1679425 862352248177196975663971 := by
  unfold tailWord_1679425
  simp only [CollatzResearch.WordTrace]
  refine ⟨61253661940737522799967729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40835774627158348533311819 61253661940737522799967729)
  ·
    refine ⟨45940246455553142099975797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61253661940737522799967729 45940246455553142099975797)
    ·
      refine ⟨4306898105208107071872731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45940246455553142099975797 4306898105208107071872731)
      ·
        refine ⟨6460347157812160607809097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4306898105208107071872731 6460347157812160607809097)
        ·
          refine ⟨4845260368359120455856823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6460347157812160607809097 4845260368359120455856823)
          ·
            refine ⟨7267890552538680683785235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845260368359120455856823 7267890552538680683785235)
            ·
              refine ⟨10901835828808021025677853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7267890552538680683785235 10901835828808021025677853)
              ·
                refine ⟨4088188435803007884629195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10901835828808021025677853 4088188435803007884629195)
                ·
                  refine ⟨6132282653704511826943793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088188435803007884629195 6132282653704511826943793)
                  ·
                    refine ⟨4599211990278383870207845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6132282653704511826943793 4599211990278383870207845)
                    ·
                      refine ⟨862352248177196975663971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4599211990278383870207845 862352248177196975663971)
                      ·
                        rfl

theorem cell23_1679425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1679425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679425 prefixEnd_1679425 := by exact prefixLift 1679425
  have htrace : WordTrace (prefixWord ++ tailWord_1679425) baseStart_1679425 baseEnd_1679425 := by
    simpa [prefixWord, tailWord_1679425, baseEnd_1679425] using wordTrace_append hprefix tailTrace_1679425
  have hstable : (prefixWord ++ tailWord_1679425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679425).length < 2 ^ (prefixWord ++ tailWord_1679425).sum := by decide
  have hdescent : baseEnd_1679425 < baseStart_1679425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679445 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_1679445 : Nat := 118140960795 + 1679445 * 2 ^ 59
def prefixEnd_1679445 : Nat := 4983230072969 + 3 ^ 40 * 1679445 * 2
def baseEnd_1679445 : Nat := 862362517790286897413879

theorem tailTrace_1679445 : CollatzResearch.WordTrace tailWord_1679445 prefixEnd_1679445 862362517790286897413879 := by
  unfold tailWord_1679445
  simp only [CollatzResearch.WordTrace]
  refine ⟨61254391400665066215695789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40836260933776710810463859 61254391400665066215695789)
  ·
    refine ⟨22970396775249399830885921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61254391400665066215695789 22970396775249399830885921)
    ·
      refine ⟨17227797581437049873164441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22970396775249399830885921 17227797581437049873164441)
      ·
        refine ⟨12920848186077787404873331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17227797581437049873164441 12920848186077787404873331)
        ·
          refine ⟨19381272279116681107309997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12920848186077787404873331 19381272279116681107309997)
          ·
            refine ⟨7267977104668755415241249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19381272279116681107309997 7267977104668755415241249)
            ·
              refine ⟨5450982828501566561430937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7267977104668755415241249 5450982828501566561430937)
              ·
                refine ⟨4088237121376174921073203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450982828501566561430937 4088237121376174921073203)
                ·
                  refine ⟨6132355682064262381609805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088237121376174921073203 6132355682064262381609805)
                  ·
                    refine ⟨2299633380774098393103677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6132355682064262381609805 2299633380774098393103677)
                    ·
                      refine ⟨862362517790286897413879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299633380774098393103677 862362517790286897413879)
                      ·
                        rfl

theorem cell23_1679445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_1679445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679445 prefixEnd_1679445 := by exact prefixLift 1679445
  have htrace : WordTrace (prefixWord ++ tailWord_1679445) baseStart_1679445 baseEnd_1679445 := by
    simpa [prefixWord, tailWord_1679445, baseEnd_1679445] using wordTrace_append hprefix tailTrace_1679445
  have hstable : (prefixWord ++ tailWord_1679445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679445).length < 2 ^ (prefixWord ++ tailWord_1679445).sum := by decide
  have hdescent : baseEnd_1679445 < baseStart_1679445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679446 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_1679446 : Nat := 118140960795 + 1679446 * 2 ^ 59
def prefixEnd_1679446 : Nat := 4983230072969 + 3 ^ 40 * 1679446 * 2
def baseEnd_1679446 : Nat := 862363031270941393501375

theorem tailTrace_1679446 : CollatzResearch.WordTrace tailWord_1679446 prefixEnd_1679446 862363031270941393501375 := by
  unfold tailWord_1679446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3828401742103840211655137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40836285249107628924321461 3828401742103840211655137)
  ·
    refine ⟨2871301306577880158741353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3828401742103840211655137 2871301306577880158741353)
    ·
      refine ⟨2153475979933410119056015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2871301306577880158741353 2153475979933410119056015)
      ·
        refine ⟨3230213969900115178584023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153475979933410119056015 3230213969900115178584023)
        ·
          refine ⟨4845320954850172767876035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3230213969900115178584023 4845320954850172767876035)
          ·
            refine ⟨7267981432275259151814053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845320954850172767876035 7267981432275259151814053)
            ·
              refine ⟨1362746518551611090965135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7267981432275259151814053 1362746518551611090965135)
              ·
                refine ⟨2044119777827416636447703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362746518551611090965135 2044119777827416636447703)
                ·
                  refine ⟨3066179666741124954671555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044119777827416636447703 3066179666741124954671555)
                  ·
                    refine ⟨4599269500111687432007333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3066179666741124954671555 4599269500111687432007333)
                    ·
                      refine ⟨862363031270941393501375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4599269500111687432007333 862363031270941393501375)
                      ·
                        rfl

theorem cell23_1679446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_1679446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679446 prefixEnd_1679446 := by exact prefixLift 1679446
  have htrace : WordTrace (prefixWord ++ tailWord_1679446) baseStart_1679446 baseEnd_1679446 := by
    simpa [prefixWord, tailWord_1679446, baseEnd_1679446] using wordTrace_append hprefix tailTrace_1679446
  have hstable : (prefixWord ++ tailWord_1679446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679446).length < 2 ^ (prefixWord ++ tailWord_1679446).sum := by decide
  have hdescent : baseEnd_1679446 < baseStart_1679446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679455 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 5, 3, 2]
def baseStart_1679455 : Nat := 118140960795 + 1679455 * 2 ^ 59
def prefixEnd_1679455 : Nat := 4983230072969 + 3 ^ 40 * 1679455 * 2
def baseEnd_1679455 : Nat := 862367652596831858288833

theorem tailTrace_1679455 : CollatzResearch.WordTrace tailWord_1679455 prefixEnd_1679455 862367652596831858288833 := by
  unfold tailWord_1679455
  simp only [CollatzResearch.WordTrace]
  refine ⟨61254756130628837923559819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40836504087085891949039879 61254756130628837923559819)
  ·
    refine ⟨91882134195943256885339729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61254756130628837923559819 91882134195943256885339729)
    ·
      refine ⟨68911600646957442664004797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91882134195943256885339729 68911600646957442664004797)
      ·
        refine ⟨25841850242609040999001799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68911600646957442664004797 25841850242609040999001799)
        ·
          refine ⟨38762775363913561498502699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25841850242609040999001799 38762775363913561498502699)
          ·
            refine ⟨58144163045870342247754049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38762775363913561498502699 58144163045870342247754049)
            ·
              refine ⟨43608122284402756685815537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58144163045870342247754049 43608122284402756685815537)
              ·
                refine ⟨32706091713302067514361653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43608122284402756685815537 32706091713302067514361653)
                ·
                  refine ⟨3066196098122068829471405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32706091713302067514361653 3066196098122068829471405)
                  ·
                    refine ⟨1149823536795775811051777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3066196098122068829471405 1149823536795775811051777)
                    ·
                      refine ⟨862367652596831858288833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149823536795775811051777 862367652596831858288833)
                      ·
                        rfl

theorem cell23_1679455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_1679455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679455 prefixEnd_1679455 := by exact prefixLift 1679455
  have htrace : WordTrace (prefixWord ++ tailWord_1679455) baseStart_1679455 baseEnd_1679455 := by
    simpa [prefixWord, tailWord_1679455, baseEnd_1679455] using wordTrace_append hprefix tailTrace_1679455
  have hstable : (prefixWord ++ tailWord_1679455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679455).length < 2 ^ (prefixWord ++ tailWord_1679455).sum := by decide
  have hdescent : baseEnd_1679455 < baseStart_1679455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679479 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 2, 1, 3]
def baseStart_1679479 : Nat := 118140960795 + 1679479 * 2 ^ 59
def prefixEnd_1679479 : Nat := 4983230072969 + 3 ^ 40 * 1679479 * 2
def baseEnd_1679479 : Nat := 862379976132539764388723

theorem tailTrace_1679479 : CollatzResearch.WordTrace tailWord_1679479 prefixEnd_1679479 862379976132539764388723 := by
  unfold tailWord_1679479
  simp only [CollatzResearch.WordTrace]
  refine ⟨61255631482541890022433491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40837087655027926681622327 61255631482541890022433491)
  ·
    refine ⟨91883447223812835033650237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61255631482541890022433491 91883447223812835033650237)
    ·
      refine ⟨34456292708929813137618839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91883447223812835033650237 34456292708929813137618839)
      ·
        refine ⟨51684439063394719706428259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34456292708929813137618839 51684439063394719706428259)
        ·
          refine ⟨77526658595092079559642389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51684439063394719706428259 77526658595092079559642389)
          ·
            refine ⟨3634062121644941229358237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77526658595092079559642389 3634062121644941229358237)
            ·
              refine ⟨1362773295616852961009339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3634062121644941229358237 1362773295616852961009339)
              ·
                refine ⟨2044159943425279441514009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362773295616852961009339 2044159943425279441514009)
                ·
                  refine ⟨1533119957568959581135507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2044159943425279441514009 1533119957568959581135507)
                  ·
                    refine ⟨2299679936353439371703261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1533119957568959581135507 2299679936353439371703261)
                    ·
                      refine ⟨862379976132539764388723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299679936353439371703261 862379976132539764388723)
                      ·
                        rfl

theorem cell23_1679479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_1679479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679479 prefixEnd_1679479 := by exact prefixLift 1679479
  have htrace : WordTrace (prefixWord ++ tailWord_1679479) baseStart_1679479 baseEnd_1679479 := by
    simpa [prefixWord, tailWord_1679479, baseEnd_1679479] using wordTrace_append hprefix tailTrace_1679479
  have hstable : (prefixWord ++ tailWord_1679479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679479).length < 2 ^ (prefixWord ++ tailWord_1679479).sum := by decide
  have hdescent : baseEnd_1679479 < baseStart_1679479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679488 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_1679488 : Nat := 118140960795 + 1679488 * 2 ^ 59
def prefixEnd_1679488 : Nat := 4983230072969 + 3 ^ 40 * 1679488 * 2
def baseEnd_1679488 : Nat := 862384597458430229176181

theorem tailTrace_1679488 : CollatzResearch.WordTrace tailWord_1679488 prefixEnd_1679488 862384597458430229176181 := by
  unfold tailWord_1679488
  simp only [CollatzResearch.WordTrace]
  refine ⟨30627979869754642279755559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40837306493006189706340745 30627979869754642279755559)
  ·
    refine ⟨45941969804631963419633339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30627979869754642279755559 45941969804631963419633339)
    ·
      refine ⟨68912954706947945129450009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45941969804631963419633339 68912954706947945129450009)
      ·
        refine ⟨51684716030210958847087507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68912954706947945129450009 51684716030210958847087507)
        ·
          refine ⟨77527074045316438270631261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51684716030210958847087507 77527074045316438270631261)
          ·
            refine ⟨29072652766993664351486723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77527074045316438270631261 29072652766993664351486723)
            ·
              refine ⟨43608979150490496527230085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29072652766993664351486723 43608979150490496527230085)
              ·
                refine ⟨8176683590716968098855641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43608979150490496527230085 8176683590716968098855641)
                ·
                  refine ⟨6132512693037726074141731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8176683590716968098855641 6132512693037726074141731)
                  ·
                    refine ⟨9198769039556589111212597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6132512693037726074141731 9198769039556589111212597)
                    ·
                      refine ⟨862384597458430229176181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9198769039556589111212597 862384597458430229176181)
                      ·
                        rfl

theorem cell23_1679488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_1679488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679488 prefixEnd_1679488 := by exact prefixLift 1679488
  have htrace : WordTrace (prefixWord ++ tailWord_1679488) baseStart_1679488 baseEnd_1679488 := by
    simpa [prefixWord, tailWord_1679488, baseEnd_1679488] using wordTrace_append hprefix tailTrace_1679488
  have hstable : (prefixWord ++ tailWord_1679488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679488).length < 2 ^ (prefixWord ++ tailWord_1679488).sum := by decide
  have hdescent : baseEnd_1679488 < baseStart_1679488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679519 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 4, 2, 2]
def baseStart_1679519 : Nat := 118140960795 + 1679519 * 2 ^ 59
def prefixEnd_1679519 : Nat := 4983230072969 + 3 ^ 40 * 1679519 * 2
def baseEnd_1679519 : Nat := 862400515358719607888539

theorem tailTrace_1679519 : CollatzResearch.WordTrace tailWord_1679519 prefixEnd_1679519 862400515358719607888539 := by
  unfold tailWord_1679519
  simp only [CollatzResearch.WordTrace]
  refine ⟨61257090402396976853889611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40838060268264651235926407 61257090402396976853889611)
  ·
    refine ⟨91885635603595465280834417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61257090402396976853889611 91885635603595465280834417)
    ·
      refine ⟨68914226702696598960625813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91885635603595465280834417 68914226702696598960625813)
      ·
        refine ⟨3230354376688903076279335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68914226702696598960625813 3230354376688903076279335)
        ·
          refine ⟨4845531565033354614419003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3230354376688903076279335 4845531565033354614419003)
          ·
            refine ⟨7268297347550031921628505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845531565033354614419003 7268297347550031921628505)
            ·
              refine ⟨5451223010662523941221379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7268297347550031921628505 5451223010662523941221379)
              ·
                refine ⟨8176834515993785911832069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451223010662523941221379 8176834515993785911832069)
                ·
                  refine ⟨1533156471748834858468513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8176834515993785911832069 1533156471748834858468513)
                  ·
                    refine ⟨1149867353811626143851385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1533156471748834858468513 1149867353811626143851385)
                    ·
                      refine ⟨862400515358719607888539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149867353811626143851385 862400515358719607888539)
                      ·
                        rfl

theorem cell23_1679519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_1679519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679519 prefixEnd_1679519 := by exact prefixLift 1679519
  have htrace : WordTrace (prefixWord ++ tailWord_1679519) baseStart_1679519 baseEnd_1679519 := by
    simpa [prefixWord, tailWord_1679519, baseEnd_1679519] using wordTrace_append hprefix tailTrace_1679519
  have hstable : (prefixWord ++ tailWord_1679519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679519).length < 2 ^ (prefixWord ++ tailWord_1679519).sum := by decide
  have hdescent : baseEnd_1679519 < baseStart_1679519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679530 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_1679530 : Nat := 118140960795 + 1679530 * 2 ^ 59
def prefixEnd_1679530 : Nat := 4983230072969 + 3 ^ 40 * 1679530 * 2
def baseEnd_1679530 : Nat := 862406163645919064850989

theorem tailTrace_1679530 : CollatzResearch.WordTrace tailWord_1679530 prefixEnd_1679530 862406163645919064850989 := by
  unfold tailWord_1679530
  simp only [CollatzResearch.WordTrace]
  refine ⟨15314372901339281433135011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40838327736904750488360029 15314372901339281433135011)
  ·
    refine ⟨22971559352008922149702517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15314372901339281433135011 22971559352008922149702517)
    ·
      refine ⟨2153583689250836451534611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22971559352008922149702517 2153583689250836451534611)
      ·
        refine ⟨3230375533876254677301917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153583689250836451534611 3230375533876254677301917)
        ·
          refine ⟨1211390825203595503988219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3230375533876254677301917 1211390825203595503988219)
          ·
            refine ⟨1817086237805393255982329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211390825203595503988219 1817086237805393255982329)
            ·
              refine ⟨1362814678354044941986747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817086237805393255982329 1362814678354044941986747)
              ·
                refine ⟨2044222017531067412980121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362814678354044941986747 2044222017531067412980121)
                ·
                  refine ⟨1533166513148300559735091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2044222017531067412980121 1533166513148300559735091)
                  ·
                    refine ⟨2299749769722450839602637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1533166513148300559735091 2299749769722450839602637)
                    ·
                      refine ⟨862406163645919064850989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299749769722450839602637 862406163645919064850989)
                      ·
                        rfl

theorem cell23_1679530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_1679530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679530 prefixEnd_1679530 := by exact prefixLift 1679530
  have htrace : WordTrace (prefixWord ++ tailWord_1679530) baseStart_1679530 baseEnd_1679530 := by
    simpa [prefixWord, tailWord_1679530, baseEnd_1679530] using wordTrace_append hprefix tailTrace_1679530
  have hstable : (prefixWord ++ tailWord_1679530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679530).length < 2 ^ (prefixWord ++ tailWord_1679530).sum := by decide
  have hdescent : baseEnd_1679530 < baseStart_1679530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679592 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_1679592 : Nat := 118140960795 + 1679592 * 2 ^ 59
def prefixEnd_1679592 : Nat := 4983230072969 + 3 ^ 40 * 1679592 * 2
def baseEnd_1679592 : Nat := 862437999446497822275703

theorem tailTrace_1679592 : CollatzResearch.WordTrace tailWord_1679592 prefixEnd_1679592 862437999446497822275703 := by
  unfold tailWord_1679592
  simp only [CollatzResearch.WordTrace]
  refine ⟨30629876465566255160648515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40839835287421673547531353 30629876465566255160648515)
  ·
    refine ⟨45944814698349382740972773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30629876465566255160648515 45944814698349382740972773)
    ·
      refine ⟨8614652755940509263932395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45944814698349382740972773 8614652755940509263932395)
      ·
        refine ⟨12921979133910763895898593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8614652755940509263932395 12921979133910763895898593)
        ·
          refine ⟨9691484350433072921923945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12921979133910763895898593 9691484350433072921923945)
          ·
            refine ⟨7268613262824804691442959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9691484350433072921923945 7268613262824804691442959)
            ·
              refine ⟨10902919894237207037164439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7268613262824804691442959 10902919894237207037164439)
              ·
                refine ⟨16354379841355810555746659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10902919894237207037164439 16354379841355810555746659)
                ·
                  refine ⟨24531569762033715833619989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16354379841355810555746659 24531569762033715833619989)
                  ·
                    refine ⟨1149917332595330429700937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24531569762033715833619989 1149917332595330429700937)
                    ·
                      refine ⟨862437999446497822275703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149917332595330429700937 862437999446497822275703)
                      ·
                        rfl

theorem cell23_1679592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_1679592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679592 prefixEnd_1679592 := by exact prefixLift 1679592
  have htrace : WordTrace (prefixWord ++ tailWord_1679592) baseStart_1679592 baseEnd_1679592 := by
    simpa [prefixWord, tailWord_1679592, baseEnd_1679592] using wordTrace_append hprefix tailTrace_1679592
  have hstable : (prefixWord ++ tailWord_1679592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679592).length < 2 ^ (prefixWord ++ tailWord_1679592).sum := by decide
  have hdescent : baseEnd_1679592 < baseStart_1679592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679595 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 3]
def baseStart_1679595 : Nat := 118140960795 + 1679595 * 2 ^ 59
def prefixEnd_1679595 : Nat := 4983230072969 + 3 ^ 40 * 1679595 * 2
def baseEnd_1679595 : Nat := 862439539888461310538189

theorem tailTrace_1679595 : CollatzResearch.WordTrace tailWord_1679595 prefixEnd_1679595 862439539888461310538189 := by
  unfold tailWord_1679595
  simp only [CollatzResearch.WordTrace]
  refine ⟨61259862350121641833656239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40839908233414427889104159 61259862350121641833656239)
  ·
    refine ⟨91889793525182462750484359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61259862350121641833656239 91889793525182462750484359)
    ·
      refine ⟨137834690287773694125726539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91889793525182462750484359 137834690287773694125726539)
      ·
        refine ⟨206752035431660541188589809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137834690287773694125726539 206752035431660541188589809)
        ·
          refine ⟨155064026573745405891442357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206752035431660541188589809 155064026573745405891442357)
          ·
            refine ⟨14537252491288631802322721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155064026573745405891442357 14537252491288631802322721)
            ·
              refine ⟨10902939368466473851742041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14537252491288631802322721 10902939368466473851742041)
              ·
                refine ⟨8177204526349855388806531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10902939368466473851742041 8177204526349855388806531)
                ·
                  refine ⟨12265806789524783083209797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8177204526349855388806531 12265806789524783083209797)
                  ·
                    refine ⟨2299838773035896828101837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12265806789524783083209797 2299838773035896828101837)
                    ·
                      refine ⟨862439539888461310538189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299838773035896828101837 862439539888461310538189)
                      ·
                        rfl

theorem cell23_1679595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 3].length) (baseStart_1679595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679595 prefixEnd_1679595 := by exact prefixLift 1679595
  have htrace : WordTrace (prefixWord ++ tailWord_1679595) baseStart_1679595 baseEnd_1679595 := by
    simpa [prefixWord, tailWord_1679595, baseEnd_1679595] using wordTrace_append hprefix tailTrace_1679595
  have hstable : (prefixWord ++ tailWord_1679595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679595).length < 2 ^ (prefixWord ++ tailWord_1679595).sum := by decide
  have hdescent : baseEnd_1679595 < baseStart_1679595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679602 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_1679602 : Nat := 118140960795 + 1679602 * 2 ^ 59
def prefixEnd_1679602 : Nat := 4983230072969 + 3 ^ 40 * 1679602 * 2
def baseEnd_1679602 : Nat := 287481044751014261050219

theorem tailTrace_1679602 : CollatzResearch.WordTrace tailWord_1679602 prefixEnd_1679602 287481044751014261050219 := by
  unfold tailWord_1679602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15315029415274070507290265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40840078440730854686107373 15315029415274070507290265)
  ·
    refine ⟨11486272061455552880467699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15315029415274070507290265 11486272061455552880467699)
    ·
      refine ⟨17229408092183329320701549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11486272061455552880467699 17229408092183329320701549)
      ·
        refine ⟨6461028034568748495263081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17229408092183329320701549 6461028034568748495263081)
        ·
          refine ⟨4845771025926561371447311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6461028034568748495263081 4845771025926561371447311)
          ·
            refine ⟨7268656538889842057170967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845771025926561371447311 7268656538889842057170967)
            ·
              refine ⟨10902984808334763085756451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7268656538889842057170967 10902984808334763085756451)
              ·
                refine ⟨16354477212502144628634677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10902984808334763085756451 16354477212502144628634677)
                ·
                  refine ⟨1533232238672076058934501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16354477212502144628634677 1533232238672076058934501)
                  ·
                    refine ⟨287481044751014261050219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1533232238672076058934501 287481044751014261050219)
                    ·
                      rfl

theorem cell23_1679602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_1679602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679602 prefixEnd_1679602 := by exact prefixLift 1679602
  have htrace : WordTrace (prefixWord ++ tailWord_1679602) baseStart_1679602 baseEnd_1679602 := by
    simpa [prefixWord, tailWord_1679602, baseEnd_1679602] using wordTrace_append hprefix tailTrace_1679602
  have hstable : (prefixWord ++ tailWord_1679602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679602).length < 2 ^ (prefixWord ++ tailWord_1679602).sum := by decide
  have hdescent : baseEnd_1679602 < baseStart_1679602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679612 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_1679612 : Nat := 118140960795 + 1679612 * 2 ^ 59
def prefixEnd_1679612 : Nat := 4983230072969 + 3 ^ 40 * 1679612 * 2
def baseEnd_1679612 : Nat := 862448269059587744025611

theorem tailTrace_1679612 : CollatzResearch.WordTrace tailWord_1679612 prefixEnd_1679612 862448269059587744025611 := by
  unfold tailWord_1679612
  simp only [CollatzResearch.WordTrace]
  refine ⟨30630241195530026868512545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40840321594040035824683393 30630241195530026868512545)
  ·
    refine ⟨22972680896647520151384409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30630241195530026868512545 22972680896647520151384409)
    ·
      refine ⟨17229510672485640113538307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22972680896647520151384409 17229510672485640113538307)
      ·
        refine ⟨25844266008728460170307461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17229510672485640113538307 25844266008728460170307461)
        ·
          refine ⟨4845799876636586281932649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25844266008728460170307461 4845799876636586281932649)
          ·
            refine ⟨3634349907477439711449487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4845799876636586281932649 3634349907477439711449487)
            ·
              refine ⟨5451524861216159567174231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634349907477439711449487 5451524861216159567174231)
              ·
                refine ⟨8177287291824239350761347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451524861216159567174231 8177287291824239350761347)
                ·
                  refine ⟨12265930937736359026142021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8177287291824239350761347 12265930937736359026142021)
                  ·
                    refine ⟨2299862050825567317401629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12265930937736359026142021 2299862050825567317401629)
                    ·
                      refine ⟨862448269059587744025611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2299862050825567317401629 862448269059587744025611)
                      ·
                        rfl

theorem cell23_1679612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_1679612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679612 prefixEnd_1679612 := by exact prefixLift 1679612
  have htrace : WordTrace (prefixWord ++ tailWord_1679612) baseStart_1679612 baseEnd_1679612 := by
    simpa [prefixWord, tailWord_1679612, baseEnd_1679612] using wordTrace_append hprefix tailTrace_1679612
  have hstable : (prefixWord ++ tailWord_1679612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679612).length < 2 ^ (prefixWord ++ tailWord_1679612).sum := by decide
  have hdescent : baseEnd_1679612 < baseStart_1679612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679619 : List Nat := [1, 1, 1, 3, 2, 3, 4, 3, 1, 4]
def baseStart_1679619 : Nat := 118140960795 + 1679619 * 2 ^ 59
def prefixEnd_1679619 : Nat := 4983230072969 + 3 ^ 40 * 1679619 * 2
def baseEnd_1679619 : Nat := 287483954474723072212693

theorem tailTrace_1679619 : CollatzResearch.WordTrace tailWord_1679619 prefixEnd_1679619 287483954474723072212693 := by
  unfold tailWord_1679619
  simp only [CollatzResearch.WordTrace]
  refine ⟨61260737702034693932529911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40840491801356462621686607 61260737702034693932529911)
  ·
    refine ⟨91891106553052040898794867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61260737702034693932529911 91891106553052040898794867)
    ·
      refine ⟨137836659829578061348192301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91891106553052040898794867 137836659829578061348192301)
      ·
        refine ⟨51688747436091773005572113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137836659829578061348192301 51688747436091773005572113)
        ·
          refine ⟨38766560577068829754179085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51688747436091773005572113 38766560577068829754179085)
          ·
            refine ⟨14537460216400811157817157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38766560577068829754179085 14537460216400811157817157)
            ·
              refine ⟨2725773790575152092090717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14537460216400811157817157 2725773790575152092090717)
              ·
                refine ⟨1022165171465682034534019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2725773790575152092090717 1022165171465682034534019)
                ·
                  refine ⟨1533247757198523051801029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022165171465682034534019 1533247757198523051801029)
                  ·
                    refine ⟨287483954474723072212693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1533247757198523051801029 287483954474723072212693)
                    ·
                      rfl

theorem cell23_1679619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 1, 4].length) (baseStart_1679619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679619 prefixEnd_1679619 := by exact prefixLift 1679619
  have htrace : WordTrace (prefixWord ++ tailWord_1679619) baseStart_1679619 baseEnd_1679619 := by
    simpa [prefixWord, tailWord_1679619, baseEnd_1679619] using wordTrace_append hprefix tailTrace_1679619
  have hstable : (prefixWord ++ tailWord_1679619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679619).length < 2 ^ (prefixWord ++ tailWord_1679619).sum := by decide
  have hdescent : baseEnd_1679619 < baseStart_1679619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679669 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_1679669 : Nat := 118140960795 + 1679669 * 2 ^ 59
def prefixEnd_1679669 : Nat := 4983230072969 + 3 ^ 40 * 1679669 * 2
def baseEnd_1679669 : Nat := 862477537456894021012849

theorem tailTrace_1679669 : CollatzResearch.WordTrace tailWord_1679669 prefixEnd_1679669 862477537456894021012849 := by
  unfold tailWord_1679669
  simp only [CollatzResearch.WordTrace]
  refine ⟨61262561351853552471850061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40841707567902368314566707 61262561351853552471850061)
  ·
    refine ⟨22973460506945082176943773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61262561351853552471850061 22973460506945082176943773)
    ·
      refine ⟨8615047690104405816353915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22973460506945082176943773 8615047690104405816353915)
      ·
        refine ⟨12922571535156608724530873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8615047690104405816353915 12922571535156608724530873)
        ·
          refine ⟨9691928651367456543398155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12922571535156608724530873 9691928651367456543398155)
          ·
            refine ⟨14537892977051184815097233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9691928651367456543398155 14537892977051184815097233)
            ·
              refine ⟨10903419732788388611322925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14537892977051184815097233 10903419732788388611322925)
              ·
                refine ⟨4088782399795645729246097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10903419732788388611322925 4088782399795645729246097)
                ·
                  refine ⟨3066586799846734296934573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4088782399795645729246097 3066586799846734296934573)
                  ·
                    refine ⟨1149970049942525361350465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3066586799846734296934573 1149970049942525361350465)
                    ·
                      refine ⟨862477537456894021012849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149970049942525361350465 862477537456894021012849)
                      ·
                        rfl

theorem cell23_1679669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_1679669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679669 prefixEnd_1679669 := by exact prefixLift 1679669
  have htrace : WordTrace (prefixWord ++ tailWord_1679669) baseStart_1679669 baseEnd_1679669 := by
    simpa [prefixWord, tailWord_1679669, baseEnd_1679669] using wordTrace_append hprefix tailTrace_1679669
  have hstable : (prefixWord ++ tailWord_1679669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679669).length < 2 ^ (prefixWord ++ tailWord_1679669).sum := by decide
  have hdescent : baseEnd_1679669 < baseStart_1679669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679692 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_1679692 : Nat := 118140960795 + 1679692 * 2 ^ 59
def prefixEnd_1679692 : Nat := 4983230072969 + 3 ^ 40 * 1679692 * 2
def baseEnd_1679692 : Nat := 287496449170649143675081

theorem tailTrace_1679692 : CollatzResearch.WordTrace tailWord_1679692 prefixEnd_1679692 287496449170649143675081 := by
  unfold tailWord_1679692
  simp only [CollatzResearch.WordTrace]
  refine ⟨30631700115385113699968665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40842266820513484933291553 30631700115385113699968665)
  ·
    refine ⟨22973775086538835274976499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30631700115385113699968665 22973775086538835274976499)
    ·
      refine ⟨34460662629808252912464749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22973775086538835274976499 34460662629808252912464749)
      ·
        refine ⟨12922748486178094842174281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34460662629808252912464749 12922748486178094842174281)
        ·
          refine ⟨9692061364633571131630711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12922748486178094842174281 9692061364633571131630711)
          ·
            refine ⟨14538092046950356697446067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9692061364633571131630711 14538092046950356697446067)
            ·
              refine ⟨21807138070425535046169101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14538092046950356697446067 21807138070425535046169101)
              ·
                refine ⟨8177676776409575642313413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21807138070425535046169101 8177676776409575642313413)
                ·
                  refine ⟨1533314395576795432933765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8177676776409575642313413 1533314395576795432933765)
                  ·
                    refine ⟨287496449170649143675081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1533314395576795432933765 287496449170649143675081)
                    ·
                      rfl

theorem cell23_1679692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_1679692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679692 prefixEnd_1679692 := by exact prefixLift 1679692
  have htrace : WordTrace (prefixWord ++ tailWord_1679692) baseStart_1679692 baseEnd_1679692 := by
    simpa [prefixWord, tailWord_1679692, baseEnd_1679692] using wordTrace_append hprefix tailTrace_1679692
  have hstable : (prefixWord ++ tailWord_1679692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679692).length < 2 ^ (prefixWord ++ tailWord_1679692).sum := by decide
  have hdescent : baseEnd_1679692 < baseStart_1679692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679695 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_1679695 : Nat := 118140960795 + 1679695 * 2 ^ 59
def prefixEnd_1679695 : Nat := 4983230072969 + 3 ^ 40 * 1679695 * 2
def baseEnd_1679695 : Nat := 862490887953910919287729

theorem tailTrace_1679695 : CollatzResearch.WordTrace tailWord_1679695 prefixEnd_1679695 862490887953910919287729 := by
  unfold tailWord_1679695
  simp only [CollatzResearch.WordTrace]
  refine ⟨61263509649759358912296539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40842339766506239274864359 61263509649759358912296539)
  ·
    refine ⟨91895264474639038368444809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61263509649759358912296539 91895264474639038368444809)
    ·
      refine ⟨68921448355979278776333607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91895264474639038368444809 68921448355979278776333607)
      ·
        refine ⟨103382172533968918164500411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68921448355979278776333607 103382172533968918164500411)
        ·
          refine ⟨155073258800953377246750617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103382172533968918164500411 155073258800953377246750617)
          ·
            refine ⟨116304944100715032935062963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155073258800953377246750617 116304944100715032935062963)
            ·
              refine ⟨174457416151072549402594445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116304944100715032935062963 174457416151072549402594445)
              ·
                refine ⟨65421531056652206025972917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174457416151072549402594445 65421531056652206025972917)
                ·
                  refine ⟨6133268536561144314934961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65421531056652206025972917 6133268536561144314934961)
                  ·
                    refine ⟨4599951402420858236201221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6133268536561144314934961 4599951402420858236201221)
                    ·
                      refine ⟨862490887953910919287729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4599951402420858236201221 862490887953910919287729)
                      ·
                        rfl

theorem cell23_1679695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_1679695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679695 prefixEnd_1679695 := by exact prefixLift 1679695
  have htrace : WordTrace (prefixWord ++ tailWord_1679695) baseStart_1679695 baseEnd_1679695 := by
    simpa [prefixWord, tailWord_1679695, baseEnd_1679695] using wordTrace_append hprefix tailTrace_1679695
  have hstable : (prefixWord ++ tailWord_1679695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679695).length < 2 ^ (prefixWord ++ tailWord_1679695).sum := by decide
  have hdescent : baseEnd_1679695 < baseStart_1679695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679699 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 3, 2, 2]
def baseStart_1679699 : Nat := 118140960795 + 1679699 * 2 ^ 59
def prefixEnd_1679699 : Nat := 4983230072969 + 3 ^ 40 * 1679699 * 2
def baseEnd_1679699 : Nat := 862492941876528903637711

theorem tailTrace_1679699 : CollatzResearch.WordTrace tailWord_1679699 prefixEnd_1679699 862492941876528903637711 := by
  unfold tailWord_1679699
  simp only [CollatzResearch.WordTrace]
  refine ⟨61263655541744867595442151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40842437027829911730294767 61263655541744867595442151)
  ·
    refine ⟨91895483312617301393163227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61263655541744867595442151 91895483312617301393163227)
    ·
      refine ⟨137843224968925952089744841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91895483312617301393163227 137843224968925952089744841)
      ·
        refine ⟨103382418726694464067308631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137843224968925952089744841 103382418726694464067308631)
        ·
          refine ⟨155073628090041696100962947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103382418726694464067308631 155073628090041696100962947)
          ·
            refine ⟨232610442135062544151444421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155073628090041696100962947 232610442135062544151444421)
            ·
              refine ⟨43614457900324227028395829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232610442135062544151444421 43614457900324227028395829)
              ·
                refine ⟨4088855428155396283912109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43614457900324227028395829 4088855428155396283912109)
                ·
                  refine ⟨1533320785558273606467041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4088855428155396283912109 1533320785558273606467041)
                  ·
                    refine ⟨1149990589168705204850281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1533320785558273606467041 1149990589168705204850281)
                    ·
                      refine ⟨862492941876528903637711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149990589168705204850281 862492941876528903637711)
                      ·
                        rfl

theorem cell23_1679699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 2, 2].length) (baseStart_1679699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679699 prefixEnd_1679699 := by exact prefixLift 1679699
  have htrace : WordTrace (prefixWord ++ tailWord_1679699) baseStart_1679699 baseEnd_1679699 := by
    simpa [prefixWord, tailWord_1679699, baseEnd_1679699] using wordTrace_append hprefix tailTrace_1679699
  have hstable : (prefixWord ++ tailWord_1679699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679699).length < 2 ^ (prefixWord ++ tailWord_1679699).sum := by decide
  have hdescent : baseEnd_1679699 < baseStart_1679699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679719 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1679719 : Nat := 118140960795 + 1679719 * 2 ^ 59
def prefixEnd_1679719 : Nat := 4983230072969 + 3 ^ 40 * 1679719 * 2
def baseEnd_1679719 : Nat := 862503211489618825387619

theorem tailTrace_1679719 : CollatzResearch.WordTrace tailWord_1679719 prefixEnd_1679719 862503211489618825387619 := by
  unfold tailWord_1679719
  simp only [CollatzResearch.WordTrace]
  refine ⟨61264385001672411011170211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40842923334448274007446807 61264385001672411011170211)
  ·
    refine ⟨91896577502508616516755317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61264385001672411011170211 91896577502508616516755317)
    ·
      refine ⟨8615304140860182798445811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91896577502508616516755317 8615304140860182798445811)
      ·
        refine ⟨12922956211290274197668717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8615304140860182798445811 12922956211290274197668717)
        ·
          refine ⟨4846108579233852824125769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12922956211290274197668717 4846108579233852824125769)
          ·
            refine ⟨3634581434425389618094327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4846108579233852824125769 3634581434425389618094327)
            ·
              refine ⟨5451872151638084427141491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634581434425389618094327 5451872151638084427141491)
              ·
                refine ⟨8177808227457126640712237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451872151638084427141491 8177808227457126640712237)
                ·
                  refine ⟨3066678085296422490267089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8177808227457126640712237 3066678085296422490267089)
                  ·
                    refine ⟨2300008563972316867700317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3066678085296422490267089 2300008563972316867700317)
                    ·
                      refine ⟨862503211489618825387619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2300008563972316867700317 862503211489618825387619)
                      ·
                        rfl

theorem cell23_1679719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1679719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679719 prefixEnd_1679719 := by exact prefixLift 1679719
  have htrace : WordTrace (prefixWord ++ tailWord_1679719) baseStart_1679719 baseEnd_1679719 := by
    simpa [prefixWord, tailWord_1679719, baseEnd_1679719] using wordTrace_append hprefix tailTrace_1679719
  have hstable : (prefixWord ++ tailWord_1679719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679719).length < 2 ^ (prefixWord ++ tailWord_1679719).sum := by decide
  have hdescent : baseEnd_1679719 < baseStart_1679719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679722 : List Nat := [3, 1, 3, 3, 1, 1, 2, 9]
def baseStart_1679722 : Nat := 118140960795 + 1679722 * 2 ^ 59
def prefixEnd_1679722 : Nat := 4983230072969 + 3 ^ 40 * 1679722 * 2
def baseEnd_1679722 : Nat := 31944620441910456061115

theorem tailTrace_1679722 : CollatzResearch.WordTrace tailWord_1679722 prefixEnd_1679722 31944620441910456061115 := by
  unfold tailWord_1679722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15316123605165385630882355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40842996280441028349019613 15316123605165385630882355)
  ·
    refine ⟨22974185407748078446323533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15316123605165385630882355 22974185407748078446323533)
    ·
      refine ⟨8615319527905529417371325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22974185407748078446323533 8615319527905529417371325)
      ·
        refine ⟨3230744822964573531514247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8615319527905529417371325 3230744822964573531514247)
        ·
          refine ⟨4846117234446860297271371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3230744822964573531514247 4846117234446860297271371)
          ·
            refine ⟨7269175851670290445907057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4846117234446860297271371 7269175851670290445907057)
            ·
              refine ⟨5451881888752717834430293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7269175851670290445907057 5451881888752717834430293)
              ·
                refine ⟨31944620441910456061115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5451881888752717834430293 31944620441910456061115)
                ·
                  rfl

theorem cell23_1679722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 9].length) (baseStart_1679722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679722 prefixEnd_1679722 := by exact prefixLift 1679722
  have htrace : WordTrace (prefixWord ++ tailWord_1679722) baseStart_1679722 baseEnd_1679722 := by
    simpa [prefixWord, tailWord_1679722, baseEnd_1679722] using wordTrace_append hprefix tailTrace_1679722
  have hstable : (prefixWord ++ tailWord_1679722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679722).length < 2 ^ (prefixWord ++ tailWord_1679722).sum := by decide
  have hdescent : baseEnd_1679722 < baseStart_1679722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679793 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 1, 3, 2]
def baseStart_1679793 : Nat := 118140960795 + 1679793 * 2 ^ 59
def prefixEnd_1679793 : Nat := 4983230072969 + 3 ^ 40 * 1679793 * 2
def baseEnd_1679793 : Nat := 862541209058051535862279

theorem tailTrace_1679793 : CollatzResearch.WordTrace tailWord_1679793 prefixEnd_1679793 862541209058051535862279 := by
  unfold tailWord_1679793
  simp only [CollatzResearch.WordTrace]
  refine ⟨61267084003404321649364033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40844722668936214432909355 61267084003404321649364033)
  ·
    refine ⟨45950313002553241237023025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61267084003404321649364033 45950313002553241237023025)
    ·
      refine ⟨34462734751914930927767269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45950313002553241237023025 34462734751914930927767269)
      ·
        refine ⟨6461762765984049548956363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34462734751914930927767269 6461762765984049548956363)
        ·
          refine ⟨9692644148976074323434545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6461762765984049548956363 9692644148976074323434545)
          ·
            refine ⟨7269483111732055742575909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9692644148976074323434545 7269483111732055742575909)
            ·
              refine ⟨1363028083449760451732983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7269483111732055742575909 1363028083449760451732983)
              ·
                refine ⟨2044542125174640677599475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363028083449760451732983 2044542125174640677599475)
                ·
                  refine ⟨3066813187761961016399213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044542125174640677599475 3066813187761961016399213)
                  ·
                    refine ⟨1150054945410735381149705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3066813187761961016399213 1150054945410735381149705)
                    ·
                      refine ⟨862541209058051535862279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150054945410735381149705 862541209058051535862279)
                      ·
                        rfl

theorem cell23_1679793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_1679793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679793 prefixEnd_1679793 := by exact prefixLift 1679793
  have htrace : WordTrace (prefixWord ++ tailWord_1679793) baseStart_1679793 baseEnd_1679793 := by
    simpa [prefixWord, tailWord_1679793, baseEnd_1679793] using wordTrace_append hprefix tailTrace_1679793
  have hstable : (prefixWord ++ tailWord_1679793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679793).length < 2 ^ (prefixWord ++ tailWord_1679793).sum := by decide
  have hdescent : baseEnd_1679793 < baseStart_1679793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679852 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_1679852 : Nat := 118140960795 + 1679852 * 2 ^ 59
def prefixEnd_1679852 : Nat := 4983230072969 + 3 ^ 40 * 1679852 * 2
def baseEnd_1679852 : Nat := 862571504416666805024507

theorem tailTrace_1679852 : CollatzResearch.WordTrace tailWord_1679852 prefixEnd_1679852 862571504416666805024507 := by
  unfold tailWord_1679852
  simp only [CollatzResearch.WordTrace]
  refine ⟨30634617955095287362880905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40846157273460383150507873 30634617955095287362880905)
  ·
    refine ⟨22975963466321465522160679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30634617955095287362880905 22975963466321465522160679)
    ·
      refine ⟨34463945199482198283241019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22975963466321465522160679 34463945199482198283241019)
      ·
        refine ⟨51695917799223297424861529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34463945199482198283241019 51695917799223297424861529)
        ·
          refine ⟨38771938349417473068646147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51695917799223297424861529 38771938349417473068646147)
          ·
            refine ⟨58157907524126209602969221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38771938349417473068646147 58157907524126209602969221)
            ·
              refine ⟨10904607660773664300556729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58157907524126209602969221 10904607660773664300556729)
              ·
                refine ⟨8178455745580248225417547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10904607660773664300556729 8178455745580248225417547)
                ·
                  refine ⟨12267683618370372338126321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8178455745580248225417547 12267683618370372338126321)
                  ·
                    refine ⟨9200762713777779253594741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12267683618370372338126321 9200762713777779253594741)
                    ·
                      refine ⟨862571504416666805024507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9200762713777779253594741 862571504416666805024507)
                      ·
                        rfl

theorem cell23_1679852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_1679852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679852 prefixEnd_1679852 := by exact prefixLift 1679852
  have htrace : WordTrace (prefixWord ++ tailWord_1679852) baseStart_1679852 baseEnd_1679852 := by
    simpa [prefixWord, tailWord_1679852, baseEnd_1679852] using wordTrace_append hprefix tailTrace_1679852
  have hstable : (prefixWord ++ tailWord_1679852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679852).length < 2 ^ (prefixWord ++ tailWord_1679852).sum := by decide
  have hdescent : baseEnd_1679852 < baseStart_1679852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679874 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_1679874 : Nat := 118140960795 + 1679874 * 2 ^ 59
def prefixEnd_1679874 : Nat := 4983230072969 + 3 ^ 40 * 1679874 * 2
def baseEnd_1679874 : Nat := 862582800991065718949407

theorem tailTrace_1679874 : CollatzResearch.WordTrace tailWord_1679874 prefixEnd_1679874 862582800991065718949407 := by
  unfold tailWord_1679874
  simp only [CollatzResearch.WordTrace]
  refine ⟨15317509579027718120765669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40846692210740581655375117 15317509579027718120765669)
  ·
    refine ⟨2872033046067697147643563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15317509579027718120765669 2872033046067697147643563)
    ·
      refine ⟨4308049569101545721465345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872033046067697147643563 4308049569101545721465345)
      ·
        refine ⟨3231037176826159291099009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4308049569101545721465345 3231037176826159291099009)
        ·
          refine ⟨2423277882619619468324257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3231037176826159291099009 2423277882619619468324257)
          ·
            refine ⟨1817458411964714601243193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2423277882619619468324257 1817458411964714601243193)
            ·
              refine ⟨1363093808973535950932395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817458411964714601243193 1363093808973535950932395)
              ·
                refine ⟨2044640713460303926398593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363093808973535950932395 2044640713460303926398593)
                ·
                  refine ⟨1533480535095227944798945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2044640713460303926398593 1533480535095227944798945)
                  ·
                    refine ⟨1150110401321420958599209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1533480535095227944798945 1150110401321420958599209)
                    ·
                      refine ⟨862582800991065718949407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150110401321420958599209 862582800991065718949407)
                      ·
                        rfl

theorem cell23_1679874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_1679874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679874 prefixEnd_1679874 := by exact prefixLift 1679874
  have htrace : WordTrace (prefixWord ++ tailWord_1679874) baseStart_1679874 baseEnd_1679874 := by
    simpa [prefixWord, tailWord_1679874, baseEnd_1679874] using wordTrace_append hprefix tailTrace_1679874
  have hstable : (prefixWord ++ tailWord_1679874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679874).length < 2 ^ (prefixWord ++ tailWord_1679874).sum := by decide
  have hdescent : baseEnd_1679874 < baseStart_1679874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679896 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1679896 : Nat := 118140960795 + 1679896 * 2 ^ 59
def prefixEnd_1679896 : Nat := 4983230072969 + 3 ^ 40 * 1679896 * 2
def baseEnd_1679896 : Nat := 862594097565464632874305

theorem tailTrace_1679896 : CollatzResearch.WordTrace tailWord_1679896 prefixEnd_1679896 862594097565464632874305 := by
  unfold tailWord_1679896
  simp only [CollatzResearch.WordTrace]
  refine ⟨30635420361015585120181771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40847227148020780160242361 30635420361015585120181771)
  ·
    refine ⟨45953130541523377680272657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30635420361015585120181771 45953130541523377680272657)
    ·
      refine ⟨34464847906142533260204493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45953130541523377680272657 34464847906142533260204493)
      ·
        refine ⟨12924317964803449972576685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34464847906142533260204493 12924317964803449972576685)
        ·
          refine ⟨4846619236801293739716257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12924317964803449972576685 4846619236801293739716257)
          ·
            refine ⟨3634964427600970304787193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4846619236801293739716257 3634964427600970304787193)
            ·
              refine ⟨2726223320700727728590395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3634964427600970304787193 2726223320700727728590395)
              ·
                refine ⟨4089334981051091592885593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726223320700727728590395 4089334981051091592885593)
                ·
                  refine ⟨3067001235788318694664195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4089334981051091592885593 3067001235788318694664195)
                  ·
                    refine ⟨4600501853682478041996293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3067001235788318694664195 4600501853682478041996293)
                    ·
                      refine ⟨862594097565464632874305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4600501853682478041996293 862594097565464632874305)
                      ·
                        rfl

theorem cell23_1679896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1679896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679896 prefixEnd_1679896 := by exact prefixLift 1679896
  have htrace : WordTrace (prefixWord ++ tailWord_1679896) baseStart_1679896 baseEnd_1679896 := by
    simpa [prefixWord, tailWord_1679896, baseEnd_1679896] using wordTrace_append hprefix tailTrace_1679896
  have hstable : (prefixWord ++ tailWord_1679896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679896).length < 2 ^ (prefixWord ++ tailWord_1679896).sum := by decide
  have hdescent : baseEnd_1679896 < baseStart_1679896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679946 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_1679946 : Nat := 118140960795 + 1679946 * 2 ^ 59
def prefixEnd_1679946 : Nat := 4983230072969 + 3 ^ 40 * 1679946 * 2
def baseEnd_1679946 : Nat := 862619771598189437249075

theorem tailTrace_1679946 : CollatzResearch.WordTrace tailWord_1679946 prefixEnd_1679946 862619771598189437249075 := by
  unfold tailWord_1679946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15318166092962507194920923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40848442914566685853122461 15318166092962507194920923)
  ·
    refine ⟨22977249139443760792381385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15318166092962507194920923 22977249139443760792381385)
    ·
      refine ⟨17232936854582820594286039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22977249139443760792381385 17232936854582820594286039)
      ·
        refine ⟨25849405281874230891429059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17232936854582820594286039 25849405281874230891429059)
        ·
          refine ⟨38774107922811346337143589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25849405281874230891429059 38774107922811346337143589)
          ·
            refine ⟨7270145235527127438214423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38774107922811346337143589 7270145235527127438214423)
            ·
              refine ⟨10905217853290691157321635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7270145235527127438214423 10905217853290691157321635)
              ·
                refine ⟨16357826779936036735982453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10905217853290691157321635 16357826779936036735982453)
                ·
                  refine ⟨1533546260619003443998355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16357826779936036735982453 1533546260619003443998355)
                  ·
                    refine ⟨2300319390928505165997533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1533546260619003443998355 2300319390928505165997533)
                    ·
                      refine ⟨862619771598189437249075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2300319390928505165997533 862619771598189437249075)
                      ·
                        rfl

theorem cell23_1679946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_1679946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679946 prefixEnd_1679946 := by exact prefixLift 1679946
  have htrace : WordTrace (prefixWord ++ tailWord_1679946) baseStart_1679946 baseEnd_1679946 := by
    simpa [prefixWord, tailWord_1679946, baseEnd_1679946] using wordTrace_append hprefix tailTrace_1679946
  have hstable : (prefixWord ++ tailWord_1679946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679946).length < 2 ^ (prefixWord ++ tailWord_1679946).sum := by decide
  have hdescent : baseEnd_1679946 < baseStart_1679946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679970 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 6]
def baseStart_1679970 : Nat := 118140960795 + 1679970 * 2 ^ 59
def prefixEnd_1679970 : Nat := 4983230072969 + 3 ^ 40 * 1679970 * 2
def baseEnd_1679970 : Nat := 95848010570433038149885

theorem tailTrace_1679970 : CollatzResearch.WordTrace tailWord_1679970 prefixEnd_1679970 95848010570433038149885 := by
  unfold tailWord_1679970
  simp only [CollatzResearch.WordTrace]
  refine ⟨15318384930940770219639341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40849026482508720585704909 15318384930940770219639341)
  ·
    refine ⟨5744394349102788832364753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15318384930940770219639341 5744394349102788832364753)
    ·
      refine ⟨4308295761827091624273565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5744394349102788832364753 4308295761827091624273565)
      ·
        refine ⟨1615610910685159359102587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4308295761827091624273565 1615610910685159359102587)
        ·
          refine ⟨2423416366027739038653881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615610910685159359102587 2423416366027739038653881)
          ·
            refine ⟨1817562274520804278990411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2423416366027739038653881 1817562274520804278990411)
            ·
              refine ⟨2726343411781206418485617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817562274520804278990411 2726343411781206418485617)
              ·
                refine ⟨2044757558835904813864213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726343411781206418485617 2044757558835904813864213)
                ·
                  refine ⟨95848010570433038149885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2044757558835904813864213 95848010570433038149885)
                  ·
                    rfl

theorem cell23_1679970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_1679970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679970 prefixEnd_1679970 := by exact prefixLift 1679970
  have htrace : WordTrace (prefixWord ++ tailWord_1679970) baseStart_1679970 baseEnd_1679970 := by
    simpa [prefixWord, tailWord_1679970, baseEnd_1679970] using wordTrace_append hprefix tailTrace_1679970
  have hstable : (prefixWord ++ tailWord_1679970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679970).length < 2 ^ (prefixWord ++ tailWord_1679970).sum := by decide
  have hdescent : baseEnd_1679970 < baseStart_1679970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679996 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_1679996 : Nat := 118140960795 + 1679996 * 2 ^ 59
def prefixEnd_1679996 : Nat := 4983230072969 + 3 ^ 40 * 1679996 * 2
def baseEnd_1679996 : Nat := 287548481876971413874615

theorem tailTrace_1679996 : CollatzResearch.WordTrace tailWord_1679996 prefixEnd_1679996 287548481876971413874615 := by
  unfold tailWord_1679996
  simp only [CollatzResearch.WordTrace]
  refine ⟨30637244010834443659501921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40849658681112591546002561 30637244010834443659501921)
  ·
    refine ⟨22977933008125832744626441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30637244010834443659501921 22977933008125832744626441)
    ·
      refine ⟨17233449756094374558469831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22977933008125832744626441 17233449756094374558469831)
      ·
        refine ⟨25850174634141561837704747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17233449756094374558469831 25850174634141561837704747)
        ·
          refine ⟨38775261951212342756557121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25850174634141561837704747 38775261951212342756557121)
          ·
            refine ⟨29081446463409257067417841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38775261951212342756557121 29081446463409257067417841)
            ·
              refine ⟨21811084847556942800563381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29081446463409257067417841 21811084847556942800563381)
              ·
                refine ⟨2044789204458463387552817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21811084847556942800563381 2044789204458463387552817)
                ·
                  refine ⟨1533591903343847540664613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2044789204458463387552817 1533591903343847540664613)
                  ·
                    refine ⟨287548481876971413874615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1533591903343847540664613 287548481876971413874615)
                    ·
                      rfl

theorem cell23_1679996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_1679996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679996 prefixEnd_1679996 := by exact prefixLift 1679996
  have htrace : WordTrace (prefixWord ++ tailWord_1679996) baseStart_1679996 baseEnd_1679996 := by
    simpa [prefixWord, tailWord_1679996, baseEnd_1679996] using wordTrace_append hprefix tailTrace_1679996
  have hstable : (prefixWord ++ tailWord_1679996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679996).length < 2 ^ (prefixWord ++ tailWord_1679996).sum := by decide
  have hdescent : baseEnd_1679996 < baseStart_1679996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679999 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 4]
def baseStart_1679999 : Nat := 118140960795 + 1679999 * 2 ^ 59
def prefixEnd_1679999 : Nat := 4983230072969 + 3 ^ 40 * 1679999 * 2
def baseEnd_1679999 : Nat := 862646986072877729886331

theorem tailTrace_1679999 : CollatzResearch.WordTrace tailWord_1679999 prefixEnd_1679999 862646986072877729886331 := by
  unfold tailWord_1679999
  simp only [CollatzResearch.WordTrace]
  refine ⟨61274597440658018831363051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40849731627105345887575367 61274597440658018831363051)
  ·
    refine ⟨91911896160987028247044577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61274597440658018831363051 91911896160987028247044577)
    ·
      refine ⟨68933922120740271185283433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91911896160987028247044577 68933922120740271185283433)
      ·
        refine ⟨51700441590555203388962575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68933922120740271185283433 51700441590555203388962575)
        ·
          refine ⟨77550662385832805083443863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51700441590555203388962575 77550662385832805083443863)
          ·
            refine ⟨116325993578749207625165795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77550662385832805083443863 116325993578749207625165795)
            ·
              refine ⟨174488990368123811437748693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116325993578749207625165795 174488990368123811437748693)
              ·
                refine ⟨4089585711752901830572235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 174488990368123811437748693 4089585711752901830572235)
                ·
                  refine ⟨6134378567629352745858353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089585711752901830572235 6134378567629352745858353)
                  ·
                    refine ⟨4600783925722014559393765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6134378567629352745858353 4600783925722014559393765)
                    ·
                      refine ⟨862646986072877729886331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4600783925722014559393765 862646986072877729886331)
                      ·
                        rfl

theorem cell23_1679999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_1679999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1679999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1679999 prefixEnd_1679999 := by exact prefixLift 1679999
  have htrace : WordTrace (prefixWord ++ tailWord_1679999) baseStart_1679999 baseEnd_1679999 := by
    simpa [prefixWord, tailWord_1679999, baseEnd_1679999] using wordTrace_append hprefix tailTrace_1679999
  have hstable : (prefixWord ++ tailWord_1679999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679999).length < 2 ^ (prefixWord ++ tailWord_1679999).sum := by decide
  have hdescent : baseEnd_1679999 < baseStart_1679999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680003 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 3, 2, 2]
def baseStart_1680003 : Nat := 118140960795 + 1680003 * 2 ^ 59
def prefixEnd_1680003 : Nat := 4983230072969 + 3 ^ 40 * 1680003 * 2
def baseEnd_1680003 : Nat := 862649039995495714236313

theorem tailTrace_1680003 : CollatzResearch.WordTrace tailWord_1680003 prefixEnd_1680003 862649039995495714236313 := by
  unfold tailWord_1680003
  simp only [CollatzResearch.WordTrace]
  refine ⟨61274743332643527514508663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40849828888429018343005775 61274743332643527514508663)
  ·
    refine ⟨91912114998965291271762995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61274743332643527514508663 91912114998965291271762995)
    ·
      refine ⟨137868172498447936907644493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91912114998965291271762995 137868172498447936907644493)
      ·
        refine ⟨51700564686917976340366685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137868172498447936907644493 51700564686917976340366685)
        ·
          refine ⟨19387711757594241127637507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51700564686917976340366685 19387711757594241127637507)
          ·
            refine ⟨29081567636391361691456261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19387711757594241127637507 29081567636391361691456261)
            ·
              refine ⟨5452793931823380317148049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29081567636391361691456261 5452793931823380317148049)
              ·
                refine ⟨4089595448867535237861037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5452793931823380317148049 4089595448867535237861037)
                ·
                  refine ⟨1533598293325325714197889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4089595448867535237861037 1533598293325325714197889)
                  ·
                    refine ⟨1150198719993994285648417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1533598293325325714197889 1150198719993994285648417)
                    ·
                      refine ⟨862649039995495714236313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150198719993994285648417 862649039995495714236313)
                      ·
                        rfl

theorem cell23_1680003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_1680003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680003 prefixEnd_1680003 := by exact prefixLift 1680003
  have htrace : WordTrace (prefixWord ++ tailWord_1680003) baseStart_1680003 baseEnd_1680003 := by
    simpa [prefixWord, tailWord_1680003, baseEnd_1680003] using wordTrace_append hprefix tailTrace_1680003
  have hstable : (prefixWord ++ tailWord_1680003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680003).length < 2 ^ (prefixWord ++ tailWord_1680003).sum := by decide
  have hdescent : baseEnd_1680003 < baseStart_1680003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680054 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_1680054 : Nat := 118140960795 + 1680054 * 2 ^ 59
def prefixEnd_1680054 : Nat := 4983230072969 + 3 ^ 40 * 1680054 * 2
def baseEnd_1680054 : Nat := 862675227508875014698579

theorem tailTrace_1680054 : CollatzResearch.WordTrace tailWord_1680054 prefixEnd_1680054 862675227508875014698579 := by
  unfold tailWord_1680054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3829787715966172701538451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40851068970305842149743477 3829787715966172701538451)
  ·
    refine ⟨5744681573949259052307677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3829787715966172701538451 5744681573949259052307677)
    ·
      refine ⟨2154255590230972144615379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5744681573949259052307677 2154255590230972144615379)
      ·
        refine ⟨3231383385346458216923069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154255590230972144615379 3231383385346458216923069)
        ·
          refine ⟨1211768769504921831346151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3231383385346458216923069 1211768769504921831346151)
          ·
            refine ⟨1817653154257382747019227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211768769504921831346151 1817653154257382747019227)
            ·
              refine ⟨2726479731386074120528841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817653154257382747019227 2726479731386074120528841)
              ·
                refine ⟨2044859798539555590396631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726479731386074120528841 2044859798539555590396631)
                ·
                  refine ⟨3067289697809333385594947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044859798539555590396631 3067289697809333385594947)
                  ·
                    refine ⟨4600934546714000078392421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3067289697809333385594947 4600934546714000078392421)
                    ·
                      refine ⟨862675227508875014698579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4600934546714000078392421 862675227508875014698579)
                      ·
                        rfl

theorem cell23_1680054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_1680054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680054 prefixEnd_1680054 := by exact prefixLift 1680054
  have htrace : WordTrace (prefixWord ++ tailWord_1680054) baseStart_1680054 baseEnd_1680054 := by
    simpa [prefixWord, tailWord_1680054, baseEnd_1680054] using wordTrace_append hprefix tailTrace_1680054
  have hstable : (prefixWord ++ tailWord_1680054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680054).length < 2 ^ (prefixWord ++ tailWord_1680054).sum := by decide
  have hdescent : baseEnd_1680054 < baseStart_1680054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680063 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 3, 3, 2]
def baseStart_1680063 : Nat := 118140960795 + 1680063 * 2 ^ 59
def prefixEnd_1680063 : Nat := 4983230072969 + 3 ^ 40 * 1680063 * 2
def baseEnd_1680063 : Nat := 862679848834765479486037

theorem tailTrace_1680063 : CollatzResearch.WordTrace tailWord_1680063 prefixEnd_1680063 862679848834765479486037 := by
  unfold tailWord_1680063
  simp only [CollatzResearch.WordTrace]
  refine ⟨61276931712426157761692843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40851287808284105174461895 61276931712426157761692843)
  ·
    refine ⟨91915397568639236642539265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61276931712426157761692843 91915397568639236642539265)
    ·
      refine ⟨68936548176479427481904449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91915397568639236642539265 68936548176479427481904449)
      ·
        refine ⟨51702411132359570611428337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68936548176479427481904449 51702411132359570611428337)
        ·
          refine ⟨38776808349269677958571253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51702411132359570611428337 38776808349269677958571253)
          ·
            refine ⟨3635325782744032308616055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38776808349269677958571253 3635325782744032308616055)
            ·
              refine ⟨5452988674116048462924083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635325782744032308616055 5452988674116048462924083)
              ·
                refine ⟨8179483011174072694386125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452988674116048462924083 8179483011174072694386125)
                ·
                  refine ⟨3067306129190277260394797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8179483011174072694386125 3067306129190277260394797)
                  ·
                    refine ⟨1150239798446353972648049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3067306129190277260394797 1150239798446353972648049)
                    ·
                      refine ⟨862679848834765479486037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150239798446353972648049 862679848834765479486037)
                      ·
                        rfl

theorem cell23_1680063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_1680063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680063 prefixEnd_1680063 := by exact prefixLift 1680063
  have htrace : WordTrace (prefixWord ++ tailWord_1680063) baseStart_1680063 baseEnd_1680063 := by
    simpa [prefixWord, tailWord_1680063, baseEnd_1680063] using wordTrace_append hprefix tailTrace_1680063
  have hstable : (prefixWord ++ tailWord_1680063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680063).length < 2 ^ (prefixWord ++ tailWord_1680063).sum := by decide
  have hdescent : baseEnd_1680063 < baseStart_1680063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680110 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_1680110 : Nat := 118140960795 + 1680110 * 2 ^ 59
def prefixEnd_1680110 : Nat := 4983230072969 + 3 ^ 40 * 1680110 * 2
def baseEnd_1680110 : Nat := 862703982425526795598321

theorem tailTrace_1680110 : CollatzResearch.WordTrace tailWord_1680110 prefixEnd_1680110 862703982425526795598321 := by
  unfold tailWord_1680110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659830742906985598581723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40852430628837256525769189 7659830742906985598581723)
  ·
    refine ⟨11489746114360478397872585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7659830742906985598581723 11489746114360478397872585)
    ·
      refine ⟨8617309585770358798404439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11489746114360478397872585 8617309585770358798404439)
      ·
        refine ⟨12925964378655538197606659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8617309585770358798404439 12925964378655538197606659)
        ·
          refine ⟨19388946567983307296409989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12925964378655538197606659 19388946567983307296409989)
          ·
            refine ⟨3635427481496870118076873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19388946567983307296409989 3635427481496870118076873)
            ·
              refine ⟨2726570611122652588557655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3635427481496870118076873 2726570611122652588557655)
              ·
                refine ⟨4089855916683978882836483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726570611122652588557655 4089855916683978882836483)
                ·
                  refine ⟨6134783875025968324254725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089855916683978882836483 6134783875025968324254725)
                  ·
                    refine ⟨1150271976567369060797761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6134783875025968324254725 1150271976567369060797761)
                    ·
                      refine ⟨862703982425526795598321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150271976567369060797761 862703982425526795598321)
                      ·
                        rfl

theorem cell23_1680110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_1680110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680110 prefixEnd_1680110 := by exact prefixLift 1680110
  have htrace : WordTrace (prefixWord ++ tailWord_1680110) baseStart_1680110 baseEnd_1680110 := by
    simpa [prefixWord, tailWord_1680110, baseEnd_1680110] using wordTrace_append hprefix tailTrace_1680110
  have hstable : (prefixWord ++ tailWord_1680110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680110).length < 2 ^ (prefixWord ++ tailWord_1680110).sum := by decide
  have hdescent : baseEnd_1680110 < baseStart_1680110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680243 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 1, 5, 2]
def baseStart_1680243 : Nat := 118140960795 + 1680243 * 2 ^ 59
def prefixEnd_1680243 : Nat := 4983230072969 + 3 ^ 40 * 1680243 * 2
def baseEnd_1680243 : Nat := 862772275352574775235209

theorem tailTrace_1680243 : CollatzResearch.WordTrace tailWord_1680243 prefixEnd_1680243 862772275352574775235209 := by
  unfold tailWord_1680243
  simp only [CollatzResearch.WordTrace]
  refine ⟨61283496851774048503245383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40855664567849365668830255 61283496851774048503245383)
  ·
    refine ⟨91925245277661072754868075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61283496851774048503245383 91925245277661072754868075)
    ·
      refine ⟨137887867916491609132302113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91925245277661072754868075 137887867916491609132302113)
      ·
        refine ⟨103415900937368706849226585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137887867916491609132302113 103415900937368706849226585)
        ·
          refine ⟨77561925703026530136919939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103415900937368706849226585 77561925703026530136919939)
          ·
            refine ⟨116342888554539795205379909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77561925703026530136919939 116342888554539795205379909)
            ·
              refine ⟨21814291603976211601008733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116342888554539795205379909 21814291603976211601008733)
              ·
                refine ⟨8180359351491079350378275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21814291603976211601008733 8180359351491079350378275)
                ·
                  refine ⟨12270539027236619025567413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8180359351491079350378275 12270539027236619025567413)
                  ·
                    refine ⟨1150363033803433033646945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12270539027236619025567413 1150363033803433033646945)
                    ·
                      refine ⟨862772275352574775235209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150363033803433033646945 862772275352574775235209)
                      ·
                        rfl

theorem cell23_1680243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 5, 2].length) (baseStart_1680243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680243 prefixEnd_1680243 := by exact prefixLift 1680243
  have htrace : WordTrace (prefixWord ++ tailWord_1680243) baseStart_1680243 baseEnd_1680243 := by
    simpa [prefixWord, tailWord_1680243, baseEnd_1680243] using wordTrace_append hprefix tailTrace_1680243
  have hstable : (prefixWord ++ tailWord_1680243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680243).length < 2 ^ (prefixWord ++ tailWord_1680243).sum := by decide
  have hdescent : baseEnd_1680243 < baseStart_1680243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680253 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_1680253 : Nat := 118140960795 + 1680253 * 2 ^ 59
def prefixEnd_1680253 : Nat := 4983230072969 + 3 ^ 40 * 1680253 * 2
def baseEnd_1680253 : Nat := 287592470053039912036721

theorem tailTrace_1680253 : CollatzResearch.WordTrace tailWord_1680253 prefixEnd_1680253 287592470053039912036721 := by
  unfold tailWord_1680253
  simp only [CollatzResearch.WordTrace]
  refine ⟨61283861581737820211109413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40855907721158546807406275 61283861581737820211109413)
  ·
    refine ⟨11490724046575841289583015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61283861581737820211109413 11490724046575841289583015)
    ·
      refine ⟨17236086069863761934374523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11490724046575841289583015 17236086069863761934374523)
      ·
        refine ⟨25854129104795642901561785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17236086069863761934374523 25854129104795642901561785)
        ·
          refine ⟨19390596828596732176171339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25854129104795642901561785 19390596828596732176171339)
          ·
            refine ⟨29085895242895098264257009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19390596828596732176171339 29085895242895098264257009)
            ·
              refine ⟨21814421432171323698192757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29085895242895098264257009 21814421432171323698192757)
              ·
                refine ⟨2045102009266061596705571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21814421432171323698192757 2045102009266061596705571)
                ·
                  refine ⟨3067653013899092395058357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045102009266061596705571 3067653013899092395058357)
                  ·
                    refine ⟨287592470053039912036721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3067653013899092395058357 287592470053039912036721)
                    ·
                      rfl

theorem cell23_1680253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_1680253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680253 prefixEnd_1680253 := by exact prefixLift 1680253
  have htrace : WordTrace (prefixWord ++ tailWord_1680253) baseStart_1680253 baseEnd_1680253 := by
    simpa [prefixWord, tailWord_1680253, baseEnd_1680253] using wordTrace_append hprefix tailTrace_1680253
  have hstable : (prefixWord ++ tailWord_1680253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680253).length < 2 ^ (prefixWord ++ tailWord_1680253).sum := by decide
  have hdescent : baseEnd_1680253 < baseStart_1680253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680273 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 2, 6, 2]
def baseStart_1680273 : Nat := 118140960795 + 1680273 * 2 ^ 59
def prefixEnd_1680273 : Nat := 4983230072969 + 3 ^ 40 * 1680273 * 2
def baseEnd_1680273 : Nat := 862787679772209657860071

theorem tailTrace_1680273 : CollatzResearch.WordTrace tailWord_1680273 prefixEnd_1680273 862787679772209657860071 := by
  unfold tailWord_1680273
  simp only [CollatzResearch.WordTrace]
  refine ⟨61284591041665363626837473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40856394027776909084558315 61284591041665363626837473)
  ·
    refine ⟨45963443281249022720128105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61284591041665363626837473 45963443281249022720128105)
    ·
      refine ⟨34472582460936767040096079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45963443281249022720128105 34472582460936767040096079)
      ·
        refine ⟨51708873691405150560144119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34472582460936767040096079 51708873691405150560144119)
        ·
          refine ⟨77563310537107725840216179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51708873691405150560144119 77563310537107725840216179)
          ·
            refine ⟨116344965805661588760324269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77563310537107725840216179 116344965805661588760324269)
            ·
              refine ⟨43629362177123095785121601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116344965805661588760324269 43629362177123095785121601)
              ·
                refine ⟨32722021632842321838841201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43629362177123095785121601 32722021632842321838841201)
                ·
                  refine ⟨24541516224631741379130901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32722021632842321838841201 24541516224631741379130901)
                  ·
                    refine ⟨1150383573029612877146761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24541516224631741379130901 1150383573029612877146761)
                    ·
                      refine ⟨862787679772209657860071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150383573029612877146761 862787679772209657860071)
                      ·
                        rfl

theorem cell23_1680273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_1680273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680273 prefixEnd_1680273 := by exact prefixLift 1680273
  have htrace : WordTrace (prefixWord ++ tailWord_1680273) baseStart_1680273 baseEnd_1680273 := by
    simpa [prefixWord, tailWord_1680273, baseEnd_1680273] using wordTrace_append hprefix tailTrace_1680273
  have hstable : (prefixWord ++ tailWord_1680273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680273).length < 2 ^ (prefixWord ++ tailWord_1680273).sum := by decide
  have hdescent : baseEnd_1680273 < baseStart_1680273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680290 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1680290 : Nat := 118140960795 + 1680290 * 2 ^ 59
def prefixEnd_1680290 : Nat := 4983230072969 + 3 ^ 40 * 1680290 * 2
def baseEnd_1680290 : Nat := 862796408943336091347493

theorem tailTrace_1680290 : CollatzResearch.WordTrace tailWord_1680290 prefixEnd_1680290 862796408943336091347493 := by
  unfold tailWord_1680290
  simp only [CollatzResearch.WordTrace]
  refine ⟨15321302770650943882551581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40856807388402517020137549 15321302770650943882551581)
  ·
    refine ⟨5745488538994103955956843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15321302770650943882551581 5745488538994103955956843)
    ·
      refine ⟨8618232808491155933935265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5745488538994103955956843 8618232808491155933935265)
      ·
        refine ⟨6463674606368366950451449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8618232808491155933935265 6463674606368366950451449)
        ·
          refine ⟨4847755954776275212838587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6463674606368366950451449 4847755954776275212838587)
          ·
            refine ⟨7271633932164412819257881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847755954776275212838587 7271633932164412819257881)
            ·
              refine ⟨5453725449123309614443411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7271633932164412819257881 5453725449123309614443411)
              ·
                refine ⟨8180588173684964421665117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453725449123309614443411 8180588173684964421665117)
                ·
                  refine ⟨3067720565131861658124419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8180588173684964421665117 3067720565131861658124419)
                  ·
                    refine ⟨4601580847697792487186629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3067720565131861658124419 4601580847697792487186629)
                    ·
                      refine ⟨862796408943336091347493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4601580847697792487186629 862796408943336091347493)
                      ·
                        rfl

theorem cell23_1680290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1680290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680290 prefixEnd_1680290 := by exact prefixLift 1680290
  have htrace : WordTrace (prefixWord ++ tailWord_1680290) baseStart_1680290 baseEnd_1680290 := by
    simpa [prefixWord, tailWord_1680290, baseEnd_1680290] using wordTrace_append hprefix tailTrace_1680290
  have hstable : (prefixWord ++ tailWord_1680290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680290).length < 2 ^ (prefixWord ++ tailWord_1680290).sum := by decide
  have hdescent : baseEnd_1680290 < baseStart_1680290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680367 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 1, 3, 2]
def baseStart_1680367 : Nat := 118140960795 + 1680367 * 2 ^ 59
def prefixEnd_1680367 : Nat := 4983230072969 + 3 ^ 40 * 1680367 * 2
def baseEnd_1680367 : Nat := 862835946953732290084639

theorem tailTrace_1680367 : CollatzResearch.WordTrace tailWord_1680367 prefixEnd_1680367 862835946953732290084639 := by
  unfold tailWord_1680367
  simp only [CollatzResearch.WordTrace]
  refine ⟨61288019503324817680759355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40858679668883211787172903 61288019503324817680759355)
  ·
    refine ⟨91932029254987226521139033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61288019503324817680759355 91932029254987226521139033)
    ·
      refine ⟨68949021941240419890854275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91932029254987226521139033 68949021941240419890854275)
      ·
        refine ⟨103423532911860629836281413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68949021941240419890854275 103423532911860629836281413)
        ·
          refine ⟨19391912420973868094302765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103423532911860629836281413 19391912420973868094302765)
          ·
            refine ⟨7271967157865200535363537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19391912420973868094302765 7271967157865200535363537)
            ·
              refine ⟨5453975368398900401522653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7271967157865200535363537 5453975368398900401522653)
              ·
                refine ⟨2045240763149587650570995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5453975368398900401522653 2045240763149587650570995)
                ·
                  refine ⟨3067861144724381475856493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045240763149587650570995 3067861144724381475856493)
                  ·
                    refine ⟨1150447929271643053446185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3067861144724381475856493 1150447929271643053446185)
                    ·
                      refine ⟨862835946953732290084639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150447929271643053446185 862835946953732290084639)
                      ·
                        rfl

theorem cell23_1680367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 3, 2].length) (baseStart_1680367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680367 prefixEnd_1680367 := by exact prefixLift 1680367
  have htrace : WordTrace (prefixWord ++ tailWord_1680367) baseStart_1680367 baseEnd_1680367 := by
    simpa [prefixWord, tailWord_1680367, baseEnd_1680367] using wordTrace_append hprefix tailTrace_1680367
  have hstable : (prefixWord ++ tailWord_1680367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680367).length < 2 ^ (prefixWord ++ tailWord_1680367).sum := by decide
  have hdescent : baseEnd_1680367 < baseStart_1680367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680393 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_1680393 : Nat := 118140960795 + 1680393 * 2 ^ 59
def prefixEnd_1680393 : Nat := 4983230072969 + 3 ^ 40 * 1680393 * 2
def baseEnd_1680393 : Nat := 862849297450749188359519

theorem tailTrace_1680393 : CollatzResearch.WordTrace tailWord_1680393 prefixEnd_1680393 862849297450749188359519 := by
  unfold tailWord_1680393
  simp only [CollatzResearch.WordTrace]
  refine ⟨61288967801230624121205833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40859311867487082747470555 61288967801230624121205833)
  ·
    refine ⟨45966725850922968090904375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61288967801230624121205833 45966725850922968090904375)
    ·
      refine ⟨68950088776384452136356563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45966725850922968090904375 68950088776384452136356563)
      ·
        refine ⟨103425133164576678204534845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68950088776384452136356563 103425133164576678204534845)
        ·
          refine ⟨38784424936716254326700567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103425133164576678204534845 38784424936716254326700567)
          ·
            refine ⟨58176637405074381490050851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38784424936716254326700567 58176637405074381490050851)
            ·
              refine ⟨87264956107611572235076277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58176637405074381490050851 87264956107611572235076277)
              ·
                refine ⟨8181089635088584897038401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87264956107611572235076277 8181089635088584897038401)
                ·
                  refine ⟨6135817226316438672778801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8181089635088584897038401 6135817226316438672778801)
                  ·
                    refine ⟨4601862919737329004584101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6135817226316438672778801 4601862919737329004584101)
                    ·
                      refine ⟨862849297450749188359519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4601862919737329004584101 862849297450749188359519)
                      ·
                        rfl

theorem cell23_1680393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_1680393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680393 prefixEnd_1680393 := by exact prefixLift 1680393
  have htrace : WordTrace (prefixWord ++ tailWord_1680393) baseStart_1680393 baseEnd_1680393 := by
    simpa [prefixWord, tailWord_1680393, baseEnd_1680393] using wordTrace_append hprefix tailTrace_1680393
  have hstable : (prefixWord ++ tailWord_1680393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680393).length < 2 ^ (prefixWord ++ tailWord_1680393).sum := by decide
  have hdescent : baseEnd_1680393 < baseStart_1680393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680473 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_1680473 : Nat := 118140960795 + 1680473 * 2 ^ 59
def prefixEnd_1680473 : Nat := 4983230072969 + 3 ^ 40 * 1680473 * 2
def baseEnd_1680473 : Nat := 862890375903108875359151

theorem tailTrace_1680473 : CollatzResearch.WordTrace tailWord_1680473 prefixEnd_1680473 862890375903108875359151 := by
  unfold tailWord_1680473
  simp only [CollatzResearch.WordTrace]
  refine ⟨61291885640940797784118073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40861257093960531856078715 61291885640940797784118073)
  ·
    refine ⟨45968914230705598338088555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61291885640940797784118073 45968914230705598338088555)
    ·
      refine ⟨68953371346058397507132833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45968914230705598338088555 68953371346058397507132833)
      ·
        refine ⟨51715028509543798130349625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68953371346058397507132833 51715028509543798130349625)
        ·
          refine ⟨38786271382157848597762219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51715028509543798130349625 38786271382157848597762219)
          ·
            refine ⟨58179407073236772896643329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38786271382157848597762219 58179407073236772896643329)
            ·
              refine ⟨43634555304927579672482497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58179407073236772896643329 43634555304927579672482497)
              ·
                refine ⟨32725916478695684754361873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43634555304927579672482497 32725916478695684754361873)
                ·
                  refine ⟨24544437359021763565771405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32725916478695684754361873 24544437359021763565771405)
                  ·
                    refine ⟨9204164009633161337164277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24544437359021763565771405 9204164009633161337164277)
                    ·
                      refine ⟨862890375903108875359151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9204164009633161337164277 862890375903108875359151)
                      ·
                        rfl

theorem cell23_1680473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_1680473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680473 prefixEnd_1680473 := by exact prefixLift 1680473
  have htrace : WordTrace (prefixWord ++ tailWord_1680473) baseStart_1680473 baseEnd_1680473 := by
    simpa [prefixWord, tailWord_1680473, baseEnd_1680473] using wordTrace_append hprefix tailTrace_1680473
  have hstable : (prefixWord ++ tailWord_1680473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680473).length < 2 ^ (prefixWord ++ tailWord_1680473).sum := by decide
  have hdescent : baseEnd_1680473 < baseStart_1680473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680480 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 5, 4]
def baseStart_1680480 : Nat := 118140960795 + 1680480 * 2 ^ 59
def prefixEnd_1680480 : Nat := 4983230072969 + 3 ^ 40 * 1680480 * 2
def baseEnd_1680480 : Nat := 287631323422563449323873

theorem tailTrace_1680480 : CollatzResearch.WordTrace tailWord_1680480 prefixEnd_1680480 287631323422563449323873 := by
  unfold tailWord_1680480
  simp only [CollatzResearch.WordTrace]
  refine ⟨30646070475957718989811447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40861427301276958653081929 30646070475957718989811447)
  ·
    refine ⟨45969105713936578484717171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30646070475957718989811447 45969105713936578484717171)
    ·
      refine ⟨68953658570904867727075757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45969105713936578484717171 68953658570904867727075757)
      ·
        refine ⟨25857621964089325397653409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68953658570904867727075757 25857621964089325397653409)
        ·
          refine ⟨19393216473066994048240057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25857621964089325397653409 19393216473066994048240057)
          ·
            refine ⟨14544912354800245536180043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19393216473066994048240057 14544912354800245536180043)
            ·
              refine ⟨21817368532200368304270065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14544912354800245536180043 21817368532200368304270065)
              ·
                refine ⟨16363026399150276228202549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21817368532200368304270065 16363026399150276228202549)
                ·
                  refine ⟨1534033724920338396393989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16363026399150276228202549 1534033724920338396393989)
                  ·
                    refine ⟨287631323422563449323873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1534033724920338396393989 287631323422563449323873)
                    ·
                      rfl

theorem cell23_1680480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5, 4].length) (baseStart_1680480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680480 prefixEnd_1680480 := by exact prefixLift 1680480
  have htrace : WordTrace (prefixWord ++ tailWord_1680480) baseStart_1680480 baseEnd_1680480 := by
    simpa [prefixWord, tailWord_1680480, baseEnd_1680480] using wordTrace_append hprefix tailTrace_1680480
  have hstable : (prefixWord ++ tailWord_1680480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680480).length < 2 ^ (prefixWord ++ tailWord_1680480).sum := by decide
  have hdescent : baseEnd_1680480 < baseStart_1680480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680487 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_1680487 : Nat := 118140960795 + 1680487 * 2 ^ 59
def prefixEnd_1680487 : Nat := 4983230072969 + 3 ^ 40 * 1680487 * 2
def baseEnd_1680487 : Nat := 862897564632271820584087

theorem tailTrace_1680487 : CollatzResearch.WordTrace tailWord_1680487 prefixEnd_1680487 862897564632271820584087 := by
  unfold tailWord_1680487
  simp only [CollatzResearch.WordTrace]
  refine ⟨61292396262890078175127715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40861597508593385450085143 61292396262890078175127715)
  ·
    refine ⟨91938594394335117262691573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61292396262890078175127715 91938594394335117262691573)
    ·
      refine ⟨8619243224468917243377335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91938594394335117262691573 8619243224468917243377335)
      ·
        refine ⟨12928864836703375865066003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8619243224468917243377335 12928864836703375865066003)
        ·
          refine ⟨19393297255055063797599005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12928864836703375865066003 19393297255055063797599005)
          ·
            refine ⟨7272486470645648924099627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19393297255055063797599005 7272486470645648924099627)
            ·
              refine ⟨10908729705968473386149441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7272486470645648924099627 10908729705968473386149441)
              ·
                refine ⟨8181547279476355039612081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10908729705968473386149441 8181547279476355039612081)
                ·
                  refine ⟨6136160459607266279709061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8181547279476355039612081 6136160459607266279709061)
                  ·
                    refine ⟨1150530086176362427445449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6136160459607266279709061 1150530086176362427445449)
                    ·
                      refine ⟨862897564632271820584087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150530086176362427445449 862897564632271820584087)
                      ·
                        rfl

theorem cell23_1680487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_1680487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680487 prefixEnd_1680487 := by exact prefixLift 1680487
  have htrace : WordTrace (prefixWord ++ tailWord_1680487) baseStart_1680487 baseEnd_1680487 := by
    simpa [prefixWord, tailWord_1680487, baseEnd_1680487] using wordTrace_append hprefix tailTrace_1680487
  have hstable : (prefixWord ++ tailWord_1680487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680487).length < 2 ^ (prefixWord ++ tailWord_1680487).sum := by decide
  have hdescent : baseEnd_1680487 < baseStart_1680487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680523 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 2, 9]
def baseStart_1680523 : Nat := 118140960795 + 1680523 * 2 ^ 59
def prefixEnd_1680523 : Nat := 4983230072969 + 3 ^ 40 * 1680523 * 2
def baseEnd_1680523 : Nat := 287638683311944559911307

theorem tailTrace_1680523 : CollatzResearch.WordTrace tailWord_1680523 prefixEnd_1680523 287638683311944559911307 := by
  unfold tailWord_1680523
  simp only [CollatzResearch.WordTrace]
  refine ⟨61293709290759656323438223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40862472860506437548958815 61293709290759656323438223)
  ·
    refine ⟨91940563936139484485157335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61293709290759656323438223 91940563936139484485157335)
    ·
      refine ⟨137910845904209226727736003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91940563936139484485157335 137910845904209226727736003)
      ·
        refine ⟨206866268856313840091604005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137910845904209226727736003 206866268856313840091604005)
        ·
          refine ⟨38787425410558845017175751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206866268856313840091604005 38787425410558845017175751)
          ·
            refine ⟨58181138115838267525763627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38787425410558845017175751 58181138115838267525763627)
            ·
              refine ⟨87271707173757401288645441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58181138115838267525763627 87271707173757401288645441)
              ·
                refine ⟨65453780380318050966484081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87271707173757401288645441 65453780380318050966484081)
                ·
                  refine ⟨49090335285238538224863061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65453780380318050966484081 49090335285238538224863061)
                  ·
                    refine ⟨287638683311944559911307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 49090335285238538224863061 287638683311944559911307)
                    ·
                      rfl

theorem cell23_1680523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 9].length) (baseStart_1680523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680523 prefixEnd_1680523 := by exact prefixLift 1680523
  have htrace : WordTrace (prefixWord ++ tailWord_1680523) baseStart_1680523 baseEnd_1680523 := by
    simpa [prefixWord, tailWord_1680523, baseEnd_1680523] using wordTrace_append hprefix tailTrace_1680523
  have hstable : (prefixWord ++ tailWord_1680523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680523).length < 2 ^ (prefixWord ++ tailWord_1680523).sum := by decide
  have hdescent : baseEnd_1680523 < baseStart_1680523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680560 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 4]
def baseStart_1680560 : Nat := 118140960795 + 1680560 * 2 ^ 59
def prefixEnd_1680560 : Nat := 4983230072969 + 3 ^ 40 * 1680560 * 2
def baseEnd_1680560 : Nat := 862935048720050034971251

theorem tailTrace_1680560 : CollatzResearch.WordTrace tailWord_1680560 prefixEnd_1680560 862935048720050034971251 := by
  unfold tailWord_1680560
  simp only [CollatzResearch.WordTrace]
  refine ⟨30647529395812805821267567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40863372527750407761690089 30647529395812805821267567)
  ·
    refine ⟨45971294093719208731901351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30647529395812805821267567 45971294093719208731901351)
    ·
      refine ⟨68956941140578813097852027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45971294093719208731901351 68956941140578813097852027)
      ·
        refine ⟨103435411710868219646778041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68956941140578813097852027 103435411710868219646778041)
        ·
          refine ⟨77576558783151164735083531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103435411710868219646778041 77576558783151164735083531)
          ·
            refine ⟨116364838174726747102625297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77576558783151164735083531 116364838174726747102625297)
            ·
              refine ⟨87273628631045060326968973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116364838174726747102625297 87273628631045060326968973)
              ·
                refine ⟨32727610736641897622613365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87273628631045060326968973 32727610736641897622613365)
                ·
                  refine ⟨3068213506560177902120003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32727610736641897622613365 3068213506560177902120003)
                  ·
                    refine ⟨4602320259840266853180005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3068213506560177902120003 4602320259840266853180005)
                    ·
                      refine ⟨862935048720050034971251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4602320259840266853180005 862935048720050034971251)
                      ·
                        rfl

theorem cell23_1680560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_1680560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680560 prefixEnd_1680560 := by exact prefixLift 1680560
  have htrace : WordTrace (prefixWord ++ tailWord_1680560) baseStart_1680560 baseEnd_1680560 := by
    simpa [prefixWord, tailWord_1680560, baseEnd_1680560] using wordTrace_append hprefix tailTrace_1680560
  have hstable : (prefixWord ++ tailWord_1680560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680560).length < 2 ^ (prefixWord ++ tailWord_1680560).sum := by decide
  have hdescent : baseEnd_1680560 < baseStart_1680560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680570 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_1680570 : Nat := 118140960795 + 1680570 * 2 ^ 59
def prefixEnd_1680570 : Nat := 4983230072969 + 3 ^ 40 * 1680570 * 2
def baseEnd_1680570 : Nat := 287646727842198331948735

theorem tailTrace_1680570 : CollatzResearch.WordTrace tailWord_1680570 prefixEnd_1680570 287646727842198331948735 := by
  unfold tailWord_1680570
  simp only [CollatzResearch.WordTrace]
  refine ⟨15323855880397345837599791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40863615681059588900266109 15323855880397345837599791)
  ·
    refine ⟨22985783820596018756399687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15323855880397345837599791 22985783820596018756399687)
    ·
      refine ⟨34478675730894028134599531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22985783820596018756399687 34478675730894028134599531)
      ·
        refine ⟨51718013596341042201899297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34478675730894028134599531 51718013596341042201899297)
        ·
          refine ⟨38788510197255781651424473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51718013596341042201899297 38788510197255781651424473)
          ·
            refine ⟨29091382647941836238568355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38788510197255781651424473 29091382647941836238568355)
            ·
              refine ⟨43637073971912754357852533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29091382647941836238568355 43637073971912754357852533)
              ·
                refine ⟨4090975684866820721048675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43637073971912754357852533 4090975684866820721048675)
                ·
                  refine ⟨6136463527300231081573013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090975684866820721048675 6136463527300231081573013)
                  ·
                    refine ⟨287646727842198331948735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6136463527300231081573013 287646727842198331948735)
                    ·
                      rfl

theorem cell23_1680570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_1680570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680570 prefixEnd_1680570 := by exact prefixLift 1680570
  have htrace : WordTrace (prefixWord ++ tailWord_1680570) baseStart_1680570 baseEnd_1680570 := by
    simpa [prefixWord, tailWord_1680570, baseEnd_1680570] using wordTrace_append hprefix tailTrace_1680570
  have hstable : (prefixWord ++ tailWord_1680570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680570).length < 2 ^ (prefixWord ++ tailWord_1680570).sum := by decide
  have hdescent : baseEnd_1680570 < baseStart_1680570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680574 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1680574 : Nat := 118140960795 + 1680574 * 2 ^ 59
def prefixEnd_1680574 : Nat := 4983230072969 + 3 ^ 40 * 1680574 * 2
def baseEnd_1680574 : Nat := 287647412483070993398729

theorem tailTrace_1680574 : CollatzResearch.WordTrace tailWord_1680574 prefixEnd_1680574 287647412483070993398729 := by
  unfold tailWord_1680574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7661946176696861504193097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40863712942383261355696517 7661946176696861504193097)
  ·
    refine ⟨5746459632522646128144823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7661946176696861504193097 5746459632522646128144823)
    ·
      refine ⟨8619689448783969192217235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746459632522646128144823 8619689448783969192217235)
      ·
        refine ⟨12929534173175953788325853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8619689448783969192217235 12929534173175953788325853)
        ·
          refine ⟨4848575314940982670622195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12929534173175953788325853 4848575314940982670622195)
          ·
            refine ⟨7272862972411474005933293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848575314940982670622195 7272862972411474005933293)
            ·
              refine ⟨2727323614654302752224985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7272862972411474005933293 2727323614654302752224985)
              ·
                refine ⟨2045492710990727064168739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2727323614654302752224985 2045492710990727064168739)
                ·
                  refine ⟨3068239066486090596253109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045492710990727064168739 3068239066486090596253109)
                  ·
                    refine ⟨287647412483070993398729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3068239066486090596253109 287647412483070993398729)
                    ·
                      rfl

theorem cell23_1680574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1680574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680574 prefixEnd_1680574 := by exact prefixLift 1680574
  have htrace : WordTrace (prefixWord ++ tailWord_1680574) baseStart_1680574 baseEnd_1680574 := by
    simpa [prefixWord, tailWord_1680574, baseEnd_1680574] using wordTrace_append hprefix tailTrace_1680574
  have hstable : (prefixWord ++ tailWord_1680574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680574).length < 2 ^ (prefixWord ++ tailWord_1680574).sum := by decide
  have hdescent : baseEnd_1680574 < baseStart_1680574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680600 : List Nat := [2, 1, 2, 2, 5, 11]
def baseStart_1680600 : Nat := 118140960795 + 1680600 * 2 ^ 59
def prefixEnd_1680600 : Nat := 4983230072969 + 3 ^ 40 * 1680600 * 2
def baseEnd_1680600 : Nat := 3551257563564732010169

theorem tailTrace_1680600 : CollatzResearch.WordTrace tailWord_1680600 prefixEnd_1680600 3551257563564732010169 := by
  unfold tailWord_1680600
  simp only [CollatzResearch.WordTrace]
  refine ⟨30648258855740349236995627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40864345140987132315994169 30648258855740349236995627)
  ·
    refine ⟨45972388283610523855493441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30648258855740349236995627 45972388283610523855493441)
    ·
      refine ⟨34479291212707892891620081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45972388283610523855493441 34479291212707892891620081)
      ·
        refine ⟨25859468409530919668715061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34479291212707892891620081 25859468409530919668715061)
        ·
          refine ⟨2424325163393523718942037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25859468409530919668715061 2424325163393523718942037)
          ·
            refine ⟨3551257563564732010169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2424325163393523718942037 3551257563564732010169)
            ·
              rfl

theorem cell23_1680600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 11].length) (baseStart_1680600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680600 prefixEnd_1680600 := by exact prefixLift 1680600
  have htrace : WordTrace (prefixWord ++ tailWord_1680600) baseStart_1680600 baseEnd_1680600 := by
    simpa [prefixWord, tailWord_1680600, baseEnd_1680600] using wordTrace_append hprefix tailTrace_1680600
  have hstable : (prefixWord ++ tailWord_1680600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680600).length < 2 ^ (prefixWord ++ tailWord_1680600).sum := by decide
  have hdescent : baseEnd_1680600 < baseStart_1680600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680627 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 3]
def baseStart_1680627 : Nat := 118140960795 + 1680627 * 2 ^ 59
def prefixEnd_1680627 : Nat := 4983230072969 + 3 ^ 40 * 1680627 * 2
def baseEnd_1680627 : Nat := 862969451923901272833443

theorem tailTrace_1680627 : CollatzResearch.WordTrace tailWord_1680627 prefixEnd_1680627 862969451923901272833443 := by
  unfold tailWord_1680627
  simp only [CollatzResearch.WordTrace]
  refine ⟨61297502482382882085224135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40865001654921921390149423 61297502482382882085224135)
  ·
    refine ⟨91946253723574323127836203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61297502482382882085224135 91946253723574323127836203)
    ·
      refine ⟨137919380585361484691754305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91946253723574323127836203 137919380585361484691754305)
      ·
        refine ⟨103439535439021113518815729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137919380585361484691754305 103439535439021113518815729)
        ·
          refine ⟨77579651579265835139111797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103439535439021113518815729 77579651579265835139111797)
          ·
            refine ⟨7273092335556172044291731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77579651579265835139111797 7273092335556172044291731)
            ·
              refine ⟨10909638503334258066437597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7273092335556172044291731 10909638503334258066437597)
              ·
                refine ⟨4091114438750346774914099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10909638503334258066437597 4091114438750346774914099)
                ·
                  refine ⟨6136671658125520162371149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091114438750346774914099 6136671658125520162371149)
                  ·
                    refine ⟨2301251871797070060889181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6136671658125520162371149 2301251871797070060889181)
                    ·
                      refine ⟨862969451923901272833443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2301251871797070060889181 862969451923901272833443)
                      ·
                        rfl

theorem cell23_1680627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 3].length) (baseStart_1680627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680627 prefixEnd_1680627 := by exact prefixLift 1680627
  have htrace : WordTrace (prefixWord ++ tailWord_1680627) baseStart_1680627 baseEnd_1680627 := by
    simpa [prefixWord, tailWord_1680627, baseEnd_1680627] using wordTrace_append hprefix tailTrace_1680627
  have hstable : (prefixWord ++ tailWord_1680627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680627).length < 2 ^ (prefixWord ++ tailWord_1680627).sum := by decide
  have hdescent : baseEnd_1680627 < baseStart_1680627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680640 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_1680640 : Nat := 118140960795 + 1680640 * 2 ^ 59
def prefixEnd_1680640 : Nat := 4983230072969 + 3 ^ 40 * 1680640 * 2
def baseEnd_1680640 : Nat := 862976127172409721970883

theorem tailTrace_1680640 : CollatzResearch.WordTrace tailWord_1680640 prefixEnd_1680640 862976127172409721970883 := by
  unfold tailWord_1680640
  simp only [CollatzResearch.WordTrace]
  refine ⟨30648988315667892652723687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40865317754223856870298249 30648988315667892652723687)
  ·
    refine ⟨45973482473501838979085531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30648988315667892652723687 45973482473501838979085531)
    ·
      refine ⟨68960223710252758468628297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45973482473501838979085531 68960223710252758468628297)
      ·
        refine ⟨51720167782689568851471223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68960223710252758468628297 51720167782689568851471223)
        ·
          refine ⟨77580251674034353277206835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51720167782689568851471223 77580251674034353277206835)
          ·
            refine ⟨116370377511051529915810253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77580251674034353277206835 116370377511051529915810253)
            ·
              refine ⟨43638891566644323718428845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116370377511051529915810253 43638891566644323718428845)
              ·
                refine ⟨16364584337491621394410817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43638891566644323718428845 16364584337491621394410817)
                ·
                  refine ⟨12273438253118716045808113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16364584337491621394410817 12273438253118716045808113)
                  ·
                    refine ⟨9205078689839037034356085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12273438253118716045808113 9205078689839037034356085)
                    ·
                      refine ⟨862976127172409721970883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9205078689839037034356085 862976127172409721970883)
                      ·
                        rfl

theorem cell23_1680640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_1680640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680640 prefixEnd_1680640 := by exact prefixLift 1680640
  have htrace : WordTrace (prefixWord ++ tailWord_1680640) baseStart_1680640 baseEnd_1680640 := by
    simpa [prefixWord, tailWord_1680640, baseEnd_1680640] using wordTrace_append hprefix tailTrace_1680640
  have hstable : (prefixWord ++ tailWord_1680640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680640).length < 2 ^ (prefixWord ++ tailWord_1680640).sum := by decide
  have hdescent : baseEnd_1680640 < baseStart_1680640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680644 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1680644 : Nat := 118140960795 + 1680644 * 2 ^ 59
def prefixEnd_1680644 : Nat := 4983230072969 + 3 ^ 40 * 1680644 * 2
def baseEnd_1680644 : Nat := 862978181095027706320865

theorem tailTrace_1680644 : CollatzResearch.WordTrace tailWord_1680644 prefixEnd_1680644 862978181095027706320865 := by
  unfold tailWord_1680644
  simp only [CollatzResearch.WordTrace]
  refine ⟨30649061261660646994296493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40865415015547529325728657 30649061261660646994296493)
  ·
    refine ⟨11493397973122742622861185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30649061261660646994296493 11493397973122742622861185)
    ·
      refine ⟨8620048479842056967145889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11493397973122742622861185 8620048479842056967145889)
      ·
        refine ⟨6465036359881542725359417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8620048479842056967145889 6465036359881542725359417)
        ·
          refine ⟨4848777269911157044019563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6465036359881542725359417 4848777269911157044019563)
          ·
            refine ⟨7273165904866735566029345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848777269911157044019563 7273165904866735566029345)
            ·
              refine ⟨5454874428650051674522009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7273165904866735566029345 5454874428650051674522009)
              ·
                refine ⟨4091155821487538755891507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454874428650051674522009 4091155821487538755891507)
                ·
                  refine ⟨6136733732231308133837261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091155821487538755891507 6136733732231308133837261)
                  ·
                    refine ⟨2301275149586740550188973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6136733732231308133837261 2301275149586740550188973)
                    ·
                      refine ⟨862978181095027706320865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2301275149586740550188973 862978181095027706320865)
                      ·
                        rfl

theorem cell23_1680644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1680644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680644 prefixEnd_1680644 := by exact prefixLift 1680644
  have htrace : WordTrace (prefixWord ++ tailWord_1680644) baseStart_1680644 baseEnd_1680644 := by
    simpa [prefixWord, tailWord_1680644, baseEnd_1680644] using wordTrace_append hprefix tailTrace_1680644
  have hstable : (prefixWord ++ tailWord_1680644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680644).length < 2 ^ (prefixWord ++ tailWord_1680644).sum := by decide
  have hdescent : baseEnd_1680644 < baseStart_1680644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680648 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 1, 2, 3]
def baseStart_1680648 : Nat := 118140960795 + 1680648 * 2 ^ 59
def prefixEnd_1680648 : Nat := 4983230072969 + 3 ^ 40 * 1680648 * 2
def baseEnd_1680648 : Nat := 862980235017645690670847

theorem tailTrace_1680648 : CollatzResearch.WordTrace tailWord_1680648 prefixEnd_1680648 862980235017645690670847 := by
  unfold tailWord_1680648
  simp only [CollatzResearch.WordTrace]
  refine ⟨30649134207653401335869299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40865512276871201781159065 30649134207653401335869299)
  ·
    refine ⟨45973701311480102003803949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30649134207653401335869299 45973701311480102003803949)
    ·
      refine ⟨17240137991805038251426481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45973701311480102003803949 17240137991805038251426481)
      ·
        refine ⟨12930103493853778688569861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17240137991805038251426481 12930103493853778688569861)
        ·
          refine ⟨2424394405097583504106849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12930103493853778688569861 2424394405097583504106849)
          ·
            refine ⟨1818295803823187628080137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2424394405097583504106849 1818295803823187628080137)
            ·
              refine ⟨1363721852867390721060103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818295803823187628080137 1363721852867390721060103)
              ·
                refine ⟨2045582779301086081590155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363721852867390721060103 2045582779301086081590155)
                ·
                  refine ⟨3068374168951629122385233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045582779301086081590155 3068374168951629122385233)
                  ·
                    refine ⟨2301280626713721841788925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3068374168951629122385233 2301280626713721841788925)
                    ·
                      refine ⟨862980235017645690670847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2301280626713721841788925 862980235017645690670847)
                      ·
                        rfl

theorem cell23_1680648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_1680648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680648 prefixEnd_1680648 := by exact prefixLift 1680648
  have htrace : WordTrace (prefixWord ++ tailWord_1680648) baseStart_1680648 baseEnd_1680648 := by
    simpa [prefixWord, tailWord_1680648, baseEnd_1680648] using wordTrace_append hprefix tailTrace_1680648
  have hstable : (prefixWord ++ tailWord_1680648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680648).length < 2 ^ (prefixWord ++ tailWord_1680648).sum := by decide
  have hdescent : baseEnd_1680648 < baseStart_1680648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680677 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_1680677 : Nat := 118140960795 + 1680677 * 2 ^ 59
def prefixEnd_1680677 : Nat := 4983230072969 + 3 ^ 40 * 1680677 * 2
def baseEnd_1680677 : Nat := 287665041985542025736071

theorem tailTrace_1680677 : CollatzResearch.WordTrace tailWord_1680677 prefixEnd_1680677 287665041985542025736071 := by
  unfold tailWord_1680677
  simp only [CollatzResearch.WordTrace]
  refine ⟨61299326132201740624544285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40866217421467827083029523 61299326132201740624544285)
  ·
    refine ⟨22987247299575652734204107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61299326132201740624544285 22987247299575652734204107)
    ·
      refine ⟨34480870949363479101306161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22987247299575652734204107 34480870949363479101306161)
      ·
        refine ⟨25860653212022609325979621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34480870949363479101306161 25860653212022609325979621)
        ·
          refine ⟨4848872477254239248621179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25860653212022609325979621 4848872477254239248621179)
          ·
            refine ⟨7273308715881358872931769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848872477254239248621179 7273308715881358872931769)
            ·
              refine ⟨5454981536911019154698827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7273308715881358872931769 5454981536911019154698827)
              ·
                refine ⟨8182472305366528732048241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454981536911019154698827 8182472305366528732048241)
                ·
                  refine ⟨6136854229024896549036181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8182472305366528732048241 6136854229024896549036181)
                  ·
                    refine ⟨287665041985542025736071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6136854229024896549036181 287665041985542025736071)
                    ·
                      rfl

theorem cell23_1680677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_1680677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680677 prefixEnd_1680677 := by exact prefixLift 1680677
  have htrace : WordTrace (prefixWord ++ tailWord_1680677) baseStart_1680677 baseEnd_1680677 := by
    simpa [prefixWord, tailWord_1680677, baseEnd_1680677] using wordTrace_append hprefix tailTrace_1680677
  have hstable : (prefixWord ++ tailWord_1680677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680677).length < 2 ^ (prefixWord ++ tailWord_1680677).sum := by decide
  have hdescent : baseEnd_1680677 < baseStart_1680677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680754 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_1680754 : Nat := 118140960795 + 1680754 * 2 ^ 59
def prefixEnd_1680754 : Nat := 4983230072969 + 3 ^ 40 * 1680754 * 2
def baseEnd_1680754 : Nat := 287678221322340758648453

theorem tailTrace_1680754 : CollatzResearch.WordTrace tailWord_1680754 prefixEnd_1680754 287678221322340758648453 := by
  unfold tailWord_1680754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15325533638230695693774329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40868089701948521850064877 15325533638230695693774329)
  ·
    refine ⟨11494150228673021770330747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15325533638230695693774329 11494150228673021770330747)
    ·
      refine ⟨17241225343009532655496121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11494150228673021770330747 17241225343009532655496121)
      ·
        refine ⟨12930919007257149491622091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17241225343009532655496121 12930919007257149491622091)
        ·
          refine ⟨19396378510885724237433137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12930919007257149491622091 19396378510885724237433137)
          ·
            refine ⟨14547283883164293178074853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19396378510885724237433137 14547283883164293178074853)
            ·
              refine ⟨2727615728093304970889035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14547283883164293178074853 2727615728093304970889035)
              ·
                refine ⟨4091423592139957456333553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2727615728093304970889035 4091423592139957456333553)
                ·
                  refine ⟨3068567694104968092250165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4091423592139957456333553 3068567694104968092250165)
                  ·
                    refine ⟨287678221322340758648453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3068567694104968092250165 287678221322340758648453)
                    ·
                      rfl

theorem cell23_1680754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_1680754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680754 prefixEnd_1680754 := by exact prefixLift 1680754
  have htrace : WordTrace (prefixWord ++ tailWord_1680754) baseStart_1680754 baseEnd_1680754 := by
    simpa [prefixWord, tailWord_1680754, baseEnd_1680754] using wordTrace_append hprefix tailTrace_1680754
  have hstable : (prefixWord ++ tailWord_1680754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680754).length < 2 ^ (prefixWord ++ tailWord_1680754).sum := by decide
  have hdescent : baseEnd_1680754 < baseStart_1680754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680794 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1680794 : Nat := 118140960795 + 1680794 * 2 ^ 59
def prefixEnd_1680794 : Nat := 4983230072969 + 3 ^ 40 * 1680794 * 2
def baseEnd_1680794 : Nat := 863055203193202119445175

theorem tailTrace_1680794 : CollatzResearch.WordTrace tailWord_1680794 prefixEnd_1680794 863055203193202119445175 := by
  unfold tailWord_1680794
  simp only [CollatzResearch.WordTrace]
  refine ⟨15325898368194467401638359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40869062315185246404368957 15325898368194467401638359)
  ·
    refine ⟨22988847552291701102457539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15325898368194467401638359 22988847552291701102457539)
    ·
      refine ⟨34483271328437551653686309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22988847552291701102457539 34483271328437551653686309)
      ·
        refine ⟨6465613374082040935066183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34483271328437551653686309 6465613374082040935066183)
        ·
          refine ⟨9698420061123061402599275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465613374082040935066183 9698420061123061402599275)
          ·
            refine ⟨14547630091684592103898913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9698420061123061402599275 14547630091684592103898913)
            ·
              refine ⟨10910722568763444077924185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14547630091684592103898913 10910722568763444077924185)
              ·
                refine ⟨8183041926572583058443139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10910722568763444077924185 8183041926572583058443139)
                ·
                  refine ⟨12274562889858874587664709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8183041926572583058443139 12274562889858874587664709)
                  ·
                    refine ⟨2301480541848538985187133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12274562889858874587664709 2301480541848538985187133)
                    ·
                      refine ⟨863055203193202119445175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2301480541848538985187133 863055203193202119445175)
                      ·
                        rfl

theorem cell23_1680794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1680794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680794 prefixEnd_1680794 := by exact prefixLift 1680794
  have htrace : WordTrace (prefixWord ++ tailWord_1680794) baseStart_1680794 baseEnd_1680794 := by
    simpa [prefixWord, tailWord_1680794, baseEnd_1680794] using wordTrace_append hprefix tailTrace_1680794
  have hstable : (prefixWord ++ tailWord_1680794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680794).length < 2 ^ (prefixWord ++ tailWord_1680794).sum := by decide
  have hdescent : baseEnd_1680794 < baseStart_1680794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680861 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1680861 : Nat := 118140960795 + 1680861 * 2 ^ 59
def prefixEnd_1680861 : Nat := 4983230072969 + 3 ^ 40 * 1680861 * 2
def baseEnd_1680861 : Nat := 287696535465684452435789

theorem tailTrace_1680861 : CollatzResearch.WordTrace tailWord_1680861 prefixEnd_1680861 287696535465684452435789 := by
  unfold tailWord_1680861
  simp only [CollatzResearch.WordTrace]
  refine ⟨61306037163535140049242437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40870691442356760032828291 61306037163535140049242437)
  ·
    refine ⟨11494881968162838759232957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61306037163535140049242437 11494881968162838759232957)
    ·
      refine ⟨4310580738061064534712359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11494881968162838759232957 4310580738061064534712359)
      ·
        refine ⟨6465871107091596802068539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310580738061064534712359 6465871107091596802068539)
        ·
          refine ⟨9698806660637395203102809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465871107091596802068539 9698806660637395203102809)
          ·
            refine ⟨7274104995478046402327107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9698806660637395203102809 7274104995478046402327107)
            ·
              refine ⟨10911157493217069603490661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7274104995478046402327107 10911157493217069603490661)
              ·
                refine ⟨2045842029978200550654499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10911157493217069603490661 2045842029978200550654499)
                ·
                  refine ⟨3068763044967300825981749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045842029978200550654499 3068763044967300825981749)
                  ·
                    refine ⟨287696535465684452435789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3068763044967300825981749 287696535465684452435789)
                    ·
                      rfl

theorem cell23_1680861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1680861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680861 prefixEnd_1680861 := by exact prefixLift 1680861
  have htrace : WordTrace (prefixWord ++ tailWord_1680861) baseStart_1680861 baseEnd_1680861 := by
    simpa [prefixWord, tailWord_1680861, baseEnd_1680861] using wordTrace_append hprefix tailTrace_1680861
  have hstable : (prefixWord ++ tailWord_1680861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680861).length < 2 ^ (prefixWord ++ tailWord_1680861).sum := by decide
  have hdescent : baseEnd_1680861 < baseStart_1680861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680881 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 4]
def baseStart_1680881 : Nat := 118140960795 + 1680881 * 2 ^ 59
def prefixEnd_1680881 : Nat := 4983230072969 + 3 ^ 40 * 1680881 * 2
def baseEnd_1680881 : Nat := 863099876010143279057275

theorem tailTrace_1680881 : CollatzResearch.WordTrace tailWord_1680881 prefixEnd_1680881 863099876010143279057275 := by
  unfold tailWord_1680881
  simp only [CollatzResearch.WordTrace]
  refine ⟨61306766623462683464970497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40871177748975122309980331 61306766623462683464970497)
  ·
    refine ⟨45980074967597012598727873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61306766623462683464970497 45980074967597012598727873)
    ·
      refine ⟨34485056225697759449045905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45980074967597012598727873 34485056225697759449045905)
      ·
        refine ⟨25863792169273319586784429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34485056225697759449045905 25863792169273319586784429)
        ·
          refine ⟨9698922063477494845044161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25863792169273319586784429 9698922063477494845044161)
          ·
            refine ⟨7274191547608121133783121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9698922063477494845044161 7274191547608121133783121)
            ·
              refine ⟨5455643660706090850337341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7274191547608121133783121 5455643660706090850337341)
              ·
                refine ⟨2045866372764784068876503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5455643660706090850337341 2045866372764784068876503)
                ·
                  refine ⟨3068799559147176103314755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045866372764784068876503 3068799559147176103314755)
                  ·
                    refine ⟨4603199338720764154972133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3068799559147176103314755 4603199338720764154972133)
                    ·
                      refine ⟨863099876010143279057275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4603199338720764154972133 863099876010143279057275)
                      ·
                        rfl

theorem cell23_1680881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_1680881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680881 prefixEnd_1680881 := by exact prefixLift 1680881
  have htrace : WordTrace (prefixWord ++ tailWord_1680881) baseStart_1680881 baseEnd_1680881 := by
    simpa [prefixWord, tailWord_1680881, baseEnd_1680881] using wordTrace_append hprefix tailTrace_1680881
  have hstable : (prefixWord ++ tailWord_1680881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680881).length < 2 ^ (prefixWord ++ tailWord_1680881).sum := by decide
  have hdescent : baseEnd_1680881 < baseStart_1680881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680885 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_1680885 : Nat := 118140960795 + 1680885 * 2 ^ 59
def prefixEnd_1680885 : Nat := 4983230072969 + 3 ^ 40 * 1680885 * 2
def baseEnd_1680885 : Nat := 863101929932761263407257

theorem tailTrace_1680885 : CollatzResearch.WordTrace tailWord_1680885 prefixEnd_1680885 863101929932761263407257 := by
  unfold tailWord_1680885
  simp only [CollatzResearch.WordTrace]
  refine ⟨61306912515448192148116109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40871275010298794765410739 61306912515448192148116109)
  ·
    refine ⟨22990092193293072055543541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61306912515448192148116109 22990092193293072055543541)
    ·
      refine ⟨2155321143121225505207207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22990092193293072055543541 2155321143121225505207207)
      ·
        refine ⟨3232981714681838257810811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2155321143121225505207207 3232981714681838257810811)
        ·
          refine ⟨4849472572022757386716217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232981714681838257810811 4849472572022757386716217)
          ·
            refine ⟨3637104429017068040037163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4849472572022757386716217 3637104429017068040037163)
            ·
              refine ⟨5455656643525602060055745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3637104429017068040037163 5455656643525602060055745)
              ·
                refine ⟨4091742482644201545041809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5455656643525602060055745 4091742482644201545041809)
                ·
                  refine ⟨3068806861983151158781357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4091742482644201545041809 3068806861983151158781357)
                  ·
                    refine ⟨1150802573243681684543009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3068806861983151158781357 1150802573243681684543009)
                    ·
                      refine ⟨863101929932761263407257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150802573243681684543009 863101929932761263407257)
                      ·
                        rfl

theorem cell23_1680885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_1680885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680885 prefixEnd_1680885 := by exact prefixLift 1680885
  have htrace : WordTrace (prefixWord ++ tailWord_1680885) baseStart_1680885 baseEnd_1680885 := by
    simpa [prefixWord, tailWord_1680885, baseEnd_1680885] using wordTrace_append hprefix tailTrace_1680885
  have hstable : (prefixWord ++ tailWord_1680885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680885).length < 2 ^ (prefixWord ++ tailWord_1680885).sum := by decide
  have hdescent : baseEnd_1680885 < baseStart_1680885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680908 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_1680908 : Nat := 118140960795 + 1680908 * 2 ^ 59
def prefixEnd_1680908 : Nat := 4983230072969 + 3 ^ 40 * 1680908 * 2
def baseEnd_1680908 : Nat := 287704579995938224473217

theorem tailTrace_1680908 : CollatzResearch.WordTrace tailWord_1680908 prefixEnd_1680908 287704579995938224473217 := by
  unfold tailWord_1680908
  simp only [CollatzResearch.WordTrace]
  refine ⟨30653875697182433538101689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40871834262909911384135585 30653875697182433538101689)
  ·
    refine ⟨22990406772886825153576267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30653875697182433538101689 22990406772886825153576267)
    ·
      refine ⟨34485610159330237730364401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22990406772886825153576267 34485610159330237730364401)
      ·
        refine ⟨25864207619497678297773301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34485610159330237730364401 25864207619497678297773301)
        ·
          refine ⟨2424769464327907340416247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25864207619497678297773301 2424769464327907340416247)
          ·
            refine ⟨3637154196491861010624371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424769464327907340416247 3637154196491861010624371)
            ·
              refine ⟨5455731294737791515936557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3637154196491861010624371 5455731294737791515936557)
              ·
                refine ⟨2045899235526671818476209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5455731294737791515936557 2045899235526671818476209)
                ·
                  refine ⟨1534424426645003863857157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2045899235526671818476209 1534424426645003863857157)
                  ·
                    refine ⟨287704579995938224473217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1534424426645003863857157 287704579995938224473217)
                    ·
                      rfl

theorem cell23_1680908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_1680908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680908 prefixEnd_1680908 := by exact prefixLift 1680908
  have htrace : WordTrace (prefixWord ++ tailWord_1680908) baseStart_1680908 baseEnd_1680908 := by
    simpa [prefixWord, tailWord_1680908, baseEnd_1680908] using wordTrace_append hprefix tailTrace_1680908
  have hstable : (prefixWord ++ tailWord_1680908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680908).length < 2 ^ (prefixWord ++ tailWord_1680908).sum := by decide
  have hdescent : baseEnd_1680908 < baseStart_1680908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680949 : List Nat := [1, 3, 3, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_1680949 : Nat := 118140960795 + 1680949 * 2 ^ 59
def prefixEnd_1680949 : Nat := 4983230072969 + 3 ^ 40 * 1680949 * 2
def baseEnd_1680949 : Nat := 863134792694649013006963

theorem tailTrace_1680949 : CollatzResearch.WordTrace tailWord_1680949 prefixEnd_1680949 863134792694649013006963 := by
  unfold tailWord_1680949
  simp only [CollatzResearch.WordTrace]
  refine ⟨61309246787216331078445901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40872831191477554052297267 61309246787216331078445901)
  ·
    refine ⟨22990967545206124154417213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61309246787216331078445901 22990967545206124154417213)
    ·
      refine ⟨8621612829452296557906455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22990967545206124154417213 8621612829452296557906455)
      ·
        refine ⟨12932419244178444836859683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8621612829452296557906455 12932419244178444836859683)
        ·
          refine ⟨19398628866267667255289525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12932419244178444836859683 19398628866267667255289525)
          ·
            refine ⟨1818621456212593805183393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19398628866267667255289525 1818621456212593805183393)
            ·
              refine ⟨1363966092159445353887545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818621456212593805183393 1363966092159445353887545)
              ·
                refine ⟨1022974569119584015415659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363966092159445353887545 1022974569119584015415659)
                ·
                  refine ⟨1534461853679376023123489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022974569119584015415659 1534461853679376023123489)
                  ·
                    refine ⟨1150846390259532017342617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1534461853679376023123489 1150846390259532017342617)
                    ·
                      refine ⟨863134792694649013006963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150846390259532017342617 863134792694649013006963)
                      ·
                        rfl

theorem cell23_1680949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_1680949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680949 prefixEnd_1680949 := by exact prefixLift 1680949
  have htrace : WordTrace (prefixWord ++ tailWord_1680949) baseStart_1680949 baseEnd_1680949 := by
    simpa [prefixWord, tailWord_1680949, baseEnd_1680949] using wordTrace_append hprefix tailTrace_1680949
  have hstable : (prefixWord ++ tailWord_1680949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680949).length < 2 ^ (prefixWord ++ tailWord_1680949).sum := by decide
  have hdescent : baseEnd_1680949 < baseStart_1680949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680954 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_1680954 : Nat := 118140960795 + 1680954 * 2 ^ 59
def prefixEnd_1680954 : Nat := 4983230072969 + 3 ^ 40 * 1680954 * 2
def baseEnd_1680954 : Nat := 863137360097921493444439

theorem tailTrace_1680954 : CollatzResearch.WordTrace tailWord_1680954 prefixEnd_1680954 863137360097921493444439 := by
  unfold tailWord_1680954
  simp only [CollatzResearch.WordTrace]
  refine ⟨15327357288049554233094479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40872952768132144621585277 15327357288049554233094479)
  ·
    refine ⟨22991035932074331349641719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15327357288049554233094479 22991035932074331349641719)
    ·
      refine ⟨34486553898111497024462579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22991035932074331349641719 34486553898111497024462579)
      ·
        refine ⟨51729830847167245536693869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34486553898111497024462579 51729830847167245536693869)
        ·
          refine ⟨19398686567687717076260201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51729830847167245536693869 19398686567687717076260201)
          ·
            refine ⟨14549014925765787807195151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19398686567687717076260201 14549014925765787807195151)
            ·
              refine ⟨21823522388648681710792727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14549014925765787807195151 21823522388648681710792727)
              ·
                refine ⟨32735283582973022566189091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21823522388648681710792727 32735283582973022566189091)
                ·
                  refine ⟨49102925374459533849283637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32735283582973022566189091 49102925374459533849283637)
                  ·
                    refine ⟨4603399253855581298370341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49102925374459533849283637 4603399253855581298370341)
                    ·
                      refine ⟨863137360097921493444439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4603399253855581298370341 863137360097921493444439)
                      ·
                        rfl

theorem cell23_1680954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_1680954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680954 prefixEnd_1680954 := by exact prefixLift 1680954
  have htrace : WordTrace (prefixWord ++ tailWord_1680954) baseStart_1680954 baseEnd_1680954 := by
    simpa [prefixWord, tailWord_1680954, baseEnd_1680954] using wordTrace_append hprefix tailTrace_1680954
  have hstable : (prefixWord ++ tailWord_1680954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680954).length < 2 ^ (prefixWord ++ tailWord_1680954).sum := by decide
  have hdescent : baseEnd_1680954 < baseStart_1680954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680984 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1680984 : Nat := 118140960795 + 1680984 * 2 ^ 59
def prefixEnd_1680984 : Nat := 4983230072969 + 3 ^ 40 * 1680984 * 2
def baseEnd_1680984 : Nat := 863152764517556376069301

theorem tailTrace_1680984 : CollatzResearch.WordTrace tailWord_1680984 prefixEnd_1680984 863152764517556376069301 := by
  unfold tailWord_1680984
  simp only [CollatzResearch.WordTrace]
  refine ⟨30655261671044766027985003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40873682228059688037313337 30655261671044766027985003)
  ·
    refine ⟨45982892506567149041977505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30655261671044766027985003 45982892506567149041977505)
    ·
      refine ⟨34487169379925361781483129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45982892506567149041977505 34487169379925361781483129)
      ·
        refine ⟨25865377034944021336112347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34487169379925361781483129 25865377034944021336112347)
        ·
          refine ⟨38798065552416032004168521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25865377034944021336112347 38798065552416032004168521)
          ·
            refine ⟨29098549164312024003126391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38798065552416032004168521 29098549164312024003126391)
            ·
              refine ⟨43647823746468036004689587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29098549164312024003126391 43647823746468036004689587)
              ·
                refine ⟨65471735619702054007034381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43647823746468036004689587 65471735619702054007034381)
                ·
                  refine ⟨24551900857388270252637893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65471735619702054007034381 24551900857388270252637893)
                  ·
                    refine ⟨4603481410760300672369605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24551900857388270252637893 4603481410760300672369605)
                    ·
                      refine ⟨863152764517556376069301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4603481410760300672369605 863152764517556376069301)
                      ·
                        rfl

theorem cell23_1680984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1680984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1680984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1680984 prefixEnd_1680984 := by exact prefixLift 1680984
  have htrace : WordTrace (prefixWord ++ tailWord_1680984) baseStart_1680984 baseEnd_1680984 := by
    simpa [prefixWord, tailWord_1680984, baseEnd_1680984] using wordTrace_append hprefix tailTrace_1680984
  have hstable : (prefixWord ++ tailWord_1680984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680984).length < 2 ^ (prefixWord ++ tailWord_1680984).sum := by decide
  have hdescent : baseEnd_1680984 < baseStart_1680984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681024 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 3, 7]
def baseStart_1681024 : Nat := 118140960795 + 1681024 * 2 ^ 59
def prefixEnd_1681024 : Nat := 4983230072969 + 3 ^ 40 * 1681024 * 2
def baseEnd_1681024 : Nat := 287724434581245406523039

theorem tailTrace_1681024 : CollatzResearch.WordTrace tailWord_1681024 prefixEnd_1681024 287724434581245406523039 := by
  unfold tailWord_1681024
  simp only [CollatzResearch.WordTrace]
  refine ⟨30655991130972309443713063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40874654841296412591617417 30655991130972309443713063)
  ·
    refine ⟨45983986696458464165569595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30655991130972309443713063 45983986696458464165569595)
    ·
      refine ⟨68975980044687696248354393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45983986696458464165569595 68975980044687696248354393)
      ·
        refine ⟨51731985033515772186265795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68975980044687696248354393 51731985033515772186265795)
        ·
          refine ⟨77597977550273658279398693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51731985033515772186265795 77597977550273658279398693)
          ·
            refine ⟨14549620790676310927387255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77597977550273658279398693 14549620790676310927387255)
            ·
              refine ⟨21824431186014466391080883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14549620790676310927387255 21824431186014466391080883)
              ·
                refine ⟨32736646779021699586621325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21824431186014466391080883 32736646779021699586621325)
                ·
                  refine ⟨12276242542133137344982997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32736646779021699586621325 12276242542133137344982997)
                  ·
                    refine ⟨287724434581245406523039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12276242542133137344982997 287724434581245406523039)
                    ·
                      rfl

theorem cell23_1681024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_1681024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681024 prefixEnd_1681024 := by exact prefixLift 1681024
  have htrace : WordTrace (prefixWord ++ tailWord_1681024) baseStart_1681024 baseEnd_1681024 := by
    simpa [prefixWord, tailWord_1681024, baseEnd_1681024] using wordTrace_append hprefix tailTrace_1681024
  have hstable : (prefixWord ++ tailWord_1681024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681024).length < 2 ^ (prefixWord ++ tailWord_1681024).sum := by decide
  have hdescent : baseEnd_1681024 < baseStart_1681024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681061 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_1681061 : Nat := 118140960795 + 1681061 * 2 ^ 59
def prefixEnd_1681061 : Nat := 4983230072969 + 3 ^ 40 * 1681061 * 2
def baseEnd_1681061 : Nat := 863192302527952574806447

theorem tailTrace_1681061 : CollatzResearch.WordTrace tailWord_1681061 prefixEnd_1681061 863192302527952574806447 := by
  unfold tailWord_1681061
  simp only [CollatzResearch.WordTrace]
  refine ⟨61313331762810574206523037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40875554508540382804348691 61313331762810574206523037)
  ·
    refine ⟨22992499411053965327446139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61313331762810574206523037 22992499411053965327446139)
    ·
      refine ⟨34488749116580947991169209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22992499411053965327446139 34488749116580947991169209)
      ·
        refine ⟨25866561837435710993376907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34488749116580947991169209 25866561837435710993376907)
        ·
          refine ⟨38799842756153566490065361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25866561837435710993376907 38799842756153566490065361)
          ·
            refine ⟨29099882067115174867549021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38799842756153566490065361 29099882067115174867549021)
            ·
              refine ⟨10912455775168190575330883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29099882067115174867549021 10912455775168190575330883)
              ·
                refine ⟨16368683662752285862996325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10912455775168190575330883 16368683662752285862996325)
                ·
                  refine ⟨3069128186766053599311811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16368683662752285862996325 3069128186766053599311811)
                  ·
                    refine ⟨4603692280149080398967717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3069128186766053599311811 4603692280149080398967717)
                    ·
                      refine ⟨863192302527952574806447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4603692280149080398967717 863192302527952574806447)
                      ·
                        rfl

theorem cell23_1681061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_1681061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681061 prefixEnd_1681061 := by exact prefixLift 1681061
  have htrace : WordTrace (prefixWord ++ tailWord_1681061) baseStart_1681061 baseEnd_1681061 := by
    simpa [prefixWord, tailWord_1681061, baseEnd_1681061] using wordTrace_append hprefix tailTrace_1681061
  have hstable : (prefixWord ++ tailWord_1681061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681061).length < 2 ^ (prefixWord ++ tailWord_1681061).sum := by decide
  have hdescent : baseEnd_1681061 < baseStart_1681061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681081 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1681081 : Nat := 118140960795 + 1681081 * 2 ^ 59
def prefixEnd_1681081 : Nat := 4983230072969 + 3 ^ 40 * 1681081 * 2
def baseEnd_1681081 : Nat := 863202572141042496556355

theorem tailTrace_1681081 : CollatzResearch.WordTrace tailWord_1681081 prefixEnd_1681081 863202572141042496556355 := by
  unfold tailWord_1681081
  simp only [CollatzResearch.WordTrace]
  refine ⟨61314061222738117622251097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40876040815158745081500731 61314061222738117622251097)
  ·
    refine ⟨45985545917053588216688323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61314061222738117622251097 45985545917053588216688323)
    ·
      refine ⟨68978318875580382325032485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45985545917053588216688323 68978318875580382325032485)
      ·
        refine ⟨12933434789171321685943591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68978318875580382325032485 12933434789171321685943591)
        ·
          refine ⟨19400152183756982528915387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12933434789171321685943591 19400152183756982528915387)
          ·
            refine ⟨29100228275635473793373081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19400152183756982528915387 29100228275635473793373081)
            ·
              refine ⟨21825171206726605345029811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29100228275635473793373081 21825171206726605345029811)
              ·
                refine ⟨32737756810089908017544717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21825171206726605345029811 32737756810089908017544717)
                ·
                  refine ⟨12276658803783715506579269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32737756810089908017544717 12276658803783715506579269)
                  ·
                    refine ⟨2301873525709446657483613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12276658803783715506579269 2301873525709446657483613)
                    ·
                      refine ⟨863202572141042496556355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2301873525709446657483613 863202572141042496556355)
                      ·
                        rfl

theorem cell23_1681081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1681081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681081 prefixEnd_1681081 := by exact prefixLift 1681081
  have htrace : WordTrace (prefixWord ++ tailWord_1681081) baseStart_1681081 baseEnd_1681081 := by
    simpa [prefixWord, tailWord_1681081, baseEnd_1681081] using wordTrace_append hprefix tailTrace_1681081
  have hstable : (prefixWord ++ tailWord_1681081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681081).length < 2 ^ (prefixWord ++ tailWord_1681081).sum := by decide
  have hdescent : baseEnd_1681081 < baseStart_1681081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681131 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 3, 5]
def baseStart_1681131 : Nat := 118140960795 + 1681131 * 2 ^ 59
def prefixEnd_1681131 : Nat := 4983230072969 + 3 ^ 40 * 1681131 * 2
def baseEnd_1681131 : Nat := 287742748724589100310375

theorem tailTrace_1681131 : CollatzResearch.WordTrace tailWord_1681131 prefixEnd_1681131 287742748724589100310375 := by
  unfold tailWord_1681131
  simp only [CollatzResearch.WordTrace]
  refine ⟨61315884872556976161571247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40877256581704650774380831 61315884872556976161571247)
  ·
    refine ⟨91973827308835464242356871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61315884872556976161571247 91973827308835464242356871)
    ·
      refine ⟨137960740963253196363535307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91973827308835464242356871 137960740963253196363535307)
      ·
        refine ⟨206941111444879794545302961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137960740963253196363535307 206941111444879794545302961)
        ·
          refine ⟨155205833583659845908977221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206941111444879794545302961 155205833583659845908977221)
          ·
            refine ⟨29101093796936221107933229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155205833583659845908977221 29101093796936221107933229)
            ·
              refine ⟨10912910173851082915474961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29101093796936221107933229 10912910173851082915474961)
              ·
                refine ⟨8184682630388312186606221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10912910173851082915474961 8184682630388312186606221)
                ·
                  refine ⟨3069255986395617069977333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8184682630388312186606221 3069255986395617069977333)
                  ·
                    refine ⟨287742748724589100310375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3069255986395617069977333 287742748724589100310375)
                    ·
                      rfl

theorem cell23_1681131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 5].length) (baseStart_1681131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681131 prefixEnd_1681131 := by exact prefixLift 1681131
  have htrace : WordTrace (prefixWord ++ tailWord_1681131) baseStart_1681131 baseEnd_1681131 := by
    simpa [prefixWord, tailWord_1681131, baseEnd_1681131] using wordTrace_append hprefix tailTrace_1681131
  have hstable : (prefixWord ++ tailWord_1681131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681131).length < 2 ^ (prefixWord ++ tailWord_1681131).sum := by decide
  have hdescent : baseEnd_1681131 < baseStart_1681131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681148 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_1681148 : Nat := 118140960795 + 1681148 * 2 ^ 59
def prefixEnd_1681148 : Nat := 4983230072969 + 3 ^ 40 * 1681148 * 2
def baseEnd_1681148 : Nat := 287745658448297911472849

theorem tailTrace_1681148 : CollatzResearch.WordTrace tailWord_1681148 prefixEnd_1681148 287745658448297911472849 := by
  unfold tailWord_1681148
  simp only [CollatzResearch.WordTrace]
  refine ⟨30658252456747694032470049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40877669942330258709960065 30658252456747694032470049)
  ·
    refine ⟨22993689342560770524352537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30658252456747694032470049 22993689342560770524352537)
    ·
      refine ⟨17245267006920577893264403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22993689342560770524352537 17245267006920577893264403)
      ·
        refine ⟨25867900510380866839896605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17245267006920577893264403 25867900510380866839896605)
        ·
          refine ⟨9700462691392825064961227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25867900510380866839896605 9700462691392825064961227)
          ·
            refine ⟨14550694037089237597441841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9700462691392825064961227 14550694037089237597441841)
            ·
              refine ⟨10913020527816928198081381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14550694037089237597441841 10913020527816928198081381)
              ·
                refine ⟨2046191348965674037140259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10913020527816928198081381 2046191348965674037140259)
                ·
                  refine ⟨3069287023448511055710389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046191348965674037140259 3069287023448511055710389)
                  ·
                    refine ⟨287745658448297911472849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3069287023448511055710389 287745658448297911472849)
                    ·
                      rfl

theorem cell23_1681148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_1681148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681148 prefixEnd_1681148 := by exact prefixLift 1681148
  have htrace : WordTrace (prefixWord ++ tailWord_1681148) baseStart_1681148 baseEnd_1681148 := by
    simpa [prefixWord, tailWord_1681148, baseEnd_1681148] using wordTrace_append hprefix tailTrace_1681148
  have hstable : (prefixWord ++ tailWord_1681148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681148).length < 2 ^ (prefixWord ++ tailWord_1681148).sum := by decide
  have hdescent : baseEnd_1681148 < baseStart_1681148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681155 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 2, 3, 2]
def baseStart_1681155 : Nat := 118140960795 + 1681155 * 2 ^ 59
def prefixEnd_1681155 : Nat := 4983230072969 + 3 ^ 40 * 1681155 * 2
def baseEnd_1681155 : Nat := 863240569709475207031015

theorem tailTrace_1681155 : CollatzResearch.WordTrace tailWord_1681155 prefixEnd_1681155 863240569709475207031015 := by
  unfold tailWord_1681155
  simp only [CollatzResearch.WordTrace]
  refine ⟨61316760224470028260444919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40877840149646685506963279 61316760224470028260444919)
  ·
    refine ⟨91975140336705042390667379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61316760224470028260444919 91975140336705042390667379)
    ·
      refine ⟨137962710505057563586001069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91975140336705042390667379 137962710505057563586001069)
      ·
        refine ⟨51736016439396586344750401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137962710505057563586001069 51736016439396586344750401)
        ·
          refine ⟨38802012329547439758562801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51736016439396586344750401 38802012329547439758562801)
          ·
            refine ⟨29101509247160579818922101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38802012329547439758562801 29101509247160579818922101)
            ·
              refine ⟨2728266491921304358023947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29101509247160579818922101 2728266491921304358023947)
              ·
                refine ⟨4092399737881956537035921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728266491921304358023947 4092399737881956537035921)
                ·
                  refine ⟨3069299803411467402776941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4092399737881956537035921 3069299803411467402776941)
                  ·
                    refine ⟨1150987426279300276041353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3069299803411467402776941 1150987426279300276041353)
                    ·
                      refine ⟨863240569709475207031015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1150987426279300276041353 863240569709475207031015)
                      ·
                        rfl

theorem cell23_1681155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_1681155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681155 prefixEnd_1681155 := by exact prefixLift 1681155
  have htrace : WordTrace (prefixWord ++ tailWord_1681155) baseStart_1681155 baseEnd_1681155 := by
    simpa [prefixWord, tailWord_1681155, baseEnd_1681155] using wordTrace_append hprefix tailTrace_1681155
  have hstable : (prefixWord ++ tailWord_1681155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681155).length < 2 ^ (prefixWord ++ tailWord_1681155).sum := by decide
  have hdescent : baseEnd_1681155 < baseStart_1681155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681162 : List Nat := [3, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3]
def baseStart_1681162 : Nat := 118140960795 + 1681162 * 2 ^ 59
def prefixEnd_1681162 : Nat := 4983230072969 + 3 ^ 40 * 1681162 * 2
def baseEnd_1681162 : Nat := 863244164074056679643483

theorem tailTrace_1681162 : CollatzResearch.WordTrace tailWord_1681162 prefixEnd_1681162 863244164074056679643483 := by
  unfold tailWord_1681162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15329253883861167113987435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40878010356963112303966493 15329253883861167113987435)
  ·
    refine ⟨22993880825791750670981153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15329253883861167113987435 22993880825791750670981153)
    ·
      refine ⟨17245410619343813003235865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22993880825791750670981153 17245410619343813003235865)
      ·
        refine ⟨12934057964507859752426899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17245410619343813003235865 12934057964507859752426899)
        ·
          refine ⟨19401086946761789628640349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12934057964507859752426899 19401086946761789628640349)
          ·
            refine ⟨7275407605035671110740131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19401086946761789628640349 7275407605035671110740131)
            ·
              refine ⟨10913111407553506666110197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275407605035671110740131 10913111407553506666110197)
              ·
                refine ⟨1023104194458141249947831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10913111407553506666110197 1023104194458141249947831)
                ·
                  refine ⟨1534656291687211874921747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023104194458141249947831 1534656291687211874921747)
                  ·
                    refine ⟨2301984437530817812382621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1534656291687211874921747 2301984437530817812382621)
                    ·
                      refine ⟨863244164074056679643483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2301984437530817812382621 863244164074056679643483)
                      ·
                        rfl

theorem cell23_1681162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_1681162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681162 prefixEnd_1681162 := by exact prefixLift 1681162
  have htrace : WordTrace (prefixWord ++ tailWord_1681162) baseStart_1681162 baseEnd_1681162 := by
    simpa [prefixWord, tailWord_1681162, baseEnd_1681162] using wordTrace_append hprefix tailTrace_1681162
  have hstable : (prefixWord ++ tailWord_1681162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681162).length < 2 ^ (prefixWord ++ tailWord_1681162).sum := by decide
  have hdescent : baseEnd_1681162 < baseStart_1681162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681188 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1681188 : Nat := 118140960795 + 1681188 * 2 ^ 59
def prefixEnd_1681188 : Nat := 4983230072969 + 3 ^ 40 * 1681188 * 2
def baseEnd_1681188 : Nat := 863257514571073577918363

theorem tailTrace_1681188 : CollatzResearch.WordTrace tailWord_1681188 prefixEnd_1681188 863257514571073577918363 := by
  unfold tailWord_1681188
  simp only [CollatzResearch.WordTrace]
  refine ⟨30658981916675237448198109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40878642555566983264264145 30658981916675237448198109)
  ·
    refine ⟨11497118218753214043074291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30658981916675237448198109 11497118218753214043074291)
    ·
      refine ⟨17245677328129821064611437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11497118218753214043074291 17245677328129821064611437)
      ·
        refine ⟨6467128998048682899229289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17245677328129821064611437 6467128998048682899229289)
        ·
          refine ⟨4850346748536512174421967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6467128998048682899229289 4850346748536512174421967)
          ·
            refine ⟨7275520122804768261632951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4850346748536512174421967 7275520122804768261632951)
            ·
              refine ⟨10913280184207152392449427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275520122804768261632951 10913280184207152392449427)
              ·
                refine ⟨16369920276310728588674141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10913280184207152392449427 16369920276310728588674141)
                ·
                  refine ⟨6138720103616523220752803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16369920276310728588674141 6138720103616523220752803)
                  ·
                    refine ⟨9208080155424784831129205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6138720103616523220752803 9208080155424784831129205)
                    ·
                      refine ⟨863257514571073577918363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9208080155424784831129205 863257514571073577918363)
                      ·
                        rfl

theorem cell23_1681188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1681188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681188 prefixEnd_1681188 := by exact prefixLift 1681188
  have htrace : WordTrace (prefixWord ++ tailWord_1681188) baseStart_1681188 baseEnd_1681188 := by
    simpa [prefixWord, tailWord_1681188, baseEnd_1681188] using wordTrace_append hprefix tailTrace_1681188
  have hstable : (prefixWord ++ tailWord_1681188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681188).length < 2 ^ (prefixWord ++ tailWord_1681188).sum := by decide
  have hdescent : baseEnd_1681188 < baseStart_1681188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681202 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2]
def baseStart_1681202 : Nat := 118140960795 + 1681202 * 2 ^ 59
def prefixEnd_1681202 : Nat := 4983230072969 + 3 ^ 40 * 1681202 * 2
def baseEnd_1681202 : Nat := 863264703300236523143299

theorem tailTrace_1681202 : CollatzResearch.WordTrace tailWord_1681202 prefixEnd_1681202 863264703300236523143299 := by
  unfold tailWord_1681202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15329618613824938821851465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40878982970199836858270573 15329618613824938821851465)
  ·
    refine ⟨11497213960368704116388599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15329618613824938821851465 11497213960368704116388599)
    ·
      refine ⟨17245820940553056174582899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11497213960368704116388599 17245820940553056174582899)
      ·
        refine ⟨25868731410829584261874349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17245820940553056174582899 25868731410829584261874349)
        ·
          refine ⟨9700774279061094098202881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25868731410829584261874349 9700774279061094098202881)
          ·
            refine ⟨7275580709295820573652161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9700774279061094098202881 7275580709295820573652161)
            ·
              refine ⟨5456685531971865430239121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7275580709295820573652161 5456685531971865430239121)
              ·
                refine ⟨4092514148978899072679341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5456685531971865430239121 4092514148978899072679341)
                ·
                  refine ⟨1534692805867087152254753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4092514148978899072679341 1534692805867087152254753)
                  ·
                    refine ⟨1151019604400315364191065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1534692805867087152254753 1151019604400315364191065)
                    ·
                      refine ⟨863264703300236523143299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1151019604400315364191065 863264703300236523143299)
                      ·
                        rfl

theorem cell23_1681202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_1681202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681202 prefixEnd_1681202 := by exact prefixLift 1681202
  have htrace : WordTrace (prefixWord ++ tailWord_1681202) baseStart_1681202 baseEnd_1681202 := by
    simpa [prefixWord, tailWord_1681202, baseEnd_1681202] using wordTrace_append hprefix tailTrace_1681202
  have hstable : (prefixWord ++ tailWord_1681202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681202).length < 2 ^ (prefixWord ++ tailWord_1681202).sum := by decide
  have hdescent : baseEnd_1681202 < baseStart_1681202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681208 : List Nat := [2, 1, 2, 1, 3, 3, 4, 7]
def baseStart_1681208 : Nat := 118140960795 + 1681208 * 2 ^ 59
def prefixEnd_1681208 : Nat := 4983230072969 + 3 ^ 40 * 1681208 * 2
def baseEnd_1681208 : Nat := 31972880895709759246973

theorem tailTrace_1681208 : CollatzResearch.WordTrace tailWord_1681208 prefixEnd_1681208 31972880895709759246973 := by
  unfold tailWord_1681208
  simp only [CollatzResearch.WordTrace]
  refine ⟨30659346646639009156062139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40879128862185345541416185 30659346646639009156062139)
  ·
    refine ⟨45989019969958513734093209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30659346646639009156062139 45989019969958513734093209)
    ·
      refine ⟨34491764977468885300569907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45989019969958513734093209 34491764977468885300569907)
      ·
        refine ⟨51737647466203327950854861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34491764977468885300569907 51737647466203327950854861)
        ·
          refine ⟨19401617799826247981570573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51737647466203327950854861 19401617799826247981570573)
          ·
            refine ⟨7275606674934842993088965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19401617799826247981570573 7275606674934842993088965)
            ·
              refine ⟨1364176251550283061204181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7275606674934842993088965 1364176251550283061204181)
              ·
                refine ⟨31972880895709759246973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1364176251550283061204181 31972880895709759246973)
                ·
                  rfl

theorem cell23_1681208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 7].length) (baseStart_1681208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681208 prefixEnd_1681208 := by exact prefixLift 1681208
  have htrace : WordTrace (prefixWord ++ tailWord_1681208) baseStart_1681208 baseEnd_1681208 := by
    simpa [prefixWord, tailWord_1681208, baseEnd_1681208] using wordTrace_append hprefix tailTrace_1681208
  have hstable : (prefixWord ++ tailWord_1681208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681208).length < 2 ^ (prefixWord ++ tailWord_1681208).sum := by decide
  have hdescent : baseEnd_1681208 < baseStart_1681208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681219 : List Nat := [1, 1, 1, 3, 1, 5, 3, 3, 1, 2, 2]
def baseStart_1681219 : Nat := 118140960795 + 1681219 * 2 ^ 59
def prefixEnd_1681219 : Nat := 4983230072969 + 3 ^ 40 * 1681219 * 2
def baseEnd_1681219 : Nat := 863273432471362956630721

theorem tailTrace_1681219 : CollatzResearch.WordTrace tailWord_1681219 prefixEnd_1681219 863273432471362956630721 := by
  unfold tailWord_1681219
  simp only [CollatzResearch.WordTrace]
  refine ⟨61319094496238167190774711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40879396330825444793849807 61319094496238167190774711)
  ·
    refine ⟨91978641744357250786162067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61319094496238167190774711 91978641744357250786162067)
    ·
      refine ⟨137967962616535876179243101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91978641744357250786162067 137967962616535876179243101)
      ·
        refine ⟨51737985981200953567216163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137967962616535876179243101 51737985981200953567216163)
        ·
          refine ⟨77606978971801430350824245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51737985981200953567216163 77606978971801430350824245)
          ·
            refine ⟨7275654278606384095389773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77606978971801430350824245 7275654278606384095389773)
            ·
              refine ⟨2728370354477394035771165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7275654278606384095389773 2728370354477394035771165)
              ·
                refine ⟨1023138882929022763414187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2728370354477394035771165 1023138882929022763414187)
                ·
                  refine ⟨1534708324393534145121281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023138882929022763414187 1534708324393534145121281)
                  ·
                    refine ⟨1151031243295150608840961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1534708324393534145121281 1151031243295150608840961)
                    ·
                      refine ⟨863273432471362956630721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1151031243295150608840961 863273432471362956630721)
                      ·
                        rfl

theorem cell23_1681219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 1, 2, 2].length) (baseStart_1681219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681219 prefixEnd_1681219 := by exact prefixLift 1681219
  have htrace : WordTrace (prefixWord ++ tailWord_1681219) baseStart_1681219 baseEnd_1681219 := by
    simpa [prefixWord, tailWord_1681219, baseEnd_1681219] using wordTrace_append hprefix tailTrace_1681219
  have hstable : (prefixWord ++ tailWord_1681219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681219).length < 2 ^ (prefixWord ++ tailWord_1681219).sum := by decide
  have hdescent : baseEnd_1681219 < baseStart_1681219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681222 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1681222 : Nat := 118140960795 + 1681222 * 2 ^ 59
def prefixEnd_1681222 : Nat := 4983230072969 + 3 ^ 40 * 1681222 * 2
def baseEnd_1681222 : Nat := 863274972913326444893207

theorem tailTrace_1681222 : CollatzResearch.WordTrace tailWord_1681222 prefixEnd_1681222 863274972913326444893207 := by
  unfold tailWord_1681222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916225122350853084472935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40879469276818199135422613 1916225122350853084472935)
  ·
    refine ⟨2874337683526279626709403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1916225122350853084472935 2874337683526279626709403)
    ·
      refine ⟨4311506525289419440064105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874337683526279626709403 4311506525289419440064105)
      ·
        refine ⟨3233629893967064580048079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4311506525289419440064105 3233629893967064580048079)
        ·
          refine ⟨4850444840950596870072119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3233629893967064580048079 4850444840950596870072119)
          ·
            refine ⟨7275667261425895305108179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4850444840950596870072119 7275667261425895305108179)
            ·
              refine ⟨10913500892138842957662269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275667261425895305108179 10913500892138842957662269)
              ·
                refine ⟨4092562834552066109123351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10913500892138842957662269 4092562834552066109123351)
                ·
                  refine ⟨6138844251828099163685027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092562834552066109123351 6138844251828099163685027)
                  ·
                    refine ⟨9208266377742148745527541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6138844251828099163685027 9208266377742148745527541)
                    ·
                      refine ⟨863274972913326444893207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9208266377742148745527541 863274972913326444893207)
                      ·
                        rfl

theorem cell23_1681222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1681222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681222 prefixEnd_1681222 := by exact prefixLift 1681222
  have htrace : WordTrace (prefixWord ++ tailWord_1681222) baseStart_1681222 baseEnd_1681222 := by
    simpa [prefixWord, tailWord_1681222, baseEnd_1681222] using wordTrace_append hprefix tailTrace_1681222
  have hstable : (prefixWord ++ tailWord_1681222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681222).length < 2 ^ (prefixWord ++ tailWord_1681222).sum := by decide
  have hdescent : baseEnd_1681222 < baseStart_1681222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681309 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_1681309 : Nat := 118140960795 + 1681309 * 2 ^ 59
def prefixEnd_1681309 : Nat := 4983230072969 + 3 ^ 40 * 1681309 * 2
def baseEnd_1681309 : Nat := 863319645730267604505307

theorem tailTrace_1681309 : CollatzResearch.WordTrace tailWord_1681309 prefixEnd_1681309 863319645730267604505307 := by
  unfold tailWord_1681309
  simp only [CollatzResearch.WordTrace]
  refine ⟨61322377065912112561550981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40881584710608075041033987 61322377065912112561550981)
  ·
    refine ⟨11497945699858521105290809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61322377065912112561550981 11497945699858521105290809)
    ·
      refine ⟨8623459274893890828968107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11497945699858521105290809 8623459274893890828968107)
      ·
        refine ⟨12935188912340836243452161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8623459274893890828968107 12935188912340836243452161)
        ·
          refine ⟨9701391684255627182589121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12935188912340836243452161 9701391684255627182589121)
          ·
            refine ⟨7276043763191720386941841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9701391684255627182589121 7276043763191720386941841)
            ·
              refine ⟨5457032822393790290206381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7276043763191720386941841 5457032822393790290206381)
              ·
                refine ⟨2046387308397671358827393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5457032822393790290206381 2046387308397671358827393)
                ·
                  refine ⟨1534790481298253519120545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2046387308397671358827393 1534790481298253519120545)
                  ·
                    refine ⟨1151092860973690139340409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1534790481298253519120545 1151092860973690139340409)
                    ·
                      refine ⟨863319645730267604505307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1151092860973690139340409 863319645730267604505307)
                      ·
                        rfl

theorem cell23_1681309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_1681309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681309 prefixEnd_1681309 := by exact prefixLift 1681309
  have htrace : WordTrace (prefixWord ++ tailWord_1681309) baseStart_1681309 baseEnd_1681309 := by
    simpa [prefixWord, tailWord_1681309, baseEnd_1681309] using wordTrace_append hprefix tailTrace_1681309
  have hstable : (prefixWord ++ tailWord_1681309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681309).length < 2 ^ (prefixWord ++ tailWord_1681309).sum := by decide
  have hdescent : baseEnd_1681309 < baseStart_1681309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681338 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_1681338 : Nat := 118140960795 + 1681338 * 2 ^ 59
def prefixEnd_1681338 : Nat := 4983230072969 + 3 ^ 40 * 1681338 * 2
def baseEnd_1681338 : Nat := 863334536669247991042673

theorem tailTrace_1681338 : CollatzResearch.WordTrace tailWord_1681338 prefixEnd_1681338 863334536669247991042673 := by
  unfold tailWord_1681338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15330858695701762628589167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40882289855204700342904445 15330858695701762628589167)
  ·
    refine ⟨22996288043552643942883751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15330858695701762628589167 22996288043552643942883751)
    ·
      refine ⟨34494432065328965914325627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22996288043552643942883751 34494432065328965914325627)
      ·
        refine ⟨51741648097993448871488441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34494432065328965914325627 51741648097993448871488441)
        ·
          refine ⟨38806236073495086653616331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51741648097993448871488441 38806236073495086653616331)
          ·
            refine ⟨58209354110242629980424497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38806236073495086653616331 58209354110242629980424497)
            ·
              refine ⟨43657015582681972485318373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58209354110242629980424497 43657015582681972485318373)
              ·
                refine ⟨8185690421752869840997195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43657015582681972485318373 8185690421752869840997195)
                ·
                  refine ⟨12278535632629304761495793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8185690421752869840997195 12278535632629304761495793)
                  ·
                    refine ⟨9208901724471978571121845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12278535632629304761495793 9208901724471978571121845)
                    ·
                      refine ⟨863334536669247991042673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9208901724471978571121845 863334536669247991042673)
                      ·
                        rfl

theorem cell23_1681338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_1681338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681338 prefixEnd_1681338 := by exact prefixLift 1681338
  have htrace : WordTrace (prefixWord ++ tailWord_1681338) baseStart_1681338 baseEnd_1681338 := by
    simpa [prefixWord, tailWord_1681338, baseEnd_1681338] using wordTrace_append hprefix tailTrace_1681338
  have hstable : (prefixWord ++ tailWord_1681338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681338).length < 2 ^ (prefixWord ++ tailWord_1681338).sum := by decide
  have hdescent : baseEnd_1681338 < baseStart_1681338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681365 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1681365 : Nat := 118140960795 + 1681365 * 2 ^ 59
def prefixEnd_1681365 : Nat := 4983230072969 + 3 ^ 40 * 1681365 * 2
def baseEnd_1681365 : Nat := 863348400646919385405049

theorem tailTrace_1681365 : CollatzResearch.WordTrace tailWord_1681365 prefixEnd_1681365 863348400646919385405049 := by
  unfold tailWord_1681365
  simp only [CollatzResearch.WordTrace]
  refine ⟨61324419553709234125589549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40882946369139489417059699 61324419553709234125589549)
  ·
    refine ⟨22996657332640962797096081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61324419553709234125589549 22996657332640962797096081)
    ·
      refine ⟨17247492999480722097822061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22996657332640962797096081 17247492999480722097822061)
      ·
        refine ⟨6467809874805270786683273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17247492999480722097822061 6467809874805270786683273)
        ·
          refine ⟨4850857406103953090012455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6467809874805270786683273 4850857406103953090012455)
          ·
            refine ⟨7276286109155929635018683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4850857406103953090012455 7276286109155929635018683)
            ·
              refine ⟨10914429163733894452528025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7276286109155929635018683 10914429163733894452528025)
              ·
                refine ⟨8185821872800420839396019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10914429163733894452528025 8185821872800420839396019)
                ·
                  refine ⟨12278732809200631259094029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8185821872800420839396019 12278732809200631259094029)
                  ·
                    refine ⟨4604524803450236722160261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12278732809200631259094029 4604524803450236722160261)
                    ·
                      refine ⟨863348400646919385405049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4604524803450236722160261 863348400646919385405049)
                      ·
                        rfl

theorem cell23_1681365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1681365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681365 prefixEnd_1681365 := by exact prefixLift 1681365
  have htrace : WordTrace (prefixWord ++ tailWord_1681365) baseStart_1681365 baseEnd_1681365 := by
    simpa [prefixWord, tailWord_1681365, baseEnd_1681365] using wordTrace_append hprefix tailTrace_1681365
  have hstable : (prefixWord ++ tailWord_1681365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681365).length < 2 ^ (prefixWord ++ tailWord_1681365).sum := by decide
  have hdescent : baseEnd_1681365 < baseStart_1681365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681408 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_1681408 : Nat := 118140960795 + 1681408 * 2 ^ 59
def prefixEnd_1681408 : Nat := 4983230072969 + 3 ^ 40 * 1681408 * 2
def baseEnd_1681408 : Nat := 863370480315062717167351

theorem tailTrace_1681408 : CollatzResearch.WordTrace tailWord_1681408 prefixEnd_1681408 863370480315062717167351 := by
  unfold tailWord_1681408
  simp only [CollatzResearch.WordTrace]
  refine ⟨30662993946276726234702439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40883991928368968312936585 30662993946276726234702439)
  ·
    refine ⟨45994490919415089352053659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30662993946276726234702439 45994490919415089352053659)
    ·
      refine ⟨68991736379122634028080489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45994490919415089352053659 68991736379122634028080489)
      ·
        refine ⟨51743802284341975521060367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68991736379122634028080489 51743802284341975521060367)
        ·
          refine ⟨77615703426512963281590551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51743802284341975521060367 77615703426512963281590551)
          ·
            refine ⟨116423555139769444922385827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77615703426512963281590551 116423555139769444922385827)
            ·
              refine ⟨174635332709654167383578741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116423555139769444922385827 174635332709654167383578741)
              ·
                refine ⟨16372062441530078192210507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174635332709654167383578741 16372062441530078192210507)
                ·
                  refine ⟨24558093662295117288315761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16372062441530078192210507 24558093662295117288315761)
                  ·
                    refine ⟨18418570246721337966236821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24558093662295117288315761 18418570246721337966236821)
                    ·
                      refine ⟨863370480315062717167351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18418570246721337966236821 863370480315062717167351)
                      ·
                        rfl

theorem cell23_1681408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_1681408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681408 prefixEnd_1681408 := by exact prefixLift 1681408
  have htrace : WordTrace (prefixWord ++ tailWord_1681408) baseStart_1681408 baseEnd_1681408 := by
    simpa [prefixWord, tailWord_1681408, baseEnd_1681408] using wordTrace_append hprefix tailTrace_1681408
  have hstable : (prefixWord ++ tailWord_1681408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681408).length < 2 ^ (prefixWord ++ tailWord_1681408).sum := by decide
  have hdescent : baseEnd_1681408 < baseStart_1681408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681432 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1681432 : Nat := 118140960795 + 1681432 * 2 ^ 59
def prefixEnd_1681432 : Nat := 4983230072969 + 3 ^ 40 * 1681432 * 2
def baseEnd_1681432 : Nat := 863382803850770623267241

theorem tailTrace_1681432 : CollatzResearch.WordTrace tailWord_1681432 prefixEnd_1681432 863382803850770623267241 := by
  unfold tailWord_1681432
  simp only [CollatzResearch.WordTrace]
  refine ⟨30663431622233252284139275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40884575496311003045519033 30663431622233252284139275)
  ·
    refine ⟨45995147433349878426208913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30663431622233252284139275 45995147433349878426208913)
    ·
      refine ⟨34496360575012408819656685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45995147433349878426208913 34496360575012408819656685)
      ·
        refine ⟨12936135215629653307371257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34496360575012408819656685 12936135215629653307371257)
        ·
          refine ⟨9702101411722239980528443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12936135215629653307371257 9702101411722239980528443)
          ·
            refine ⟨14553152117583359970792665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9702101411722239980528443 14553152117583359970792665)
            ·
              refine ⟨10914864088187519978094499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14553152117583359970792665 10914864088187519978094499)
              ·
                refine ⟨16372296132281279967141749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10914864088187519978094499 16372296132281279967141749)
                ·
                  refine ⟨1534902762401369996919539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16372296132281279967141749 1534902762401369996919539)
                  ·
                    refine ⟨2302354143602054995379309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1534902762401369996919539 2302354143602054995379309)
                    ·
                      refine ⟨863382803850770623267241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2302354143602054995379309 863382803850770623267241)
                      ·
                        rfl

theorem cell23_1681432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1681432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681432 prefixEnd_1681432 := by exact prefixLift 1681432
  have htrace : WordTrace (prefixWord ++ tailWord_1681432) baseStart_1681432 baseEnd_1681432 := by
    simpa [prefixWord, tailWord_1681432, baseEnd_1681432] using wordTrace_append hprefix tailTrace_1681432
  have hstable : (prefixWord ++ tailWord_1681432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681432).length < 2 ^ (prefixWord ++ tailWord_1681432).sum := by decide
  have hdescent : baseEnd_1681432 < baseStart_1681432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681435 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 1, 5]
def baseStart_1681435 : Nat := 118140960795 + 1681435 * 2 ^ 59
def prefixEnd_1681435 : Nat := 4983230072969 + 3 ^ 40 * 1681435 * 2
def baseEnd_1681435 : Nat := 287794781430911370509909

theorem tailTrace_1681435 : CollatzResearch.WordTrace tailWord_1681435 prefixEnd_1681435 287794781430911370509909 := by
  unfold tailWord_1681435
  simp only [CollatzResearch.WordTrace]
  refine ⟨61326972663455636080637759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40884648442303757387091839 61326972663455636080637759)
  ·
    refine ⟨91990458995183454120956639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61326972663455636080637759 91990458995183454120956639)
    ·
      refine ⟨137985688492775181181434959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91990458995183454120956639 137985688492775181181434959)
      ·
        refine ⟨206978532739162771772152439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137985688492775181181434959 206978532739162771772152439)
        ·
          refine ⟨310467799108744157658228659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206978532739162771772152439 310467799108744157658228659)
          ·
            refine ⟨465701698663116236487342989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310467799108744157658228659 465701698663116236487342989)
            ·
              refine ⟨174638136998668588682753621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465701698663116236487342989 174638136998668588682753621)
              ·
                refine ⟨2046540667953147523626019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 174638136998668588682753621 2046540667953147523626019)
                ·
                  refine ⟨3069811001929721285439029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046540667953147523626019 3069811001929721285439029)
                  ·
                    refine ⟨287794781430911370509909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3069811001929721285439029 287794781430911370509909)
                    ·
                      rfl

theorem cell23_1681435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 5].length) (baseStart_1681435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681435 prefixEnd_1681435 := by exact prefixLift 1681435
  have htrace : WordTrace (prefixWord ++ tailWord_1681435) baseStart_1681435 baseEnd_1681435 := by
    simpa [prefixWord, tailWord_1681435, baseEnd_1681435] using wordTrace_append hprefix tailTrace_1681435
  have hstable : (prefixWord ++ tailWord_1681435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681435).length < 2 ^ (prefixWord ++ tailWord_1681435).sum := by decide
  have hdescent : baseEnd_1681435 < baseStart_1681435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681460 : List Nat := [2, 5, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_1681460 : Nat := 118140960795 + 1681460 * 2 ^ 59
def prefixEnd_1681460 : Nat := 4983230072969 + 3 ^ 40 * 1681460 * 2
def baseEnd_1681460 : Nat := 287799060436365504572371

theorem tailTrace_1681460 : CollatzResearch.WordTrace tailWord_1681460 prefixEnd_1681460 287799060436365504572371 := by
  unfold tailWord_1681460
  simp only [CollatzResearch.WordTrace]
  refine ⟨30663942244182532675148917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40885256325576710233531889 30663942244182532675148917)
  ·
    refine ⟨2874744585392112438295211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30663942244182532675148917 2874744585392112438295211)
    ·
      refine ⟨4312116878088168657442817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874744585392112438295211 4312116878088168657442817)
      ·
        refine ⟨3234087658566126493082113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4312116878088168657442817 3234087658566126493082113)
        ·
          refine ⟨2425565743924594869811585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3234087658566126493082113 2425565743924594869811585)
          ·
            refine ⟨1819174307943446152358689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425565743924594869811585 1819174307943446152358689)
            ·
              refine ⟨1364380730957584614269017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819174307943446152358689 1364380730957584614269017)
              ·
                refine ⟨1023285548218188460701763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364380730957584614269017 1023285548218188460701763)
                ·
                  refine ⟨1534928322327282691052645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023285548218188460701763 1534928322327282691052645)
                  ·
                    refine ⟨287799060436365504572371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1534928322327282691052645 287799060436365504572371)
                    ·
                      rfl

theorem cell23_1681460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_1681460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681460 prefixEnd_1681460 := by exact prefixLift 1681460
  have htrace : WordTrace (prefixWord ++ tailWord_1681460) baseStart_1681460 baseEnd_1681460 := by
    simpa [prefixWord, tailWord_1681460, baseEnd_1681460] using wordTrace_append hprefix tailTrace_1681460
  have hstable : (prefixWord ++ tailWord_1681460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681460).length < 2 ^ (prefixWord ++ tailWord_1681460).sum := by decide
  have hdescent : baseEnd_1681460 < baseStart_1681460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681506 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1681506 : Nat := 118140960795 + 1681506 * 2 ^ 59
def prefixEnd_1681506 : Nat := 4983230072969 + 3 ^ 40 * 1681506 * 2
def baseEnd_1681506 : Nat := 863420801419203333741901

theorem tailTrace_1681506 : CollatzResearch.WordTrace tailWord_1681506 prefixEnd_1681506 863420801419203333741901 := by
  unfold tailWord_1681506
  simp only [CollatzResearch.WordTrace]
  refine ⟨15332390561549603801618093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40886374830798943470981581 15332390561549603801618093)
  ·
    refine ⟨5749646460581101425606785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15332390561549603801618093 5749646460581101425606785)
    ·
      refine ⟨4312234845435826069205089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5749646460581101425606785 4312234845435826069205089)
      ·
        refine ⟨3234176134076869551903817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4312234845435826069205089 3234176134076869551903817)
        ·
          refine ⟨2425632100557652163927863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3234176134076869551903817 2425632100557652163927863)
          ·
            refine ⟨3638448150836478245891795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425632100557652163927863 3638448150836478245891795)
            ·
              refine ⟨5457672226254717368837693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638448150836478245891795 5457672226254717368837693)
              ·
                refine ⟨2046627084845519013314135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5457672226254717368837693 2046627084845519013314135)
                ·
                  refine ⟨3069940627268278519971203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046627084845519013314135 3069940627268278519971203)
                  ·
                    refine ⟨4604910940902417779956805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3069940627268278519971203 4604910940902417779956805)
                    ·
                      refine ⟨863420801419203333741901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4604910940902417779956805 863420801419203333741901)
                      ·
                        rfl

theorem cell23_1681506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1681506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681506 prefixEnd_1681506 := by exact prefixLift 1681506
  have htrace : WordTrace (prefixWord ++ tailWord_1681506) baseStart_1681506 baseEnd_1681506 := by
    simpa [prefixWord, tailWord_1681506, baseEnd_1681506] using wordTrace_append hprefix tailTrace_1681506
  have hstable : (prefixWord ++ tailWord_1681506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681506).length < 2 ^ (prefixWord ++ tailWord_1681506).sum := by decide
  have hdescent : baseEnd_1681506 < baseStart_1681506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681509 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 1, 2, 3]
def baseStart_1681509 : Nat := 118140960795 + 1681509 * 2 ^ 59
def prefixEnd_1681509 : Nat := 4983230072969 + 3 ^ 40 * 1681509 * 2
def baseEnd_1681509 : Nat := 863422341861166822004387

theorem tailTrace_1681509 : CollatzResearch.WordTrace tailWord_1681509 prefixEnd_1681509 863422341861166822004387 := by
  unfold tailWord_1681509
  simp only [CollatzResearch.WordTrace]
  refine ⟨61329671665187546718831581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40886447776791697812554387 61329671665187546718831581)
  ·
    refine ⟨22998626874445330019561843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61329671665187546718831581 22998626874445330019561843)
    ·
      refine ⟨34497940311667995029342765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22998626874445330019561843 34497940311667995029342765)
      ·
        refine ⟨12936727616875498136003537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34497940311667995029342765 12936727616875498136003537)
        ·
          refine ⟨9702545712656623602002653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12936727616875498136003537 9702545712656623602002653)
          ·
            refine ⟨3638454642246233850750995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9702545712656623602002653 3638454642246233850750995)
            ·
              refine ⟨5457681963369350776126493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638454642246233850750995 5457681963369350776126493)
              ·
                refine ⟨2046630736263506541047435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5457681963369350776126493 2046630736263506541047435)
                ·
                  refine ⟨3069946104395259811571153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046630736263506541047435 3069946104395259811571153)
                  ·
                    refine ⟨2302459578296444858678365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3069946104395259811571153 2302459578296444858678365)
                    ·
                      refine ⟨863422341861166822004387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2302459578296444858678365 863422341861166822004387)
                      ·
                        rfl

theorem cell23_1681509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_1681509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681509 prefixEnd_1681509 := by exact prefixLift 1681509
  have htrace : WordTrace (prefixWord ++ tailWord_1681509) baseStart_1681509 baseEnd_1681509 := by
    simpa [prefixWord, tailWord_1681509, baseEnd_1681509] using wordTrace_append hprefix tailTrace_1681509
  have hstable : (prefixWord ++ tailWord_1681509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681509).length < 2 ^ (prefixWord ++ tailWord_1681509).sum := by decide
  have hdescent : baseEnd_1681509 < baseStart_1681509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681539 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 1, 3, 3]
def baseStart_1681539 : Nat := 118140960795 + 1681539 * 2 ^ 59
def prefixEnd_1681539 : Nat := 4983230072969 + 3 ^ 40 * 1681539 * 2
def baseEnd_1681539 : Nat := 863437746280801704629249

theorem tailTrace_1681539 : CollatzResearch.WordTrace tailWord_1681539 prefixEnd_1681539 863437746280801704629249 := by
  unfold tailWord_1681539
  simp only [CollatzResearch.WordTrace]
  refine ⟨61330765855078861842423671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40887177236719241228282447 61330765855078861842423671)
  ·
    refine ⟨91996148782618292763635507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61330765855078861842423671 91996148782618292763635507)
    ·
      refine ⟨137994223173927439145453261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91996148782618292763635507 137994223173927439145453261)
      ·
        refine ⟨51747833690222789679544973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137994223173927439145453261 51747833690222789679544973)
        ·
          refine ⟨19405437633833546129829365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51747833690222789679544973 19405437633833546129829365)
          ·
            refine ⟨1819259778171894949671503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19405437633833546129829365 1819259778171894949671503)
            ·
              refine ⟨2728889667257842424507255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819259778171894949671503 2728889667257842424507255)
              ·
                refine ⟨4093334500886763636760883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728889667257842424507255 4093334500886763636760883)
                ·
                  refine ⟨6140001751330145455141325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093334500886763636760883 6140001751330145455141325)
                  ·
                    refine ⟨2302500656748804545677997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6140001751330145455141325 2302500656748804545677997)
                    ·
                      refine ⟨863437746280801704629249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2302500656748804545677997 863437746280801704629249)
                      ·
                        rfl

theorem cell23_1681539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_1681539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681539 prefixEnd_1681539 := by exact prefixLift 1681539
  have htrace : WordTrace (prefixWord ++ tailWord_1681539) baseStart_1681539 baseEnd_1681539 := by
    simpa [prefixWord, tailWord_1681539, baseEnd_1681539] using wordTrace_append hprefix tailTrace_1681539
  have hstable : (prefixWord ++ tailWord_1681539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681539).length < 2 ^ (prefixWord ++ tailWord_1681539).sum := by decide
  have hdescent : baseEnd_1681539 < baseStart_1681539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681632 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 2, 5]
def baseStart_1681632 : Nat := 118140960795 + 1681632 * 2 ^ 59
def prefixEnd_1681632 : Nat := 4983230072969 + 3 ^ 40 * 1681632 * 2
def baseEnd_1681632 : Nat := 287828499993889946922107

theorem tailTrace_1681632 : CollatzResearch.WordTrace tailWord_1681632 prefixEnd_1681632 287828499993889946922107 := by
  unfold tailWord_1681632
  simp only [CollatzResearch.WordTrace]
  refine ⟨30667078921870969362779575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40889438562494625817039433 30667078921870969362779575)
  ·
    refine ⟨46000618382806454044169363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30667078921870969362779575 46000618382806454044169363)
    ·
      refine ⟨69000927574209681066254045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46000618382806454044169363 69000927574209681066254045)
      ·
        refine ⟨25875347840328630399845267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69000927574209681066254045 25875347840328630399845267)
        ·
          refine ⟨38813021760492945599767901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25875347840328630399845267 38813021760492945599767901)
          ·
            refine ⟨14554883160184854599912963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38813021760492945599767901 14554883160184854599912963)
            ·
              refine ⟨21832324740277281899869445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14554883160184854599912963 21832324740277281899869445)
              ·
                refine ⟨4093560888801990356225521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21832324740277281899869445 4093560888801990356225521)
                ·
                  refine ⟨3070170666601492767169141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4093560888801990356225521 3070170666601492767169141)
                  ·
                    refine ⟨287828499993889946922107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3070170666601492767169141 287828499993889946922107)
                    ·
                      rfl

theorem cell23_1681632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_1681632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681632 prefixEnd_1681632 := by exact prefixLift 1681632
  have htrace : WordTrace (prefixWord ++ tailWord_1681632) baseStart_1681632 baseEnd_1681632 := by
    simpa [prefixWord, tailWord_1681632, baseEnd_1681632] using wordTrace_append hprefix tailTrace_1681632
  have hstable : (prefixWord ++ tailWord_1681632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681632).length < 2 ^ (prefixWord ++ tailWord_1681632).sum := by decide
  have hdescent : baseEnd_1681632 < baseStart_1681632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681642 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1681642 : Nat := 118140960795 + 1681642 * 2 ^ 59
def prefixEnd_1681642 : Nat := 4983230072969 + 3 ^ 40 * 1681642 * 2
def baseEnd_1681642 : Nat := 863490634788214801641275

theorem tailTrace_1681642 : CollatzResearch.WordTrace tailWord_1681642 prefixEnd_1681642 863490634788214801641275 := by
  unfold tailWord_1681642
  simp only [CollatzResearch.WordTrace]
  refine ⟨15333630643426427608355795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40889681715803806955615453 15333630643426427608355795)
  ·
    refine ⟨23000445965139641412533693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15333630643426427608355795 23000445965139641412533693)
    ·
      refine ⟨8625167236927365529700135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23000445965139641412533693 8625167236927365529700135)
      ·
        refine ⟨12937750855391048294550203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8625167236927365529700135 12937750855391048294550203)
        ·
          refine ⟨19406626283086572441825305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12937750855391048294550203 19406626283086572441825305)
          ·
            refine ⟨14554969712314929331368979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19406626283086572441825305 14554969712314929331368979)
            ·
              refine ⟨21832454568472393997053469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14554969712314929331368979 21832454568472393997053469)
              ·
                refine ⟨8187170463177147748895051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21832454568472393997053469 8187170463177147748895051)
                ·
                  refine ⟨12280755694765721623342577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8187170463177147748895051 12280755694765721623342577)
                  ·
                    refine ⟨9210566771074291217506933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12280755694765721623342577 9210566771074291217506933)
                    ·
                      refine ⟨863490634788214801641275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9210566771074291217506933 863490634788214801641275)
                      ·
                        rfl

theorem cell23_1681642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1681642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681642 prefixEnd_1681642 := by exact prefixLift 1681642
  have htrace : WordTrace (prefixWord ++ tailWord_1681642) baseStart_1681642 baseEnd_1681642 := by
    simpa [prefixWord, tailWord_1681642, baseEnd_1681642] using wordTrace_append hprefix tailTrace_1681642
  have hstable : (prefixWord ++ tailWord_1681642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681642).length < 2 ^ (prefixWord ++ tailWord_1681642).sum := by decide
  have hdescent : baseEnd_1681642 < baseStart_1681642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681666 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1681666 : Nat := 118140960795 + 1681666 * 2 ^ 59
def prefixEnd_1681666 : Nat := 4983230072969 + 3 ^ 40 * 1681666 * 2
def baseEnd_1681666 : Nat := 287834319441307569247055

theorem tailTrace_1681666 : CollatzResearch.WordTrace tailWord_1681666 prefixEnd_1681666 287834319441307569247055 := by
  unfold tailWord_1681666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15333849481404690633074213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40890265283745841688197901 15333849481404690633074213)
  ·
    refine ⟨2875096777763379493701415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15333849481404690633074213 2875096777763379493701415)
    ·
      refine ⟨4312645166645069240552123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2875096777763379493701415 4312645166645069240552123)
      ·
        refine ⟨6468967749967603860828185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312645166645069240552123 6468967749967603860828185)
        ·
          refine ⟨4851725812475702895621139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6468967749967603860828185 4851725812475702895621139)
          ·
            refine ⟨7277588718713554343431709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4851725812475702895621139 7277588718713554343431709)
            ·
              refine ⟨2729095769517582878786891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7277588718713554343431709 2729095769517582878786891)
              ·
                refine ⟨4093643654276374318180337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2729095769517582878786891 4093643654276374318180337)
                ·
                  refine ⟨3070232740707280738635253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4093643654276374318180337 3070232740707280738635253)
                  ·
                    refine ⟨287834319441307569247055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3070232740707280738635253 287834319441307569247055)
                    ·
                      rfl

theorem cell23_1681666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1681666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681666 prefixEnd_1681666 := by exact prefixLift 1681666
  have htrace : WordTrace (prefixWord ++ tailWord_1681666) baseStart_1681666 baseEnd_1681666 := by
    simpa [prefixWord, tailWord_1681666, baseEnd_1681666] using wordTrace_append hprefix tailTrace_1681666
  have hstable : (prefixWord ++ tailWord_1681666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681666).length < 2 ^ (prefixWord ++ tailWord_1681666).sum := by decide
  have hdescent : baseEnd_1681666 < baseStart_1681666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681696 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 3, 4]
def baseStart_1681696 : Nat := 118140960795 + 1681696 * 2 ^ 59
def prefixEnd_1681696 : Nat := 4983230072969 + 3 ^ 40 * 1681696 * 2
def baseEnd_1681696 : Nat := 287839454247852530122009

theorem tailTrace_1681696 : CollatzResearch.WordTrace tailWord_1681696 prefixEnd_1681696 287839454247852530122009 := by
  unfold tailWord_1681696
  simp only [CollatzResearch.WordTrace]
  refine ⟨30668246057755038827944471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40890994743673385103925961 30668246057755038827944471)
  ·
    refine ⟨46002369086632558241916707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30668246057755038827944471 46002369086632558241916707)
    ·
      refine ⟨69003553629948837362875061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46002369086632558241916707 69003553629948837362875061)
      ·
        refine ⟨6469083152807703502769537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69003553629948837362875061 6469083152807703502769537)
        ·
          refine ⟨4851812364605777627077153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6469083152807703502769537 4851812364605777627077153)
          ·
            refine ⟨3638859273454333220307865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4851812364605777627077153 3638859273454333220307865)
            ·
              refine ⟨2729144455090749915230899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3638859273454333220307865 2729144455090749915230899)
              ·
                refine ⟨4093716682636124872846349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2729144455090749915230899 4093716682636124872846349)
                ·
                  refine ⟨1535143755988546827317381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4093716682636124872846349 1535143755988546827317381)
                  ·
                    refine ⟨287839454247852530122009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1535143755988546827317381 287839454247852530122009)
                    ·
                      rfl

theorem cell23_1681696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3, 4].length) (baseStart_1681696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681696 prefixEnd_1681696 := by exact prefixLift 1681696
  have htrace : WordTrace (prefixWord ++ tailWord_1681696) baseStart_1681696 baseEnd_1681696 := by
    simpa [prefixWord, tailWord_1681696, baseEnd_1681696] using wordTrace_append hprefix tailTrace_1681696
  have hstable : (prefixWord ++ tailWord_1681696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681696).length < 2 ^ (prefixWord ++ tailWord_1681696).sum := by decide
  have hdescent : baseEnd_1681696 < baseStart_1681696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681746 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_1681746 : Nat := 118140960795 + 1681746 * 2 ^ 59
def prefixEnd_1681746 : Nat := 4983230072969 + 3 ^ 40 * 1681746 * 2
def baseEnd_1681746 : Nat := 863544036776282394740797

theorem tailTrace_1681746 : CollatzResearch.WordTrace tailWord_1681746 prefixEnd_1681746 863544036776282394740797 := by
  unfold tailWord_1681746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15334578941332234048802273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40892210510219290796806061 15334578941332234048802273)
  ·
    refine ⟨11500934205999175536601705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15334578941332234048802273 11500934205999175536601705)
    ·
      refine ⟨8625700654499381652451279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11500934205999175536601705 8625700654499381652451279)
      ·
        refine ⟨12938550981749072478676919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8625700654499381652451279 12938550981749072478676919)
        ·
          refine ⟨19407826472623608718015379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12938550981749072478676919 19407826472623608718015379)
          ·
            refine ⟨29111739708935413077023069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19407826472623608718015379 29111739708935413077023069)
            ·
              refine ⟨10916902390850779903883651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29111739708935413077023069 10916902390850779903883651)
              ·
                refine ⟨16375353586276169855825477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10916902390850779903883651 16375353586276169855825477)
                ·
                  refine ⟨3070378797426781847967277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16375353586276169855825477 3070378797426781847967277)
                  ·
                    refine ⟨1151392049035043192987729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070378797426781847967277 1151392049035043192987729)
                    ·
                      refine ⟨863544036776282394740797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1151392049035043192987729 863544036776282394740797)
                      ·
                        rfl

theorem cell23_1681746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_1681746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681746 prefixEnd_1681746 := by exact prefixLift 1681746
  have htrace : WordTrace (prefixWord ++ tailWord_1681746) baseStart_1681746 baseEnd_1681746 := by
    simpa [prefixWord, tailWord_1681746, baseEnd_1681746] using wordTrace_append hprefix tailTrace_1681746
  have hstable : (prefixWord ++ tailWord_1681746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681746).length < 2 ^ (prefixWord ++ tailWord_1681746).sum := by decide
  have hdescent : baseEnd_1681746 < baseStart_1681746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681752 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 5, 6]
def baseStart_1681752 : Nat := 118140960795 + 1681752 * 2 ^ 59
def prefixEnd_1681752 : Nat := 4983230072969 + 3 ^ 40 * 1681752 * 2
def baseEnd_1681752 : Nat := 287849039220069790421923

theorem tailTrace_1681752 : CollatzResearch.WordTrace tailWord_1681752 prefixEnd_1681752 287849039220069790421923 := by
  unfold tailWord_1681752
  simp only [CollatzResearch.WordTrace]
  refine ⟨30669267301653599609963755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40892356402204799479951673 30669267301653599609963755)
  ·
    refine ⟨46003900952480399414945633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30669267301653599609963755 46003900952480399414945633)
    ·
      refine ⟨34502925714360299561209225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46003900952480399414945633 34502925714360299561209225)
      ·
        refine ⟨25877194285770224670906919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34502925714360299561209225 25877194285770224670906919)
        ·
          refine ⟨38815791428655337006360379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25877194285770224670906919 38815791428655337006360379)
          ·
            refine ⟨58223687142983005509540569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38815791428655337006360379 58223687142983005509540569)
            ·
              refine ⟨43667765357237254132155427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58223687142983005509540569 43667765357237254132155427)
              ·
                refine ⟨65501648035855881198233141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43667765357237254132155427 65501648035855881198233141)
                ·
                  refine ⟨6140779503361488862334357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65501648035855881198233141 6140779503361488862334357)
                  ·
                    refine ⟨287849039220069790421923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6140779503361488862334357 287849039220069790421923)
                    ·
                      rfl

theorem cell23_1681752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_1681752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681752 prefixEnd_1681752 := by exact prefixLift 1681752
  have htrace : WordTrace (prefixWord ++ tailWord_1681752) baseStart_1681752 baseEnd_1681752 := by
    simpa [prefixWord, tailWord_1681752, baseEnd_1681752] using wordTrace_append hprefix tailTrace_1681752
  have hstable : (prefixWord ++ tailWord_1681752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681752).length < 2 ^ (prefixWord ++ tailWord_1681752).sum := by decide
  have hdescent : baseEnd_1681752 < baseStart_1681752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681776 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 4]
def baseStart_1681776 : Nat := 118140960795 + 1681776 * 2 ^ 59
def prefixEnd_1681776 : Nat := 4983230072969 + 3 ^ 40 * 1681776 * 2
def baseEnd_1681776 : Nat := 863559441195917277365659

theorem tailTrace_1681776 : CollatzResearch.WordTrace tailWord_1681776 prefixEnd_1681776 863559441195917277365659 := by
  unfold tailWord_1681776
  simp only [CollatzResearch.WordTrace]
  refine ⟨30669704977610125659400591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40892939970146834212534121 30669704977610125659400591)
  ·
    refine ⟨46004557466415188489100887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30669704977610125659400591 46004557466415188489100887)
    ·
      refine ⟨69006836199622782733651331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46004557466415188489100887 69006836199622782733651331)
      ·
        refine ⟨103510254299434174100476997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69006836199622782733651331 103510254299434174100476997)
        ·
          refine ⟨19408172681143907643839437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103510254299434174100476997 19408172681143907643839437)
          ·
            refine ⟨7278064755428965366439789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19408172681143907643839437 7278064755428965366439789)
            ·
              refine ⟨2729274283285862012414921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7278064755428965366439789 2729274283285862012414921)
              ·
                refine ⟨2046955712464396509311191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2729274283285862012414921 2046955712464396509311191)
                ·
                  refine ⟨3070433568696594763966787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046955712464396509311191 3070433568696594763966787)
                  ·
                    refine ⟨4605650353044892145950181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3070433568696594763966787 4605650353044892145950181)
                    ·
                      refine ⟨863559441195917277365659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4605650353044892145950181 863559441195917277365659)
                      ·
                        rfl

theorem cell23_1681776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 4].length) (baseStart_1681776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681776 prefixEnd_1681776 := by exact prefixLift 1681776
  have htrace : WordTrace (prefixWord ++ tailWord_1681776) baseStart_1681776 baseEnd_1681776 := by
    simpa [prefixWord, tailWord_1681776, baseEnd_1681776] using wordTrace_append hprefix tailTrace_1681776
  have hstable : (prefixWord ++ tailWord_1681776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681776).length < 2 ^ (prefixWord ++ tailWord_1681776).sum := by decide
  have hdescent : baseEnd_1681776 < baseStart_1681776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681779 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 3]
def baseStart_1681779 : Nat := 118140960795 + 1681779 * 2 ^ 59
def prefixEnd_1681779 : Nat := 4983230072969 + 3 ^ 40 * 1681779 * 2
def baseEnd_1681779 : Nat := 863560981637880765628145

theorem tailTrace_1681779 : CollatzResearch.WordTrace tailWord_1681779 prefixEnd_1681779 863560981637880765628145 := by
  unfold tailWord_1681779
  simp only [CollatzResearch.WordTrace]
  refine ⟨61339519374209382831160391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40893012916139588554106927 61339519374209382831160391)
  ·
    refine ⟨92009279061314074246740587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61339519374209382831160391 92009279061314074246740587)
    ·
      refine ⟨138013918591971111370110881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92009279061314074246740587 138013918591971111370110881)
      ·
        refine ⟨103510438943978333527583161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138013918591971111370110881 103510438943978333527583161)
        ·
          refine ⟨77632829207983750145687371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103510438943978333527583161 77632829207983750145687371)
          ·
            refine ⟨116449243811975625218531057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77632829207983750145687371 116449243811975625218531057)
            ·
              refine ⟨87336932858981718913898293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116449243811975625218531057 87336932858981718913898293)
              ·
                refine ⟨8187837455529536148177965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87336932858981718913898293 8187837455529536148177965)
                ·
                  refine ⟨3070439045823576055566737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8187837455529536148177965 3070439045823576055566737)
                  ·
                    refine ⟨2302829284367682041675053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3070439045823576055566737 2302829284367682041675053)
                    ·
                      refine ⟨863560981637880765628145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2302829284367682041675053 863560981637880765628145)
                      ·
                        rfl

theorem cell23_1681779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 3].length) (baseStart_1681779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681779 prefixEnd_1681779 := by exact prefixLift 1681779
  have htrace : WordTrace (prefixWord ++ tailWord_1681779) baseStart_1681779 baseEnd_1681779 := by
    simpa [prefixWord, tailWord_1681779, baseEnd_1681779] using wordTrace_append hprefix tailTrace_1681779
  have hstable : (prefixWord ++ tailWord_1681779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681779).length < 2 ^ (prefixWord ++ tailWord_1681779).sum := by decide
  have hdescent : baseEnd_1681779 < baseStart_1681779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681789 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_1681789 : Nat := 118140960795 + 1681789 * 2 ^ 59
def prefixEnd_1681789 : Nat := 4983230072969 + 3 ^ 40 * 1681789 * 2
def baseEnd_1681789 : Nat := 863566116444425726503099

theorem tailTrace_1681789 : CollatzResearch.WordTrace tailWord_1681789 prefixEnd_1681789 863566116444425726503099 := by
  unfold tailWord_1681789
  simp only [CollatzResearch.WordTrace]
  refine ⟨61339884104173154539024421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40893256069448769692682947 61339884104173154539024421)
  ·
    refine ⟨11501228269532466476067079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61339884104173154539024421 11501228269532466476067079)
    ·
      refine ⟨17251842404298699714100619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11501228269532466476067079 17251842404298699714100619)
      ·
        refine ⟨25877763606448049571150929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17251842404298699714100619 25877763606448049571150929)
        ·
          refine ⟨19408322704836037178363197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25877763606448049571150929 19408322704836037178363197)
          ·
            refine ⟨7278121014313513941886199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19408322704836037178363197 7278121014313513941886199)
            ·
              refine ⟨10917181521470270912829299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7278121014313513941886199 10917181521470270912829299)
              ·
                refine ⟨16375772282205406369243949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10917181521470270912829299 16375772282205406369243949)
                ·
                  refine ⟨6140914605827027388466481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16375772282205406369243949 6140914605827027388466481)
                  ·
                    refine ⟨4605685954370270541349861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6140914605827027388466481 4605685954370270541349861)
                    ·
                      refine ⟨863566116444425726503099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4605685954370270541349861 863566116444425726503099)
                      ·
                        rfl

theorem cell23_1681789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_1681789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681789 prefixEnd_1681789 := by exact prefixLift 1681789
  have htrace : WordTrace (prefixWord ++ tailWord_1681789) baseStart_1681789 baseEnd_1681789 := by
    simpa [prefixWord, tailWord_1681789, baseEnd_1681789] using wordTrace_append hprefix tailTrace_1681789
  have hstable : (prefixWord ++ tailWord_1681789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681789).length < 2 ^ (prefixWord ++ tailWord_1681789).sum := by decide
  have hdescent : baseEnd_1681789 < baseStart_1681789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681816 : List Nat := [2, 1, 2, 5, 1, 3, 1, 8]
def baseStart_1681816 : Nat := 118140960795 + 1681816 * 2 ^ 59
def prefixEnd_1681816 : Nat := 4983230072969 + 3 ^ 40 * 1681816 * 2
def baseEnd_1681816 : Nat := 31984443719336930402425

theorem tailTrace_1681816 : CollatzResearch.WordTrace tailWord_1681816 prefixEnd_1681816 31984443719336930402425 := by
  unfold tailWord_1681816
  simp only [CollatzResearch.WordTrace]
  refine ⟨30670434437537669075128651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40893912583383558766838201 30670434437537669075128651)
  ·
    refine ⟨46005651656306503612692977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30670434437537669075128651 46005651656306503612692977)
    ·
      refine ⟨34504238742229877709519733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46005651656306503612692977 34504238742229877709519733)
      ·
        refine ⟨3234772382084051035267475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34504238742229877709519733 3234772382084051035267475)
        ·
          refine ⟨4852158573126076552901213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234772382084051035267475 4852158573126076552901213)
          ·
            refine ⟨1819559464922278707337955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4852158573126076552901213 1819559464922278707337955)
            ·
              refine ⟨2729339197383418061006933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819559464922278707337955 2729339197383418061006933)
              ·
                refine ⟨31984443719336930402425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2729339197383418061006933 31984443719336930402425)
                ·
                  rfl

theorem cell23_1681816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 8].length) (baseStart_1681816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681816 prefixEnd_1681816 := by exact prefixLift 1681816
  have htrace : WordTrace (prefixWord ++ tailWord_1681816) baseStart_1681816 baseEnd_1681816 := by
    simpa [prefixWord, tailWord_1681816, baseEnd_1681816] using wordTrace_append hprefix tailTrace_1681816
  have hstable : (prefixWord ++ tailWord_1681816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681816).length < 2 ^ (prefixWord ++ tailWord_1681816).sum := by decide
  have hdescent : baseEnd_1681816 < baseStart_1681816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681844 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_1681844 : Nat := 118140960795 + 1681844 * 2 ^ 59
def prefixEnd_1681844 : Nat := 4983230072969 + 3 ^ 40 * 1681844 * 2
def baseEnd_1681844 : Nat := 863594357880423011315347

theorem tailTrace_1681844 : CollatzResearch.WordTrace tailWord_1681844 prefixEnd_1681844 863594357880423011315347 := by
  unfold tailWord_1681844
  simp only [CollatzResearch.WordTrace]
  refine ⟨30670945059486949466138293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40894593412649265954851057 30670945059486949466138293)
  ·
    refine ⟨2875401099326901512450465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30670945059486949466138293 2875401099326901512450465)
    ·
      refine ⟨2156550824495176134337849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2875401099326901512450465 2156550824495176134337849)
      ·
        refine ⟨1617413118371382100753387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2156550824495176134337849 1617413118371382100753387)
        ·
          refine ⟨2426119677557073151130081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617413118371382100753387 2426119677557073151130081)
          ·
            refine ⟨1819589758167804863347561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2426119677557073151130081 1819589758167804863347561)
            ·
              refine ⟨1364692318625853647510671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819589758167804863347561 1364692318625853647510671)
              ·
                refine ⟨2047038477938780471266007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364692318625853647510671 2047038477938780471266007)
                ·
                  refine ⟨3070557716908170706899011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047038477938780471266007 3070557716908170706899011)
                  ·
                    refine ⟨4605836575362256060348517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3070557716908170706899011 4605836575362256060348517)
                    ·
                      refine ⟨863594357880423011315347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4605836575362256060348517 863594357880423011315347)
                      ·
                        rfl

theorem cell23_1681844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_1681844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681844 prefixEnd_1681844 := by exact prefixLift 1681844
  have htrace : WordTrace (prefixWord ++ tailWord_1681844) baseStart_1681844 baseEnd_1681844 := by
    simpa [prefixWord, tailWord_1681844, baseEnd_1681844] using wordTrace_append hprefix tailTrace_1681844
  have hstable : (prefixWord ++ tailWord_1681844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681844).length < 2 ^ (prefixWord ++ tailWord_1681844).sum := by decide
  have hdescent : baseEnd_1681844 < baseStart_1681844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681860 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1681860 : Nat := 118140960795 + 1681860 * 2 ^ 59
def prefixEnd_1681860 : Nat := 4983230072969 + 3 ^ 40 * 1681860 * 2
def baseEnd_1681860 : Nat := 863602573570894948715273

theorem tailTrace_1681860 : CollatzResearch.WordTrace tailWord_1681860 prefixEnd_1681860 863602573570894948715273 := by
  unfold tailWord_1681860
  simp only [CollatzResearch.WordTrace]
  refine ⟨30671236843457966832429517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40894982457943955776572689 30671236843457966832429517)
  ·
    refine ⟨11501713816296737562161069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30671236843457966832429517 11501713816296737562161069)
    ·
      refine ⟨4313142681111276585810401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11501713816296737562161069 4313142681111276585810401)
      ·
        refine ⟨3234857010833457439357801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4313142681111276585810401 3234857010833457439357801)
        ·
          refine ⟨2426142758125093079518351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3234857010833457439357801 2426142758125093079518351)
          ·
            refine ⟨3639214137187639619277527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426142758125093079518351 3639214137187639619277527)
            ·
              refine ⟨5458821205781459428916291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639214137187639619277527 5458821205781459428916291)
              ·
                refine ⟨8188231808672189143374437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5458821205781459428916291 8188231808672189143374437)
                ·
                  refine ⟨1535293464126035464382707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8188231808672189143374437 1535293464126035464382707)
                  ·
                    refine ⟨2302940196189053196574061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1535293464126035464382707 2302940196189053196574061)
                    ·
                      refine ⟨863602573570894948715273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2302940196189053196574061 863602573570894948715273)
                      ·
                        rfl

theorem cell23_1681860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1681860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681860 prefixEnd_1681860 := by exact prefixLift 1681860
  have htrace : WordTrace (prefixWord ++ tailWord_1681860) baseStart_1681860 baseEnd_1681860 := by
    simpa [prefixWord, tailWord_1681860, baseEnd_1681860] using wordTrace_append hprefix tailTrace_1681860
  have hstable : (prefixWord ++ tailWord_1681860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681860).length < 2 ^ (prefixWord ++ tailWord_1681860).sum := by decide
  have hdescent : baseEnd_1681860 < baseStart_1681860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681876 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1681876 : Nat := 118140960795 + 1681876 * 2 ^ 59
def prefixEnd_1681876 : Nat := 4983230072969 + 3 ^ 40 * 1681876 * 2
def baseEnd_1681876 : Nat := 287870263087122295371733

theorem tailTrace_1681876 : CollatzResearch.WordTrace tailWord_1681876 prefixEnd_1681876 287870263087122295371733 := by
  unfold tailWord_1681876
  simp only [CollatzResearch.WordTrace]
  refine ⟨30671528627428984198720741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40895371503238645598294321 30671528627428984198720741)
  ·
    refine ⟨5750911617642934537260139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30671528627428984198720741 5750911617642934537260139)
    ·
      refine ⟨8626367426464401805890209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5750911617642934537260139 8626367426464401805890209)
      ·
        refine ⟨6469775569848301354417657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8626367426464401805890209 6469775569848301354417657)
        ·
          refine ⟨4852331677386226015813243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6469775569848301354417657 4852331677386226015813243)
          ·
            refine ⟨7278497516079339023719865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852331677386226015813243 7278497516079339023719865)
            ·
              refine ⟨5458873137059504267789899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7278497516079339023719865 5458873137059504267789899)
              ·
                refine ⟨8188309705589256401684849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5458873137059504267789899 8188309705589256401684849)
                ·
                  refine ⟨6141232279191942301263637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8188309705589256401684849 6141232279191942301263637)
                  ·
                    refine ⟨287870263087122295371733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6141232279191942301263637 287870263087122295371733)
                    ·
                      rfl

theorem cell23_1681876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1681876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681876 prefixEnd_1681876 := by exact prefixLift 1681876
  have htrace : WordTrace (prefixWord ++ tailWord_1681876) baseStart_1681876 baseEnd_1681876 := by
    simpa [prefixWord, tailWord_1681876, baseEnd_1681876] using wordTrace_append hprefix tailTrace_1681876
  have hstable : (prefixWord ++ tailWord_1681876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681876).length < 2 ^ (prefixWord ++ tailWord_1681876).sum := by decide
  have hdescent : baseEnd_1681876 < baseStart_1681876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681889 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 7]
def baseStart_1681889 : Nat := 118140960795 + 1681889 * 2 ^ 59
def prefixEnd_1681889 : Nat := 4983230072969 + 3 ^ 40 * 1681889 * 2
def baseEnd_1681889 : Nat := 95957496056652815028071

theorem tailTrace_1681889 : CollatzResearch.WordTrace tailWord_1681889 prefixEnd_1681889 95957496056652815028071 := by
  unfold tailWord_1681889
  simp only [CollatzResearch.WordTrace]
  refine ⟨61343531403810871617664721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40895687602540581078443147 61343531403810871617664721)
  ·
    refine ⟨46007648552858153713248541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61343531403810871617664721 46007648552858153713248541)
    ·
      refine ⟨17252868207321807642468203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46007648552858153713248541 17252868207321807642468203)
      ·
        refine ⟨25879302310982711463702305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17252868207321807642468203 25879302310982711463702305)
        ·
          refine ⟨19409476733237033597776729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25879302310982711463702305 19409476733237033597776729)
          ·
            refine ⟨14557107549927775198332547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19409476733237033597776729 14557107549927775198332547)
            ·
              refine ⟨21835661324891662797498821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14557107549927775198332547 21835661324891662797498821)
              ·
                refine ⟨4094186498417186774531029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21835661324891662797498821 4094186498417186774531029)
                ·
                  refine ⟨95957496056652815028071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4094186498417186774531029 95957496056652815028071)
                  ·
                    rfl

theorem cell23_1681889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 7].length) (baseStart_1681889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681889 prefixEnd_1681889 := by exact prefixLift 1681889
  have htrace : WordTrace (prefixWord ++ tailWord_1681889) baseStart_1681889 baseEnd_1681889 := by
    simpa [prefixWord, tailWord_1681889, baseEnd_1681889] using wordTrace_append hprefix tailTrace_1681889
  have hstable : (prefixWord ++ tailWord_1681889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681889).length < 2 ^ (prefixWord ++ tailWord_1681889).sum := by decide
  have hdescent : baseEnd_1681889 < baseStart_1681889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681923 : List Nat := [1, 1, 1, 3, 2, 1, 7, 2, 5]
def baseStart_1681923 : Nat := 118140960795 + 1681923 * 2 ^ 59
def prefixEnd_1681923 : Nat := 4983230072969 + 3 ^ 40 * 1681923 * 2
def baseEnd_1681923 : Nat := 95959435872458689136387

theorem tailTrace_1681923 : CollatzResearch.WordTrace tailWord_1681923 prefixEnd_1681923 95959435872458689136387 := by
  unfold tailWord_1681923
  simp only [CollatzResearch.WordTrace]
  refine ⟨61344771485687695424402423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40896514323791796949601615 61344771485687695424402423)
  ·
    refine ⟨92017157228531543136603635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61344771485687695424402423 92017157228531543136603635)
    ·
      refine ⟨138025735842797314704905453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92017157228531543136603635 138025735842797314704905453)
      ·
        refine ⟨51759650941048993014339545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138025735842797314704905453 51759650941048993014339545)
        ·
          refine ⟨38819738205786744760754659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51759650941048993014339545 38819738205786744760754659)
          ·
            refine ⟨58229607308680117141131989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38819738205786744760754659 58229607308680117141131989)
            ·
              refine ⟨1364756421297190245495281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58229607308680117141131989 1364756421297190245495281)
              ·
                refine ⟨1023567315972892684121461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364756421297190245495281 1023567315972892684121461)
                ·
                  refine ⟨95959435872458689136387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1023567315972892684121461 95959435872458689136387)
                  ·
                    rfl

theorem cell23_1681923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 5].length) (baseStart_1681923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681923 prefixEnd_1681923 := by exact prefixLift 1681923
  have htrace : WordTrace (prefixWord ++ tailWord_1681923) baseStart_1681923 baseEnd_1681923 := by
    simpa [prefixWord, tailWord_1681923, baseEnd_1681923] using wordTrace_append hprefix tailTrace_1681923
  have hstable : (prefixWord ++ tailWord_1681923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681923).length < 2 ^ (prefixWord ++ tailWord_1681923).sum := by decide
  have hdescent : baseEnd_1681923 < baseStart_1681923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681934 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2]
def baseStart_1681934 : Nat := 118140960795 + 1681934 * 2 ^ 59
def prefixEnd_1681934 : Nat := 4983230072969 + 3 ^ 40 * 1681934 * 2
def baseEnd_1681934 : Nat := 863640571139327659189933

theorem tailTrace_1681934 : CollatzResearch.WordTrace tailWord_1681934 prefixEnd_1681934 863640571139327659189933 := by
  unfold tailWord_1681934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7668146586080980537881607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40896781792431896202035237 7668146586080980537881607)
  ·
    refine ⟨11502219879121470806822411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7668146586080980537881607 11502219879121470806822411)
    ·
      refine ⟨17253329818682206210233617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11502219879121470806822411 17253329818682206210233617)
      ·
        refine ⟨12939997364011654657675213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17253329818682206210233617 12939997364011654657675213)
        ·
          refine ⟨4852499011504370496628205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12939997364011654657675213 4852499011504370496628205)
          ·
            refine ⟨1819687129314138936235577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4852499011504370496628205 1819687129314138936235577)
            ·
              refine ⟨1364765346985604202176683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819687129314138936235577 1364765346985604202176683)
              ·
                refine ⟨2047148020478406303265025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364765346985604202176683 2047148020478406303265025)
                ·
                  refine ⟨1535361015358804727448769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2047148020478406303265025 1535361015358804727448769)
                  ·
                    refine ⟨1151520761519103545586577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1535361015358804727448769 1151520761519103545586577)
                    ·
                      refine ⟨863640571139327659189933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1151520761519103545586577 863640571139327659189933)
                      ·
                        rfl

theorem cell23_1681934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_1681934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681934 prefixEnd_1681934 := by exact prefixLift 1681934
  have htrace : WordTrace (prefixWord ++ tailWord_1681934) baseStart_1681934 baseEnd_1681934 := by
    simpa [prefixWord, tailWord_1681934, baseEnd_1681934] using wordTrace_append hprefix tailTrace_1681934
  have hstable : (prefixWord ++ tailWord_1681934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681934).length < 2 ^ (prefixWord ++ tailWord_1681934).sum := by decide
  have hdescent : baseEnd_1681934 < baseStart_1681934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681973 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_1681973 : Nat := 118140960795 + 1681973 * 2 ^ 59
def prefixEnd_1681973 : Nat := 4983230072969 + 3 ^ 40 * 1681973 * 2
def baseEnd_1681973 : Nat := 863660596884853006602253

theorem tailTrace_1681973 : CollatzResearch.WordTrace tailWord_1681973 prefixEnd_1681973 863660596884853006602253 := by
  unfold tailWord_1681973
  simp only [CollatzResearch.WordTrace]
  refine ⟨61346595135506553963722573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40897730090337702642481715 61346595135506553963722573)
  ·
    refine ⟨23004973175814957736395965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61346595135506553963722573 23004973175814957736395965)
    ·
      refine ⟨8626864940930609151148487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23004973175814957736395965 8626864940930609151148487)
      ·
        refine ⟨12940297411395913726722731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8626864940930609151148487 12940297411395913726722731)
        ·
          refine ⟨19410446117093870590084097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12940297411395913726722731 19410446117093870590084097)
          ·
            refine ⟨14557834587820402942563073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19410446117093870590084097 14557834587820402942563073)
            ·
              refine ⟨10918375940865302206922305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14557834587820402942563073 10918375940865302206922305)
              ·
                refine ⟨8188781955648976655191729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10918375940865302206922305 8188781955648976655191729)
                ·
                  refine ⟨6141586466736732491393797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8188781955648976655191729 6141586466736732491393797)
                  ·
                    refine ⟨1151547462513137342136337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6141586466736732491393797 1151547462513137342136337)
                    ·
                      refine ⟨863660596884853006602253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1151547462513137342136337 863660596884853006602253)
                      ·
                        rfl

theorem cell23_1681973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_1681973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681973 prefixEnd_1681973 := by exact prefixLift 1681973
  have htrace : WordTrace (prefixWord ++ tailWord_1681973) baseStart_1681973 baseEnd_1681973 := by
    simpa [prefixWord, tailWord_1681973, baseEnd_1681973] using wordTrace_append hprefix tailTrace_1681973
  have hstable : (prefixWord ++ tailWord_1681973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681973).length < 2 ^ (prefixWord ++ tailWord_1681973).sum := by decide
  have hdescent : baseEnd_1681973 < baseStart_1681973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681996 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 6]
def baseStart_1681996 : Nat := 118140960795 + 1681996 * 2 ^ 59
def prefixEnd_1681996 : Nat := 4983230072969 + 3 ^ 40 * 1681996 * 2
def baseEnd_1681996 : Nat := 95963600771100712957183

theorem tailTrace_1681996 : CollatzResearch.WordTrace tailWord_1681996 prefixEnd_1681996 95963600771100712957183 := by
  unfold tailWord_1681996
  simp only [CollatzResearch.WordTrace]
  refine ⟨30673717007211614445904921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40898289342948819261206561 30673717007211614445904921)
  ·
    refine ⟨23005287755408710834428691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30673717007211614445904921 23005287755408710834428691)
    ·
      refine ⟨34507931633113066251643037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23005287755408710834428691 34507931633113066251643037)
      ·
        refine ⟨12940474362417399844366139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34507931633113066251643037 12940474362417399844366139)
        ·
          refine ⟨19410711543626099766549209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12940474362417399844366139 19410711543626099766549209)
          ·
            refine ⟨14558033657719574824911907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19410711543626099766549209 14558033657719574824911907)
            ·
              refine ⟨21837050486579362237367861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14558033657719574824911907 21837050486579362237367861)
              ·
                refine ⟨2047223483116815209753237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21837050486579362237367861 2047223483116815209753237)
                ·
                  refine ⟨95963600771100712957183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2047223483116815209753237 95963600771100712957183)
                  ·
                    rfl

theorem cell23_1681996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_1681996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1681996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1681996 prefixEnd_1681996 := by exact prefixLift 1681996
  have htrace : WordTrace (prefixWord ++ tailWord_1681996) baseStart_1681996 baseEnd_1681996 := by
    simpa [prefixWord, tailWord_1681996, baseEnd_1681996] using wordTrace_append hprefix tailTrace_1681996
  have hstable : (prefixWord ++ tailWord_1681996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681996).length < 2 ^ (prefixWord ++ tailWord_1681996).sum := by decide
  have hdescent : baseEnd_1681996 < baseStart_1681996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682023 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_1682023 : Nat := 118140960795 + 1682023 * 2 ^ 59
def prefixEnd_1682023 : Nat := 4983230072969 + 3 ^ 40 * 1682023 * 2
def baseEnd_1682023 : Nat := 863686270917577810977023

theorem tailTrace_1682023 : CollatzResearch.WordTrace tailWord_1682023 prefixEnd_1682023 863686270917577810977023 := by
  unfold tailWord_1682023
  simp only [CollatzResearch.WordTrace]
  refine ⟨61348418785325412503042723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40898945856883608335361815 61348418785325412503042723)
  ·
    refine ⟨92022628177988118754564085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61348418785325412503042723 92022628177988118754564085)
    ·
      refine ⟨8627121391686386133240383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92022628177988118754564085 8627121391686386133240383)
      ·
        refine ⟨12940682087529579199860575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8627121391686386133240383 12940682087529579199860575)
        ·
          refine ⟨19411023131294368799790863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12940682087529579199860575 19411023131294368799790863)
          ·
            refine ⟨29116534696941553199686295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19411023131294368799790863 29116534696941553199686295)
            ·
              refine ⟨43674802045412329799529443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29116534696941553199686295 43674802045412329799529443)
              ·
                refine ⟨65512203068118494699294165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43674802045412329799529443 65512203068118494699294165)
                ·
                  refine ⟨1535442259409027219514707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 65512203068118494699294165 1535442259409027219514707)
                  ·
                    refine ⟨2303163389113540829272061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1535442259409027219514707 2303163389113540829272061)
                    ·
                      refine ⟨863686270917577810977023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2303163389113540829272061 863686270917577810977023)
                      ·
                        rfl

theorem cell23_1682023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_1682023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682023 prefixEnd_1682023 := by exact prefixLift 1682023
  have htrace : WordTrace (prefixWord ++ tailWord_1682023) baseStart_1682023 baseEnd_1682023 := by
    simpa [prefixWord, tailWord_1682023, baseEnd_1682023] using wordTrace_append hprefix tailTrace_1682023
  have hstable : (prefixWord ++ tailWord_1682023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682023).length < 2 ^ (prefixWord ++ tailWord_1682023).sum := by decide
  have hdescent : baseEnd_1682023 < baseStart_1682023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682030 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_1682030 : Nat := 118140960795 + 1682030 * 2 ^ 59
def prefixEnd_1682030 : Nat := 4983230072969 + 3 ^ 40 * 1682030 * 2
def baseEnd_1682030 : Nat := 95965540586906587065499

theorem tailTrace_1682030 : CollatzResearch.WordTrace tailWord_1682030 prefixEnd_1682030 95965540586906587065499 := by
  unfold tailWord_1682030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7668584262037506587318443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40899116064200035132365029 7668584262037506587318443)
  ·
    refine ⟨11502876393056259880977665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7668584262037506587318443 11502876393056259880977665)
    ·
      refine ⟨8627157294792194910733249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11502876393056259880977665 8627157294792194910733249)
      ·
        refine ⟨6470367971094146183049937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8627157294792194910733249 6470367971094146183049937)
        ·
          refine ⟨4852775978320609637287453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6470367971094146183049937 4852775978320609637287453)
          ·
            refine ⟨1819790991870228613982795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4852775978320609637287453 1819790991870228613982795)
            ·
              refine ⟨2729686487805342920974193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819790991870228613982795 2729686487805342920974193)
              ·
                refine ⟨2047264865854007190730645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2729686487805342920974193 2047264865854007190730645)
                ·
                  refine ⟨95965540586906587065499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2047264865854007190730645 95965540586906587065499)
                  ·
                    rfl

theorem cell23_1682030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_1682030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682030 prefixEnd_1682030 := by exact prefixLift 1682030
  have htrace : WordTrace (prefixWord ++ tailWord_1682030) baseStart_1682030 baseEnd_1682030 := by
    simpa [prefixWord, tailWord_1682030, baseEnd_1682030] using wordTrace_append hprefix tailTrace_1682030
  have hstable : (prefixWord ++ tailWord_1682030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682030).length < 2 ^ (prefixWord ++ tailWord_1682030).sum := by decide
  have hdescent : baseEnd_1682030 < baseStart_1682030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682093 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1682093 : Nat := 118140960795 + 1682093 * 2 ^ 59
def prefixEnd_1682093 : Nat := 4983230072969 + 3 ^ 40 * 1682093 * 2
def baseEnd_1682093 : Nat := 863722214563392537101701

theorem tailTrace_1682093 : CollatzResearch.WordTrace tailWord_1682093 prefixEnd_1682093 863722214563392537101701 := by
  unfold tailWord_1682093
  simp only [CollatzResearch.WordTrace]
  refine ⟨61350971895071814458090933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40900647930047876305393955 61350971895071814458090933)
  ·
    refine ⟨5751653615162982605446025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61350971895071814458090933 5751653615162982605446025)
    ·
      refine ⟨4313740211372236954084519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5751653615162982605446025 4313740211372236954084519)
      ·
        refine ⟨6470610317058355431126779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4313740211372236954084519 6470610317058355431126779)
        ·
          refine ⟨9705915475587533146690169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6470610317058355431126779 9705915475587533146690169)
          ·
            refine ⟨7279436606690649860017627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9705915475587533146690169 7279436606690649860017627)
            ·
              refine ⟨10919154910035974790026441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7279436606690649860017627 10919154910035974790026441)
              ·
                refine ⟨8189366182526981092519831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10919154910035974790026441 8189366182526981092519831)
                ·
                  refine ⟨12284049273790471638779747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8189366182526981092519831 12284049273790471638779747)
                  ·
                    refine ⟨18426073910685707458169621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12284049273790471638779747 18426073910685707458169621)
                    ·
                      refine ⟨863722214563392537101701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18426073910685707458169621 863722214563392537101701)
                      ·
                        rfl

theorem cell23_1682093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1682093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682093 prefixEnd_1682093 := by exact prefixLift 1682093
  have htrace : WordTrace (prefixWord ++ tailWord_1682093) baseStart_1682093 baseEnd_1682093 := by
    simpa [prefixWord, tailWord_1682093, baseEnd_1682093] using wordTrace_append hprefix tailTrace_1682093
  have hstable : (prefixWord ++ tailWord_1682093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682093).length < 2 ^ (prefixWord ++ tailWord_1682093).sum := by decide
  have hdescent : baseEnd_1682093 < baseStart_1682093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682103 : List Nat := [1, 1, 3, 1, 6, 1, 2, 8]
def baseStart_1682103 : Nat := 118140960795 + 1682103 * 2 ^ 59
def prefixEnd_1682103 : Nat := 4983230072969 + 3 ^ 40 * 1682103 * 2
def baseEnd_1682103 : Nat := 31989901828516203628765

theorem tailTrace_1682103 : CollatzResearch.WordTrace tailWord_1682103 prefixEnd_1682103 31989901828516203628765 := by
  unfold tailWord_1682103
  simp only [CollatzResearch.WordTrace]
  refine ⟨61351336625035586165954963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40900891083357057443969975 61351336625035586165954963)
  ·
    refine ⟨92027004937553379248932445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61351336625035586165954963 92027004937553379248932445)
    ·
      refine ⟨34510126851582517218349667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92027004937553379248932445 34510126851582517218349667)
      ·
        refine ⟨51765190277373775827524501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34510126851582517218349667 51765190277373775827524501)
        ·
          refine ⟨2426493294251895741915211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51765190277373775827524501 2426493294251895741915211)
          ·
            refine ⟨3639739941377843612872817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426493294251895741915211 3639739941377843612872817)
            ·
              refine ⟨2729804956033382709654613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3639739941377843612872817 2729804956033382709654613)
              ·
                refine ⟨31989901828516203628765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2729804956033382709654613 31989901828516203628765)
                ·
                  rfl

theorem cell23_1682103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 8].length) (baseStart_1682103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682103 prefixEnd_1682103 := by exact prefixLift 1682103
  have htrace : WordTrace (prefixWord ++ tailWord_1682103) baseStart_1682103 baseEnd_1682103 := by
    simpa [prefixWord, tailWord_1682103, baseEnd_1682103] using wordTrace_append hprefix tailTrace_1682103
  have hstable : (prefixWord ++ tailWord_1682103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682103).length < 2 ^ (prefixWord ++ tailWord_1682103).sum := by decide
  have hdescent : baseEnd_1682103 < baseStart_1682103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682106 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_1682106 : Nat := 118140960795 + 1682106 * 2 ^ 59
def prefixEnd_1682106 : Nat := 4983230072969 + 3 ^ 40 * 1682106 * 2
def baseEnd_1682106 : Nat := 863728889811900986239141

theorem tailTrace_1682106 : CollatzResearch.WordTrace tailWord_1682106 prefixEnd_1682106 863728889811900986239141 := by
  unfold tailWord_1682106
  simp only [CollatzResearch.WordTrace]
  refine ⟨15337861511006179419578543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40900964029349811785542781 15337861511006179419578543)
  ·
    refine ⟨23006792266509269129367815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15337861511006179419578543 23006792266509269129367815)
    ·
      refine ⟨34510188399763903694051723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23006792266509269129367815 34510188399763903694051723)
      ·
        refine ⟨51765282599645855541077585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34510188399763903694051723 51765282599645855541077585)
        ·
          refine ⟨38823961949734391655808189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51765282599645855541077585 38823961949734391655808189)
          ·
            refine ⟨14558985731150396870928071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38823961949734391655808189 14558985731150396870928071)
            ·
              refine ⟨21838478596725595306392107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14558985731150396870928071 21838478596725595306392107)
              ·
                refine ⟨32757717895088392959588161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21838478596725595306392107 32757717895088392959588161)
                ·
                  refine ⟨24568288421316294719691121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32757717895088392959588161 24568288421316294719691121)
                  ·
                    refine ⟨18426216315987221039768341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24568288421316294719691121 18426216315987221039768341)
                    ·
                      refine ⟨863728889811900986239141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18426216315987221039768341 863728889811900986239141)
                      ·
                        rfl

theorem cell23_1682106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_1682106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682106 prefixEnd_1682106 := by exact prefixLift 1682106
  have htrace : WordTrace (prefixWord ++ tailWord_1682106) baseStart_1682106 baseEnd_1682106 := by
    simpa [prefixWord, tailWord_1682106, baseEnd_1682106] using wordTrace_append hprefix tailTrace_1682106
  have hstable : (prefixWord ++ tailWord_1682106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682106).length < 2 ^ (prefixWord ++ tailWord_1682106).sum := by decide
  have hdescent : baseEnd_1682106 < baseStart_1682106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682147 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1682147 : Nat := 118140960795 + 1682147 * 2 ^ 59
def prefixEnd_1682147 : Nat := 4983230072969 + 3 ^ 40 * 1682147 * 2
def baseEnd_1682147 : Nat := 863749942518735325826453

theorem tailTrace_1682147 : CollatzResearch.WordTrace tailWord_1682147 prefixEnd_1682147 863749942518735325826453 := by
  unfold tailWord_1682147
  simp only [CollatzResearch.WordTrace]
  refine ⟨61352941436876181680556695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40901960957917454453704463 61352941436876181680556695)
  ·
    refine ⟨92029412155314272520835043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61352941436876181680556695 92029412155314272520835043)
    ·
      refine ⟨138044118232971408781252565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92029412155314272520835043 138044118232971408781252565)
      ·
        refine ⟨3235409021085267393310607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 138044118232971408781252565 3235409021085267393310607)
        ·
          refine ⟨4853113531627901089965911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235409021085267393310607 4853113531627901089965911)
          ·
            refine ⟨7279670297441851634948867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853113531627901089965911 7279670297441851634948867)
            ·
              refine ⟨10919505446162777452423301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7279670297441851634948867 10919505446162777452423301)
              ·
                refine ⟨2047407271155520772329369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10919505446162777452423301 2047407271155520772329369)
                ·
                  refine ⟨1535555453366640579247027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2047407271155520772329369 1535555453366640579247027)
                  ·
                    refine ⟨2303333180049960868870541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1535555453366640579247027 2303333180049960868870541)
                    ·
                      refine ⟨863749942518735325826453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2303333180049960868870541 863749942518735325826453)
                      ·
                        rfl

theorem cell23_1682147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1682147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682147 prefixEnd_1682147 := by exact prefixLift 1682147
  have htrace : WordTrace (prefixWord ++ tailWord_1682147) baseStart_1682147 baseEnd_1682147 := by
    simpa [prefixWord, tailWord_1682147, baseEnd_1682147] using wordTrace_append hprefix tailTrace_1682147
  have hstable : (prefixWord ++ tailWord_1682147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682147).length < 2 ^ (prefixWord ++ tailWord_1682147).sum := by decide
  have hdescent : baseEnd_1682147 < baseStart_1682147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682170 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2]
def baseStart_1682170 : Nat := 118140960795 + 1682170 * 2 ^ 59
def prefixEnd_1682170 : Nat := 4983230072969 + 3 ^ 40 * 1682170 * 2
def baseEnd_1682170 : Nat := 863761752573788735838847

theorem tailTrace_1682170 : CollatzResearch.WordTrace tailWord_1682170 prefixEnd_1682170 863761752573788735838847 := by
  unfold tailWord_1682170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15338445078948214152160991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40902520210528571072429309 15338445078948214152160991)
  ·
    refine ⟨23007667618422321228241487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15338445078948214152160991 23007667618422321228241487)
    ·
      refine ⟨34511501427633481842362231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23007667618422321228241487 34511501427633481842362231)
      ·
        refine ⟨51767252141450222763543347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34511501427633481842362231 51767252141450222763543347)
        ·
          refine ⟨77650878212175334145315021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51767252141450222763543347 77650878212175334145315021)
          ·
            refine ⟨29119079329565750304493133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77650878212175334145315021 29119079329565750304493133)
            ·
              refine ⟨10919654748587156364184925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29119079329565750304493133 10919654748587156364184925)
              ·
                refine ⟨4094870530720183636569347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10919654748587156364184925 4094870530720183636569347)
                ·
                  refine ⟨6142305796080275454854021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094870530720183636569347 6142305796080275454854021)
                  ·
                    refine ⟨1151682336765051647785129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6142305796080275454854021 1151682336765051647785129)
                    ·
                      refine ⟨863761752573788735838847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1151682336765051647785129 863761752573788735838847)
                      ·
                        rfl

theorem cell23_1682170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_1682170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682170 prefixEnd_1682170 := by exact prefixLift 1682170
  have htrace : WordTrace (prefixWord ++ tailWord_1682170) baseStart_1682170 baseEnd_1682170 := by
    simpa [prefixWord, tailWord_1682170, baseEnd_1682170] using wordTrace_append hprefix tailTrace_1682170
  have hstable : (prefixWord ++ tailWord_1682170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682170).length < 2 ^ (prefixWord ++ tailWord_1682170).sum := by decide
  have hdescent : baseEnd_1682170 < baseStart_1682170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682173 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_1682173 : Nat := 118140960795 + 1682173 * 2 ^ 59
def prefixEnd_1682173 : Nat := 4983230072969 + 3 ^ 40 * 1682173 * 2
def baseEnd_1682173 : Nat := 863763293015752224101333

theorem tailTrace_1682173 : CollatzResearch.WordTrace tailWord_1682173 prefixEnd_1682173 863763293015752224101333 := by
  unfold tailWord_1682173
  simp only [CollatzResearch.WordTrace]
  refine ⟨61353889734781988121003173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40902593156521325414002115 61353889734781988121003173)
  ·
    refine ⟨11503854325271622772688095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61353889734781988121003173 11503854325271622772688095)
    ·
      refine ⟨17255781487907434159032143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11503854325271622772688095 17255781487907434159032143)
      ·
        refine ⟨25883672231861151238548215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17255781487907434159032143 25883672231861151238548215)
        ·
          refine ⟨38825508347791726857822323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25883672231861151238548215 38825508347791726857822323)
          ·
            refine ⟨58238262521687590286733485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38825508347791726857822323 58238262521687590286733485)
            ·
              refine ⟨21839348445632846357525057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58238262521687590286733485 21839348445632846357525057)
              ·
                refine ⟨16379511334224634768143793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21839348445632846357525057 16379511334224634768143793)
                ·
                  refine ⟨12284633500668476076107845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16379511334224634768143793 12284633500668476076107845)
                  ·
                    refine ⟨2303368781375339264270221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12284633500668476076107845 2303368781375339264270221)
                    ·
                      refine ⟨863763293015752224101333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2303368781375339264270221 863763293015752224101333)
                      ·
                        rfl

theorem cell23_1682173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_1682173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682173 prefixEnd_1682173 := by exact prefixLift 1682173
  have htrace : WordTrace (prefixWord ++ tailWord_1682173) baseStart_1682173 baseEnd_1682173 := by
    simpa [prefixWord, tailWord_1682173, baseEnd_1682173] using wordTrace_append hprefix tailTrace_1682173
  have hstable : (prefixWord ++ tailWord_1682173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682173).length < 2 ^ (prefixWord ++ tailWord_1682173).sum := by decide
  have hdescent : baseEnd_1682173 < baseStart_1682173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682204 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_1682204 : Nat := 118140960795 + 1682204 * 2 ^ 59
def prefixEnd_1682204 : Nat := 4983230072969 + 3 ^ 40 * 1682204 * 2
def baseEnd_1682204 : Nat := 863779210916041602813691

theorem tailTrace_1682204 : CollatzResearch.WordTrace tailWord_1682204 prefixEnd_1682204 863779210916041602813691 := by
  unfold tailWord_1682204
  simp only [CollatzResearch.WordTrace]
  refine ⟨30677510198834840207690833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40903346931779786943587777 30677510198834840207690833)
  ·
    refine ⟨23008132649126130155768125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30677510198834840207690833 23008132649126130155768125)
    ·
      refine ⟨8628049743422298808413047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23008132649126130155768125 8628049743422298808413047)
      ·
        refine ⟨12942074615133448212619571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8628049743422298808413047 12942074615133448212619571)
        ·
          refine ⟨19413111922700172318929357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12942074615133448212619571 19413111922700172318929357)
          ·
            refine ⟨7279916971012564619598509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19413111922700172318929357 7279916971012564619598509)
            ·
              refine ⟨2729968864129711732349441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7279916971012564619598509 2729968864129711732349441)
              ·
                refine ⟨2047476648097283799262081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2729968864129711732349441 2047476648097283799262081)
                ·
                  refine ⟨1535607486072962849446561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2047476648097283799262081 1535607486072962849446561)
                  ·
                    refine ⟨1151705614554722137084921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1535607486072962849446561 1151705614554722137084921)
                    ·
                      refine ⟨863779210916041602813691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1151705614554722137084921 863779210916041602813691)
                      ·
                        rfl

theorem cell23_1682204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_1682204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682204 prefixEnd_1682204 := by exact prefixLift 1682204
  have htrace : WordTrace (prefixWord ++ tailWord_1682204) baseStart_1682204 baseEnd_1682204 := by
    simpa [prefixWord, tailWord_1682204, baseEnd_1682204] using wordTrace_append hprefix tailTrace_1682204
  have hstable : (prefixWord ++ tailWord_1682204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682204).length < 2 ^ (prefixWord ++ tailWord_1682204).sum := by decide
  have hdescent : baseEnd_1682204 < baseStart_1682204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682210 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 7]
def baseStart_1682210 : Nat := 118140960795 + 1682210 * 2 ^ 59
def prefixEnd_1682210 : Nat := 4983230072969 + 3 ^ 40 * 1682210 * 2
def baseEnd_1682210 : Nat := 95975810199996508815407

theorem tailTrace_1682210 : CollatzResearch.WordTrace tailWord_1682210 prefixEnd_1682210 95975810199996508815407 := by
  unfold tailWord_1682210
  simp only [CollatzResearch.WordTrace]
  refine ⟨15338809808911985860025021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40903492823765295626733389 15338809808911985860025021)
  ·
    refine ⟨5752053678341994697509383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15338809808911985860025021 5752053678341994697509383)
    ·
      refine ⟨8628080517512992046264075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5752053678341994697509383 8628080517512992046264075)
      ·
        refine ⟨12942120776269488069396113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8628080517512992046264075 12942120776269488069396113)
        ·
          refine ⟨9706590582202116052047085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12942120776269488069396113 9706590582202116052047085)
          ·
            refine ⟨3639971468325793519517657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9706590582202116052047085 3639971468325793519517657)
            ·
              refine ⟨2729978601244345139638243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3639971468325793519517657 2729978601244345139638243)
              ·
                refine ⟨4094967901866517709457365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2729978601244345139638243 4094967901866517709457365)
                ·
                  refine ⟨95975810199996508815407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4094967901866517709457365 95975810199996508815407)
                  ·
                    rfl

theorem cell23_1682210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_1682210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682210 prefixEnd_1682210 := by exact prefixLift 1682210
  have htrace : WordTrace (prefixWord ++ tailWord_1682210) baseStart_1682210 baseEnd_1682210 := by
    simpa [prefixWord, tailWord_1682210, baseEnd_1682210] using wordTrace_append hprefix tailTrace_1682210
  have hstable : (prefixWord ++ tailWord_1682210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682210).length < 2 ^ (prefixWord ++ tailWord_1682210).sum := by decide
  have hdescent : baseEnd_1682210 < baseStart_1682210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682243 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 4]
def baseStart_1682243 : Nat := 118140960795 + 1682243 * 2 ^ 59
def prefixEnd_1682243 : Nat := 4983230072969 + 3 ^ 40 * 1682243 * 2
def baseEnd_1682243 : Nat := 863799236661566950226011

theorem tailTrace_1682243 : CollatzResearch.WordTrace tailWord_1682243 prefixEnd_1682243 863799236661566950226011 := by
  unfold tailWord_1682243
  simp only [CollatzResearch.WordTrace]
  refine ⟨61356442844528390076051383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40904295229685593384034255 61356442844528390076051383)
  ·
    refine ⟨92034664266792585114077075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61356442844528390076051383 92034664266792585114077075)
    ·
      refine ⟨138051996400188877671115613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92034664266792585114077075 138051996400188877671115613)
      ·
        refine ⟨51769498650070829126668355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138051996400188877671115613 51769498650070829126668355)
        ·
          refine ⟨77654247975106243690002533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51769498650070829126668355 77654247975106243690002533)
          ·
            refine ⟨14560171495332420691875475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77654247975106243690002533 14560171495332420691875475)
            ·
              refine ⟨21840257242998631037813213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14560171495332420691875475 21840257242998631037813213)
              ·
                refine ⟨8190096466124486639179955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21840257242998631037813213 8190096466124486639179955)
                ·
                  refine ⟨12285144699186729958769933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8190096466124486639179955 12285144699186729958769933)
                  ·
                    refine ⟨4606929262195023734538725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12285144699186729958769933 4606929262195023734538725)
                    ·
                      refine ⟨863799236661566950226011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4606929262195023734538725 863799236661566950226011)
                      ·
                        rfl

theorem cell23_1682243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_1682243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682243 prefixEnd_1682243 := by exact prefixLift 1682243
  have htrace : WordTrace (prefixWord ++ tailWord_1682243) baseStart_1682243 baseEnd_1682243 := by
    simpa [prefixWord, tailWord_1682243, baseEnd_1682243] using wordTrace_append hprefix tailTrace_1682243
  have hstable : (prefixWord ++ tailWord_1682243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682243).length < 2 ^ (prefixWord ++ tailWord_1682243).sum := by decide
  have hdescent : baseEnd_1682243 < baseStart_1682243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682273 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_1682273 : Nat := 118140960795 + 1682273 * 2 ^ 59
def prefixEnd_1682273 : Nat := 4983230072969 + 3 ^ 40 * 1682273 * 2
def baseEnd_1682273 : Nat := 863814641081201832850873

theorem tailTrace_1682273 : CollatzResearch.WordTrace tailWord_1682273 prefixEnd_1682273 863814641081201832850873 := by
  unfold tailWord_1682273
  simp only [CollatzResearch.WordTrace]
  refine ⟨61357537034419705199643473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40905024689613136799762315 61357537034419705199643473)
  ·
    refine ⟨46018152775814778899732605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61357537034419705199643473 46018152775814778899732605)
    ·
      refine ⟨17256807290930542087399727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46018152775814778899732605 17256807290930542087399727)
      ·
        refine ⟨25885210936395813131099591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17256807290930542087399727 25885210936395813131099591)
        ·
          refine ⟨38827816404593719696649387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25885210936395813131099591 38827816404593719696649387)
          ·
            refine ⟨58241724606890579544974081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38827816404593719696649387 58241724606890579544974081)
            ·
              refine ⟨43681293455167934658730561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58241724606890579544974081 43681293455167934658730561)
              ·
                refine ⟨32760970091375950994047921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43681293455167934658730561 32760970091375950994047921)
                ·
                  refine ⟨24570727568531963245535941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32760970091375950994047921 24570727568531963245535941)
                  ·
                    refine ⟨4607011419099743108537989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24570727568531963245535941 4607011419099743108537989)
                    ·
                      refine ⟨863814641081201832850873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4607011419099743108537989 863814641081201832850873)
                      ·
                        rfl

theorem cell23_1682273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_1682273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682273 prefixEnd_1682273 := by exact prefixLift 1682273
  have htrace : WordTrace (prefixWord ++ tailWord_1682273) baseStart_1682273 baseEnd_1682273 := by
    simpa [prefixWord, tailWord_1682273, baseEnd_1682273] using wordTrace_append hprefix tailTrace_1682273
  have hstable : (prefixWord ++ tailWord_1682273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682273).length < 2 ^ (prefixWord ++ tailWord_1682273).sum := by decide
  have hdescent : baseEnd_1682273 < baseStart_1682273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682294 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1682294 : Nat := 118140960795 + 1682294 * 2 ^ 59
def prefixEnd_1682294 : Nat := 4983230072969 + 3 ^ 40 * 1682294 * 2
def baseEnd_1682294 : Nat := 863825424174946250688277

theorem tailTrace_1682294 : CollatzResearch.WordTrace tailWord_1682294 prefixEnd_1682294 863825424174946250688277 := by
  unfold tailWord_1682294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3834893935458976611634871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40905535311562417190771957 3834893935458976611634871)
  ·
    refine ⟨5752340903188464917452307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3834893935458976611634871 5752340903188464917452307)
    ·
      refine ⟨8628511354782697376178461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5752340903188464917452307 8628511354782697376178461)
      ·
        refine ⟨3235691758043511516066923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8628511354782697376178461 3235691758043511516066923)
        ·
          refine ⟨4853537637065267274100385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235691758043511516066923 4853537637065267274100385)
          ·
            refine ⟨3640153227798950455575289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4853537637065267274100385 3640153227798950455575289)
            ·
              refine ⟨2730114920849212841681467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3640153227798950455575289 2730114920849212841681467)
              ·
                refine ⟨4095172381273819262522201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730114920849212841681467 4095172381273819262522201)
                ·
                  refine ⟨3071379285955364446891651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4095172381273819262522201 3071379285955364446891651)
                  ·
                    refine ⟨4607068928933046670337477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3071379285955364446891651 4607068928933046670337477)
                    ·
                      refine ⟨863825424174946250688277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4607068928933046670337477 863825424174946250688277)
                      ·
                        rfl

theorem cell23_1682294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1682294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682294 prefixEnd_1682294 := by exact prefixLift 1682294
  have htrace : WordTrace (prefixWord ++ tailWord_1682294) baseStart_1682294 baseEnd_1682294 := by
    simpa [prefixWord, tailWord_1682294, baseEnd_1682294] using wordTrace_append hprefix tailTrace_1682294
  have hstable : (prefixWord ++ tailWord_1682294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682294).length < 2 ^ (prefixWord ++ tailWord_1682294).sum := by decide
  have hdescent : baseEnd_1682294 < baseStart_1682294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682297 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 2, 2, 3]
def baseStart_1682297 : Nat := 118140960795 + 1682297 * 2 ^ 59
def prefixEnd_1682297 : Nat := 4983230072969 + 3 ^ 40 * 1682297 * 2
def baseEnd_1682297 : Nat := 863826964616909738950763

theorem tailTrace_1682297 : CollatzResearch.WordTrace tailWord_1682297 prefixEnd_1682297 863826964616909738950763 := by
  unfold tailWord_1682297
  simp only [CollatzResearch.WordTrace]
  refine ⟨61358412386332757298517145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40905608257555171532344763 61358412386332757298517145)
  ·
    refine ⟨46018809289749567973887859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61358412386332757298517145 46018809289749567973887859)
    ·
      refine ⟨69028213934624351960831789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46018809289749567973887859 69028213934624351960831789)
      ·
        refine ⟨25885580225484131985311921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69028213934624351960831789 25885580225484131985311921)
        ·
          refine ⟨19414185169113098988983941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25885580225484131985311921 19414185169113098988983941)
          ·
            refine ⟨3640159719208706060434489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19414185169113098988983941 3640159719208706060434489)
            ·
              refine ⟨2730119789406529545325867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3640159719208706060434489 2730119789406529545325867)
              ·
                refine ⟨4095179684109794317988801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730119789406529545325867 4095179684109794317988801)
                ·
                  refine ⟨3071384763082345738491601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4095179684109794317988801 3071384763082345738491601)
                  ·
                    refine ⟨2303538572311759303868701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3071384763082345738491601 2303538572311759303868701)
                    ·
                      refine ⟨863826964616909738950763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2303538572311759303868701 863826964616909738950763)
                      ·
                        rfl

theorem cell23_1682297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_1682297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682297 prefixEnd_1682297 := by exact prefixLift 1682297
  have htrace : WordTrace (prefixWord ++ tailWord_1682297) baseStart_1682297 baseEnd_1682297 := by
    simpa [prefixWord, tailWord_1682297, baseEnd_1682297] using wordTrace_append hprefix tailTrace_1682297
  have hstable : (prefixWord ++ tailWord_1682297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682297).length < 2 ^ (prefixWord ++ tailWord_1682297).sum := by decide
  have hdescent : baseEnd_1682297 < baseStart_1682297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682327 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 3, 1, 3]
def baseStart_1682327 : Nat := 118140960795 + 1682327 * 2 ^ 59
def prefixEnd_1682327 : Nat := 4983230072969 + 3 ^ 40 * 1682327 * 2
def baseEnd_1682327 : Nat := 863842369036544621575625

theorem tailTrace_1682327 : CollatzResearch.WordTrace tailWord_1682327 prefixEnd_1682327 863842369036544621575625 := by
  unfold tailWord_1682327
  simp only [CollatzResearch.WordTrace]
  refine ⟨61359506576224072422109235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40906337717482714948072823 61359506576224072422109235)
  ·
    refine ⟨92039259864336108633163853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61359506576224072422109235 92039259864336108633163853)
    ·
      refine ⟨34514722449126040737436445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92039259864336108633163853 34514722449126040737436445)
      ·
        refine ⟨12943020918422265276538667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34514722449126040737436445 12943020918422265276538667)
        ·
          refine ⟨19414531377633397914808001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12943020918422265276538667 19414531377633397914808001)
          ·
            refine ⟨14560898533225048436106001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19414531377633397914808001 14560898533225048436106001)
            ·
              refine ⟨10920673899918786327079501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14560898533225048436106001 10920673899918786327079501)
              ·
                refine ⟨4095252712469544872654813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10920673899918786327079501 4095252712469544872654813)
                ·
                  refine ⟨1535719767176079327245555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4095252712469544872654813 1535719767176079327245555)
                  ·
                    refine ⟨2303579650764118990868333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1535719767176079327245555 2303579650764118990868333)
                    ·
                      refine ⟨863842369036544621575625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2303579650764118990868333 863842369036544621575625)
                      ·
                        rfl

theorem cell23_1682327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_1682327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682327 prefixEnd_1682327 := by exact prefixLift 1682327
  have htrace : WordTrace (prefixWord ++ tailWord_1682327) baseStart_1682327 baseEnd_1682327 := by
    simpa [prefixWord, tailWord_1682327, baseEnd_1682327] using wordTrace_append hprefix tailTrace_1682327
  have hstable : (prefixWord ++ tailWord_1682327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682327).length < 2 ^ (prefixWord ++ tailWord_1682327).sum := by decide
  have hdescent : baseEnd_1682327 < baseStart_1682327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682360 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 1, 6]
def baseStart_1682360 : Nat := 118140960795 + 1682360 * 2 ^ 59
def prefixEnd_1682360 : Nat := 4983230072969 + 3 ^ 40 * 1682360 * 2
def baseEnd_1682360 : Nat := 287953104632714330820991

theorem tailTrace_1682360 : CollatzResearch.WordTrace tailWord_1682360 prefixEnd_1682360 287953104632714330820991 := by
  unfold tailWord_1682360
  simp only [CollatzResearch.WordTrace]
  refine ⟨30680355092552259529030267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40907140123403012705373689 30680355092552259529030267)
  ·
    refine ⟨46020532638828389293545401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30680355092552259529030267 46020532638828389293545401)
    ·
      refine ⟨34515399479121291970159051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46020532638828389293545401 34515399479121291970159051)
      ·
        refine ⟨51773099218681937955238577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34515399479121291970159051 51773099218681937955238577)
        ·
          refine ⟨38829824414011453466428933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51773099218681937955238577 38829824414011453466428933)
          ·
            refine ⟨7280592077627147524955425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38829824414011453466428933 7280592077627147524955425)
            ·
              refine ⟨5460444058220360643716569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7280592077627147524955425 5460444058220360643716569)
              ·
                refine ⟨4095333043665270482787427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5460444058220360643716569 4095333043665270482787427)
                ·
                  refine ⟨6142999565497905724181141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4095333043665270482787427 6142999565497905724181141)
                  ·
                    refine ⟨287953104632714330820991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6142999565497905724181141 287953104632714330820991)
                    ·
                      rfl

theorem cell23_1682360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_1682360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682360 prefixEnd_1682360 := by exact prefixLift 1682360
  have htrace : WordTrace (prefixWord ++ tailWord_1682360) baseStart_1682360 baseEnd_1682360 := by
    simpa [prefixWord, tailWord_1682360, baseEnd_1682360] using wordTrace_append hprefix tailTrace_1682360
  have hstable : (prefixWord ++ tailWord_1682360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682360).length < 2 ^ (prefixWord ++ tailWord_1682360).sum := by decide
  have hdescent : baseEnd_1682360 < baseStart_1682360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682361 : List Nat := [1, 2, 1, 4, 2, 3, 2, 3, 1, 1, 3]
def baseStart_1682361 : Nat := 118140960795 + 1682361 * 2 ^ 59
def prefixEnd_1682361 : Nat := 4983230072969 + 3 ^ 40 * 1682361 * 2
def baseEnd_1682361 : Nat := 863859827378797488550469

theorem tailTrace_1682361 : CollatzResearch.WordTrace tailWord_1682361 prefixEnd_1682361 863859827378797488550469 := by
  unfold tailWord_1682361
  simp only [CollatzResearch.WordTrace]
  refine ⟨61360746658100896228846937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40907164438733930819231291 61360746658100896228846937)
  ·
    refine ⟨46020559993575672171635203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61360746658100896228846937 46020559993575672171635203)
    ·
      refine ⟨69030839990363508257452805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46020559993575672171635203 69030839990363508257452805)
      ·
        refine ⟨12943282498193157798272401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69030839990363508257452805 12943282498193157798272401)
        ·
          refine ⟨9707461873644868348704301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12943282498193157798272401 9707461873644868348704301)
          ·
            refine ⟨3640298202616825630764113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9707461873644868348704301 3640298202616825630764113)
            ·
              refine ⟨2730223651962619223073085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3640298202616825630764113 2730223651962619223073085)
              ·
                refine ⟨1023833869485982208652407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2730223651962619223073085 1023833869485982208652407)
                ·
                  refine ⟨1535750804228973312978611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023833869485982208652407 1535750804228973312978611)
                  ·
                    refine ⟨2303626206343459969467917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1535750804228973312978611 2303626206343459969467917)
                    ·
                      refine ⟨863859827378797488550469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2303626206343459969467917 863859827378797488550469)
                      ·
                        rfl

theorem cell23_1682361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_1682361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682361 prefixEnd_1682361 := by exact prefixLift 1682361
  have htrace : WordTrace (prefixWord ++ tailWord_1682361) baseStart_1682361 baseEnd_1682361 := by
    simpa [prefixWord, tailWord_1682361, baseEnd_1682361] using wordTrace_append hprefix tailTrace_1682361
  have hstable : (prefixWord ++ tailWord_1682361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682361).length < 2 ^ (prefixWord ++ tailWord_1682361).sum := by decide
  have hdescent : baseEnd_1682361 < baseStart_1682361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682380 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1682380 : Nat := 118140960795 + 1682380 * 2 ^ 59
def prefixEnd_1682380 : Nat := 4983230072969 + 3 ^ 40 * 1682380 * 2
def baseEnd_1682380 : Nat := 863869583511232914212881

theorem tailTrace_1682380 : CollatzResearch.WordTrace tailWord_1682380 prefixEnd_1682380 863869583511232914212881 := by
  unfold tailWord_1682380
  simp only [CollatzResearch.WordTrace]
  refine ⟨30680719822516031236894297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40907626430021374982525729 30680719822516031236894297)
  ·
    refine ⟨23010539866887023427670723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30680719822516031236894297 23010539866887023427670723)
    ·
      refine ⟨34515809800330535141506085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23010539866887023427670723 34515809800330535141506085)
      ·
        refine ⟨6471714337561975339032391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34515809800330535141506085 6471714337561975339032391)
        ·
          refine ⟨9707571506342963008548587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6471714337561975339032391 9707571506342963008548587)
          ·
            refine ⟨14561357259514444512822881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9707571506342963008548587 14561357259514444512822881)
            ·
              refine ⟨10921017944635833384617161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14561357259514444512822881 10921017944635833384617161)
              ·
                refine ⟨8190763458476875038462871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10921017944635833384617161 8190763458476875038462871)
                ·
                  refine ⟨12286145187715312557694307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8190763458476875038462871 12286145187715312557694307)
                  ·
                    refine ⟨18429217781572968836541461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12286145187715312557694307 18429217781572968836541461)
                    ·
                      refine ⟨863869583511232914212881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18429217781572968836541461 863869583511232914212881)
                      ·
                        rfl

theorem cell23_1682380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1682380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682380 prefixEnd_1682380 := by exact prefixLift 1682380
  have htrace : WordTrace (prefixWord ++ tailWord_1682380) baseStart_1682380 baseEnd_1682380 := by
    simpa [prefixWord, tailWord_1682380, baseEnd_1682380] using wordTrace_append hprefix tailTrace_1682380
  have hstable : (prefixWord ++ tailWord_1682380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682380).length < 2 ^ (prefixWord ++ tailWord_1682380).sum := by decide
  have hdescent : baseEnd_1682380 < baseStart_1682380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682397 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1682397 : Nat := 118140960795 + 1682397 * 2 ^ 59
def prefixEnd_1682397 : Nat := 4983230072969 + 3 ^ 40 * 1682397 * 2
def baseEnd_1682397 : Nat := 863878312682359347700303

theorem tailTrace_1682397 : CollatzResearch.WordTrace tailWord_1682397 prefixEnd_1682397 863878312682359347700303 := by
  unfold tailWord_1682397
  simp only [CollatzResearch.WordTrace]
  refine ⟨61362059685970474377157445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40908039790646982918104963 61362059685970474377157445)
  ·
    refine ⟨11505386191119463945717021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61362059685970474377157445 11505386191119463945717021)
    ·
      refine ⟨4314519821669798979643883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11505386191119463945717021 4314519821669798979643883)
      ·
        refine ⟨6471779732504698469465825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4314519821669798979643883 6471779732504698469465825)
        ·
          refine ⟨4853834799378523852099369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6471779732504698469465825 4853834799378523852099369)
          ·
            refine ⟨3640376099533892889074527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4853834799378523852099369 3640376099533892889074527)
            ·
              refine ⟨5460564149300839333611791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640376099533892889074527 5460564149300839333611791)
              ·
                refine ⟨8190846223951259000417687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5460564149300839333611791 8190846223951259000417687)
                ·
                  refine ⟨12286269335926888500626531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8190846223951259000417687 12286269335926888500626531)
                  ·
                    refine ⟨18429404003890332750939797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12286269335926888500626531 18429404003890332750939797)
                    ·
                      refine ⟨863878312682359347700303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18429404003890332750939797 863878312682359347700303)
                      ·
                        rfl

theorem cell23_1682397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1682397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682397 prefixEnd_1682397 := by exact prefixLift 1682397
  have htrace : WordTrace (prefixWord ++ tailWord_1682397) baseStart_1682397 baseEnd_1682397 := by
    simpa [prefixWord, tailWord_1682397, baseEnd_1682397] using wordTrace_append hprefix tailTrace_1682397
  have hstable : (prefixWord ++ tailWord_1682397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682397).length < 2 ^ (prefixWord ++ tailWord_1682397).sum := by decide
  have hdescent : baseEnd_1682397 < baseStart_1682397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682407 : List Nat := [1, 1, 5, 2, 2, 1, 4, 7]
def baseStart_1682407 : Nat := 118140960795 + 1682407 * 2 ^ 59
def prefixEnd_1682407 : Nat := 4983230072969 + 3 ^ 40 * 1682407 * 2
def baseEnd_1682407 : Nat := 31995683240329789206491

theorem tailTrace_1682407 : CollatzResearch.WordTrace tailWord_1682407 prefixEnd_1682407 31995683240329789206491 := by
  unfold tailWord_1682407
  simp only [CollatzResearch.WordTrace]
  refine ⟨61362424415934246085021475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40908282943956164056680983 61362424415934246085021475)
  ·
    refine ⟨92043636623901369127532213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61362424415934246085021475 92043636623901369127532213)
    ·
      refine ⟨8629090933490753355706145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92043636623901369127532213 8629090933490753355706145)
      ·
        refine ⟨6471818200118065016779609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8629090933490753355706145 6471818200118065016779609)
        ·
          refine ⟨4853863650088548762584707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6471818200118065016779609 4853863650088548762584707)
          ·
            refine ⟨7280795475132823143877061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853863650088548762584707 7280795475132823143877061)
            ·
              refine ⟨1365149151587404339476949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7280795475132823143877061 1365149151587404339476949)
              ·
                refine ⟨31995683240329789206491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1365149151587404339476949 31995683240329789206491)
                ·
                  rfl

theorem cell23_1682407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 7].length) (baseStart_1682407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682407 prefixEnd_1682407 := by exact prefixLift 1682407
  have htrace : WordTrace (prefixWord ++ tailWord_1682407) baseStart_1682407 baseEnd_1682407 := by
    simpa [prefixWord, tailWord_1682407, baseEnd_1682407] using wordTrace_append hprefix tailTrace_1682407
  have hstable : (prefixWord ++ tailWord_1682407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682407).length < 2 ^ (prefixWord ++ tailWord_1682407).sum := by decide
  have hdescent : baseEnd_1682407 < baseStart_1682407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682421 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1682421 : Nat := 118140960795 + 1682421 * 2 ^ 59
def prefixEnd_1682421 : Nat := 4983230072969 + 3 ^ 40 * 1682421 * 2
def baseEnd_1682421 : Nat := 863890636218067253800193

theorem tailTrace_1682421 : CollatzResearch.WordTrace tailWord_1682421 prefixEnd_1682421 863890636218067253800193 := by
  unfold tailWord_1682421
  simp only [CollatzResearch.WordTrace]
  refine ⟨61362935037883526476031117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40908623358589017650687411 61362935037883526476031117)
  ·
    refine ⟨23011100639206322428511669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61362935037883526476031117 23011100639206322428511669)
    ·
      refine ⟨2157290684925592727672969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23011100639206322428511669 2157290684925592727672969)
      ·
        refine ⟨1617968013694194545754727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2157290684925592727672969 1617968013694194545754727)
        ·
          refine ⟨2426952020541291818632091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617968013694194545754727 2426952020541291818632091)
          ·
            refine ⟨3640428030811937727948137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426952020541291818632091 3640428030811937727948137)
            ·
              refine ⟨2730321023108953295961103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3640428030811937727948137 2730321023108953295961103)
              ·
                refine ⟨4095481534663429943941655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730321023108953295961103 4095481534663429943941655)
                ·
                  refine ⟨6143222301995144915912483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4095481534663429943941655 6143222301995144915912483)
                  ·
                    refine ⟨9214833452992717373868725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6143222301995144915912483 9214833452992717373868725)
                    ·
                      refine ⟨863890636218067253800193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9214833452992717373868725 863890636218067253800193)
                      ·
                        rfl

theorem cell23_1682421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1682421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682421 prefixEnd_1682421 := by exact prefixLift 1682421
  have htrace : WordTrace (prefixWord ++ tailWord_1682421) baseStart_1682421 baseEnd_1682421 := by
    simpa [prefixWord, tailWord_1682421, baseEnd_1682421] using wordTrace_append hprefix tailTrace_1682421
  have hstable : (prefixWord ++ tailWord_1682421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682421).length < 2 ^ (prefixWord ++ tailWord_1682421).sum := by decide
  have hdescent : baseEnd_1682421 < baseStart_1682421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682427 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 5, 3, 2]
def baseStart_1682427 : Nat := 118140960795 + 1682427 * 2 ^ 59
def prefixEnd_1682427 : Nat := 4983230072969 + 3 ^ 40 * 1682427 * 2
def baseEnd_1682427 : Nat := 863893717101994230325165

theorem tailTrace_1682427 : CollatzResearch.WordTrace tailWord_1682427 prefixEnd_1682427 863893717101994230325165 := by
  unfold tailWord_1682427
  simp only [CollatzResearch.WordTrace]
  refine ⟨61363153875861789500749535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40908769250574526333833023 61363153875861789500749535)
  ·
    refine ⟨92044730813792684251124303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61363153875861789500749535 92044730813792684251124303)
    ·
      refine ⟨138067096220689026376686455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92044730813792684251124303 138067096220689026376686455)
      ·
        refine ⟨207100644331033539565029683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138067096220689026376686455 207100644331033539565029683)
        ·
          refine ⟨310650966496550309347544525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207100644331033539565029683 310650966496550309347544525)
          ·
            refine ⟨116494112436206366005329197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310650966496550309347544525 116494112436206366005329197)
            ·
              refine ⟨43685292163577387251998449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116494112436206366005329197 43685292163577387251998449)
              ·
                refine ⟨32763969122683040438998837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43685292163577387251998449 32763969122683040438998837)
                ·
                  refine ⟨3071622105251535041156141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32763969122683040438998837 3071622105251535041156141)
                  ·
                    refine ⟨1151858289469325640433553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3071622105251535041156141 1151858289469325640433553)
                    ·
                      refine ⟨863893717101994230325165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1151858289469325640433553 863893717101994230325165)
                      ·
                        rfl

theorem cell23_1682427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 3, 2].length) (baseStart_1682427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682427 prefixEnd_1682427 := by exact prefixLift 1682427
  have htrace : WordTrace (prefixWord ++ tailWord_1682427) baseStart_1682427 baseEnd_1682427 := by
    simpa [prefixWord, tailWord_1682427, baseEnd_1682427] using wordTrace_append hprefix tailTrace_1682427
  have hstable : (prefixWord ++ tailWord_1682427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682427).length < 2 ^ (prefixWord ++ tailWord_1682427).sum := by decide
  have hdescent : baseEnd_1682427 < baseStart_1682427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682461 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_1682461 : Nat := 118140960795 + 1682461 * 2 ^ 59
def prefixEnd_1682461 : Nat := 4983230072969 + 3 ^ 40 * 1682461 * 2
def baseEnd_1682461 : Nat := 863911175444247097300009

theorem tailTrace_1682461 : CollatzResearch.WordTrace tailWord_1682461 prefixEnd_1682461 863911175444247097300009 := by
  unfold tailWord_1682461
  simp only [CollatzResearch.WordTrace]
  refine ⟨61364393957738613307487237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40909595971825742204991491 61364393957738613307487237)
  ·
    refine ⟨11505823867075989995153857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61364393957738613307487237 11505823867075989995153857)
    ·
      refine ⟨8629367900306992496365393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11505823867075989995153857 8629367900306992496365393)
      ·
        refine ⟨6472025925230244372274045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8629367900306992496365393 6472025925230244372274045)
        ·
          refine ⟨2427009721961341639602767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6472025925230244372274045 2427009721961341639602767)
          ·
            refine ⟨3640514582942012459404151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427009721961341639602767 3640514582942012459404151)
            ·
              refine ⟨5460771874413018689106227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640514582942012459404151 5460771874413018689106227)
              ·
                refine ⟨8191157811619528033659341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5460771874413018689106227 8191157811619528033659341)
                ·
                  refine ⟨3071684179357323012622253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8191157811619528033659341 3071684179357323012622253)
                  ·
                    refine ⟨1151881567258996129733345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3071684179357323012622253 1151881567258996129733345)
                    ·
                      refine ⟨863911175444247097300009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1151881567258996129733345 863911175444247097300009)
                      ·
                        rfl

theorem cell23_1682461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_1682461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682461 prefixEnd_1682461 := by exact prefixLift 1682461
  have htrace : WordTrace (prefixWord ++ tailWord_1682461) baseStart_1682461 baseEnd_1682461 := by
    simpa [prefixWord, tailWord_1682461, baseEnd_1682461] using wordTrace_append hprefix tailTrace_1682461
  have hstable : (prefixWord ++ tailWord_1682461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682461).length < 2 ^ (prefixWord ++ tailWord_1682461).sum := by decide
  have hdescent : baseEnd_1682461 < baseStart_1682461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682478 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_1682478 : Nat := 118140960795 + 1682478 * 2 ^ 59
def prefixEnd_1682478 : Nat := 4983230072969 + 3 ^ 40 * 1682478 * 2
def baseEnd_1682478 : Nat := 863919904615373530787431

theorem tailTrace_1682478 : CollatzResearch.WordTrace tailWord_1682478 prefixEnd_1682478 863919904615373530787431 := by
  unfold tailWord_1682478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670626749834628151357011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40910009332451350140570725 7670626749834628151357011)
  ·
    refine ⟨11505940124751942227035517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7670626749834628151357011 11505940124751942227035517)
    ·
      refine ⟨4314727546781978335138319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11505940124751942227035517 4314727546781978335138319)
      ·
        refine ⟨6472091320172967502707479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4314727546781978335138319 6472091320172967502707479)
        ·
          refine ⟨9708136980259451254061219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472091320172967502707479 9708136980259451254061219)
          ·
            refine ⟨14562205470389176881091829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9708136980259451254061219 14562205470389176881091829)
            ·
              refine ⟨1365206762848985332602359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14562205470389176881091829 1365206762848985332602359)
              ·
                refine ⟨2047810144273477998903539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365206762848985332602359 2047810144273477998903539)
                ·
                  refine ⟨3071715216410216998355309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047810144273477998903539 3071715216410216998355309)
                  ·
                    refine ⟨1151893206153831374383241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3071715216410216998355309 1151893206153831374383241)
                    ·
                      refine ⟨863919904615373530787431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1151893206153831374383241 863919904615373530787431)
                      ·
                        rfl

theorem cell23_1682478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_1682478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682478 prefixEnd_1682478 := by exact prefixLift 1682478
  have htrace : WordTrace (prefixWord ++ tailWord_1682478) baseStart_1682478 baseEnd_1682478 := by
    simpa [prefixWord, tailWord_1682478, baseEnd_1682478] using wordTrace_append hprefix tailTrace_1682478
  have hstable : (prefixWord ++ tailWord_1682478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682478).length < 2 ^ (prefixWord ++ tailWord_1682478).sum := by decide
  have hdescent : baseEnd_1682478 < baseStart_1682478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682490 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_1682490 : Nat := 118140960795 + 1682490 * 2 ^ 59
def prefixEnd_1682490 : Nat := 4983230072969 + 3 ^ 40 * 1682490 * 2
def baseEnd_1682490 : Nat := 863926066383227483837375

theorem tailTrace_1682490 : CollatzResearch.WordTrace tailWord_1682490 prefixEnd_1682490 863926066383227483837375 := by
  unfold tailWord_1682490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341362918658387815073231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40910301116422367506861949 15341362918658387815073231)
  ·
    refine ⟨23012044377987581722609847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15341362918658387815073231 23012044377987581722609847)
    ·
      refine ⟨34518066566981372583914771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23012044377987581722609847 34518066566981372583914771)
      ·
        refine ⟨51777099850472058875872157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34518066566981372583914771 51777099850472058875872157)
        ·
          refine ⟨19416412443927022078452059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51777099850472058875872157 19416412443927022078452059)
          ·
            refine ⟨29124618665890533117678089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19416412443927022078452059 29124618665890533117678089)
            ·
              refine ⟨21843463999417899838258567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29124618665890533117678089 21843463999417899838258567)
              ·
                refine ⟨32765195999126849757387851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21843463999417899838258567 32765195999126849757387851)
                ·
                  refine ⟨49147793998690274636081777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32765195999126849757387851 49147793998690274636081777)
                  ·
                    refine ⟨36860845499017705977061333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49147793998690274636081777 36860845499017705977061333)
                    ·
                      refine ⟨863926066383227483837375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36860845499017705977061333 863926066383227483837375)
                      ·
                        rfl

theorem cell23_1682490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_1682490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682490 prefixEnd_1682490 := by exact prefixLift 1682490
  have htrace : WordTrace (prefixWord ++ tailWord_1682490) baseStart_1682490 baseEnd_1682490 := by
    simpa [prefixWord, tailWord_1682490, baseEnd_1682490] using wordTrace_append hprefix tailTrace_1682490
  have hstable : (prefixWord ++ tailWord_1682490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682490).length < 2 ^ (prefixWord ++ tailWord_1682490).sum := by decide
  have hdescent : baseEnd_1682490 < baseStart_1682490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682494 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1682494 : Nat := 118140960795 + 1682494 * 2 ^ 59
def prefixEnd_1682494 : Nat := 4983230072969 + 3 ^ 40 * 1682494 * 2
def baseEnd_1682494 : Nat := 863928120305845468187357

theorem tailTrace_1682494 : CollatzResearch.WordTrace tailWord_1682494 prefixEnd_1682494 863928120305845468187357 := by
  unfold tailWord_1682494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670699695827382492929817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40910398377746039962292357 7670699695827382492929817)
  ·
    refine ⟨5753024771870536869697363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7670699695827382492929817 5753024771870536869697363)
    ·
      refine ⟨8629537157805805304546045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5753024771870536869697363 8629537157805805304546045)
      ·
        refine ⟨3236076434177176989204767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8629537157805805304546045 3236076434177176989204767)
        ·
          refine ⟨4854114651265765483807151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236076434177176989204767 4854114651265765483807151)
          ·
            refine ⟨7281171976898648225710727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854114651265765483807151 7281171976898648225710727)
            ·
              refine ⟨10921757965347972338566091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7281171976898648225710727 10921757965347972338566091)
              ·
                refine ⟨16382636948021958507849137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10921757965347972338566091 16382636948021958507849137)
                ·
                  refine ⟨12286977711016468880886853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16382636948021958507849137 12286977711016468880886853)
                  ·
                    refine ⟨2303808320815587915166285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12286977711016468880886853 2303808320815587915166285)
                    ·
                      refine ⟨863928120305845468187357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2303808320815587915166285 863928120305845468187357)
                      ·
                        rfl

theorem cell23_1682494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1682494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682494 prefixEnd_1682494 := by exact prefixLift 1682494
  have htrace : WordTrace (prefixWord ++ tailWord_1682494) baseStart_1682494 baseEnd_1682494 := by
    simpa [prefixWord, tailWord_1682494, baseEnd_1682494] using wordTrace_append hprefix tailTrace_1682494
  have hstable : (prefixWord ++ tailWord_1682494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682494).length < 2 ^ (prefixWord ++ tailWord_1682494).sum := by decide
  have hdescent : baseEnd_1682494 < baseStart_1682494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682584 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1682584 : Nat := 118140960795 + 1682584 * 2 ^ 59
def prefixEnd_1682584 : Nat := 4983230072969 + 3 ^ 40 * 1682584 * 2
def baseEnd_1682584 : Nat := 863974333564750116061943

theorem tailTrace_1682584 : CollatzResearch.WordTrace tailWord_1682584 prefixEnd_1682584 863974333564750116061943 := by
  unfold tailWord_1682584
  simp only [CollatzResearch.WordTrace]
  refine ⟨30684440068146502657107403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40912586757528670209476537 30684440068146502657107403)
  ·
    refine ⟨46026660102219753985661105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30684440068146502657107403 46026660102219753985661105)
    ·
      refine ⟨34519995076664815489245829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46026660102219753985661105 34519995076664815489245829)
      ·
        refine ⟨6472499076874652904233593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34519995076664815489245829 6472499076874652904233593)
        ·
          refine ⟨4854374307655989678175195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6472499076874652904233593 4854374307655989678175195)
          ·
            refine ⟨7281561461483984517262793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854374307655989678175195 7281561461483984517262793)
            ·
              refine ⟨5461171096112988387947095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7281561461483984517262793 5461171096112988387947095)
              ·
                refine ⟨8191756644169482581920643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461171096112988387947095 8191756644169482581920643)
                ·
                  refine ⟨12287634966254223872880965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8191756644169482581920643 12287634966254223872880965)
                  ·
                    refine ⟨2303931556172666976165181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12287634966254223872880965 2303931556172666976165181)
                    ·
                      refine ⟨863974333564750116061943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2303931556172666976165181 863974333564750116061943)
                      ·
                        rfl

theorem cell23_1682584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1682584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682584 prefixEnd_1682584 := by exact prefixLift 1682584
  have htrace : WordTrace (prefixWord ++ tailWord_1682584) baseStart_1682584 baseEnd_1682584 := by
    simpa [prefixWord, tailWord_1682584, baseEnd_1682584] using wordTrace_append hprefix tailTrace_1682584
  have hstable : (prefixWord ++ tailWord_1682584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682584).length < 2 ^ (prefixWord ++ tailWord_1682584).sum := by decide
  have hdescent : baseEnd_1682584 < baseStart_1682584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682634 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_1682634 : Nat := 118140960795 + 1682634 * 2 ^ 59
def prefixEnd_1682634 : Nat := 4983230072969 + 3 ^ 40 * 1682634 * 2
def baseEnd_1682634 : Nat := 288000002532491640145571

theorem tailTrace_1682634 : CollatzResearch.WordTrace tailWord_1682634 prefixEnd_1682634 288000002532491640145571 := by
  unfold tailWord_1682634
  simp only [CollatzResearch.WordTrace]
  refine ⟨15342675946527965963383739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40913802524074575902356637 15342675946527965963383739)
  ·
    refine ⟨23014013919791948945075609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15342675946527965963383739 23014013919791948945075609)
    ·
      refine ⟨17260510439843961708806707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23014013919791948945075609 17260510439843961708806707)
      ·
        refine ⟨25890765659765942563210061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17260510439843961708806707 25890765659765942563210061)
        ·
          refine ⟨9709037122412228461203773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25890765659765942563210061 9709037122412228461203773)
          ·
            refine ⟨3640888920904585672951415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9709037122412228461203773 3640888920904585672951415)
            ·
              refine ⟨5461333381356878509427123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640888920904585672951415 5461333381356878509427123)
              ·
                refine ⟨8192000072035317764140685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461333381356878509427123 8192000072035317764140685)
                ·
                  refine ⟨3072000027013244161552757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8192000072035317764140685 3072000027013244161552757)
                  ·
                    refine ⟨288000002532491640145571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3072000027013244161552757 288000002532491640145571)
                    ·
                      rfl

theorem cell23_1682634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_1682634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682634 prefixEnd_1682634 := by exact prefixLift 1682634
  have htrace : WordTrace (prefixWord ++ tailWord_1682634) baseStart_1682634 baseEnd_1682634 := by
    simpa [prefixWord, tailWord_1682634, baseEnd_1682634] using wordTrace_append hprefix tailTrace_1682634
  have hstable : (prefixWord ++ tailWord_1682634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682634).length < 2 ^ (prefixWord ++ tailWord_1682634).sum := by decide
  have hdescent : baseEnd_1682634 < baseStart_1682634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682647 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 3, 6]
def baseStart_1682647 : Nat := 118140960795 + 1682647 * 2 ^ 59
def prefixEnd_1682647 : Nat := 4983230072969 + 3 ^ 40 * 1682647 * 2
def baseEnd_1682647 : Nat := 288002227615327789858051

theorem tailTrace_1682647 : CollatzResearch.WordTrace tailWord_1682647 prefixEnd_1682647 288002227615327789858051 := by
  unfold tailWord_1682647
  simp only [CollatzResearch.WordTrace]
  refine ⟨61371177935064767073758195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40914118623376511382505463 61371177935064767073758195)
  ·
    refine ⟨92056766902597150610637293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61371177935064767073758195 92056766902597150610637293)
    ·
      refine ⟨34521287588473931478988985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92056766902597150610637293 34521287588473931478988985)
      ·
        refine ⟨25890965691355448609241739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34521287588473931478988985 25890965691355448609241739)
        ·
          refine ⟨38836448537033172913862609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25890965691355448609241739 38836448537033172913862609)
          ·
            refine ⟨29127336402774879685396957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38836448537033172913862609 29127336402774879685396957)
            ·
              refine ⟨10922751151040579882023859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29127336402774879685396957 10922751151040579882023859)
              ·
                refine ⟨16384126726560869823035789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10922751151040579882023859 16384126726560869823035789)
                ·
                  refine ⟨6144047522460326183638421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16384126726560869823035789 6144047522460326183638421)
                  ·
                    refine ⟨288002227615327789858051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6144047522460326183638421 288002227615327789858051)
                    ·
                      rfl

theorem cell23_1682647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_1682647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682647 prefixEnd_1682647 := by exact prefixLift 1682647
  have htrace : WordTrace (prefixWord ++ tailWord_1682647) baseStart_1682647 baseEnd_1682647 := by
    simpa [prefixWord, tailWord_1682647, baseEnd_1682647] using wordTrace_append hprefix tailTrace_1682647
  have hstable : (prefixWord ++ tailWord_1682647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682647).length < 2 ^ (prefixWord ++ tailWord_1682647).sum := by decide
  have hdescent : baseEnd_1682647 < baseStart_1682647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682705 : List Nat := [1, 2, 2, 1, 1, 4, 4, 3, 1, 2, 2]
def baseStart_1682705 : Nat := 118140960795 + 1682705 * 2 ^ 59
def prefixEnd_1682705 : Nat := 4983230072969 + 3 ^ 40 * 1682705 * 2
def baseEnd_1682705 : Nat := 864036464723944142648887

theorem tailTrace_1682705 : CollatzResearch.WordTrace tailWord_1682705 prefixEnd_1682705 864036464723944142648887 := by
  unfold tailWord_1682705
  simp only [CollatzResearch.WordTrace]
  refine ⟨61373293368854642979369569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40915528912569761986246379 61373293368854642979369569)
  ·
    refine ⟨46029970026640982234527177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61373293368854642979369569 46029970026640982234527177)
    ·
      refine ⟨34522477519980736675895383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46029970026640982234527177 34522477519980736675895383)
      ·
        refine ⟨51783716279971105013843075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34522477519980736675895383 51783716279971105013843075)
        ·
          refine ⟨77675574419956657520764613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51783716279971105013843075 77675574419956657520764613)
          ·
            refine ⟨14564170203741873285143365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77675574419956657520764613 14564170203741873285143365)
            ·
              refine ⟨2730781913201601240964381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14564170203741873285143365 2730781913201601240964381)
              ·
                refine ⟨1024043217450600465361643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2730781913201601240964381 1024043217450600465361643)
                ·
                  refine ⟨1536064826175900698042465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024043217450600465361643 1536064826175900698042465)
                  ·
                    refine ⟨1152048619631925523531849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1536064826175900698042465 1152048619631925523531849)
                    ·
                      refine ⟨864036464723944142648887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152048619631925523531849 864036464723944142648887)
                      ·
                        rfl

theorem cell23_1682705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 1, 2, 2].length) (baseStart_1682705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682705 prefixEnd_1682705 := by exact prefixLift 1682705
  have htrace : WordTrace (prefixWord ++ tailWord_1682705) baseStart_1682705 baseEnd_1682705 := by
    simpa [prefixWord, tailWord_1682705, baseEnd_1682705] using wordTrace_append hprefix tailTrace_1682705
  have hstable : (prefixWord ++ tailWord_1682705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682705).length < 2 ^ (prefixWord ++ tailWord_1682705).sum := by decide
  have hdescent : baseEnd_1682705 < baseStart_1682705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682738 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_1682738 : Nat := 118140960795 + 1682738 * 2 ^ 59
def prefixEnd_1682738 : Nat := 4983230072969 + 3 ^ 40 * 1682738 * 2
def baseEnd_1682738 : Nat := 864053409585542513536235

theorem tailTrace_1682738 : CollatzResearch.WordTrace tailWord_1682738 prefixEnd_1682738 864053409585542513536235 := by
  unfold tailWord_1682738
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343624244433772403830217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40916331318490059743547245 15343624244433772403830217)
  ·
    refine ⟨11507718183325329302872663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15343624244433772403830217 11507718183325329302872663)
    ·
      refine ⟨17261577274987993954308995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11507718183325329302872663 17261577274987993954308995)
      ·
        refine ⟨25892365912481990931463493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17261577274987993954308995 25892365912481990931463493)
        ·
          refine ⟨4854818608590373299649405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25892365912481990931463493 4854818608590373299649405)
          ·
            refine ⟨1820556978221389987368527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4854818608590373299649405 1820556978221389987368527)
            ·
              refine ⟨2730835467332084981052791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820556978221389987368527 2730835467332084981052791)
              ·
                refine ⟨4096253200998127471579187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730835467332084981052791 4096253200998127471579187)
                ·
                  refine ⟨6144379801497191207368781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4096253200998127471579187 6144379801497191207368781)
                  ·
                    refine ⟨2304142425561446702763293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6144379801497191207368781 2304142425561446702763293)
                    ·
                      refine ⟨864053409585542513536235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2304142425561446702763293 864053409585542513536235)
                      ·
                        rfl

theorem cell23_1682738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_1682738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682738 prefixEnd_1682738 := by exact prefixLift 1682738
  have htrace : WordTrace (prefixWord ++ tailWord_1682738) baseStart_1682738 baseEnd_1682738 := by
    simpa [prefixWord, tailWord_1682738, baseEnd_1682738] using wordTrace_append hprefix tailTrace_1682738
  have hstable : (prefixWord ++ tailWord_1682738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682738).length < 2 ^ (prefixWord ++ tailWord_1682738).sum := by decide
  have hdescent : baseEnd_1682738 < baseStart_1682738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682742 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1682742 : Nat := 118140960795 + 1682742 * 2 ^ 59
def prefixEnd_1682742 : Nat := 4983230072969 + 3 ^ 40 * 1682742 * 2
def baseEnd_1682742 : Nat := 864055463508160497886217

theorem tailTrace_1682742 : CollatzResearch.WordTrace tailWord_1682742 prefixEnd_1682742 864055463508160497886217 := by
  unfold tailWord_1682742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3835915179357537393654155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40916428579813732198977653 3835915179357537393654155)
  ·
    refine ⟨5753872769036306090481233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3835915179357537393654155 5753872769036306090481233)
    ·
      refine ⟨4315404576777229567860925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5753872769036306090481233 4315404576777229567860925)
      ·
        refine ⟨1618276716291461087947847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4315404576777229567860925 1618276716291461087947847)
        ·
          refine ⟨2427415074437191631921771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618276716291461087947847 2427415074437191631921771)
          ·
            refine ⟨3641122611655787447882657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427415074437191631921771 3641122611655787447882657)
            ·
              refine ⟨2730841958741840585911993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3641122611655787447882657 2730841958741840585911993)
              ·
                refine ⟨2048131469056380439433995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2730841958741840585911993 2048131469056380439433995)
                ·
                  refine ⟨3072197203584570659150993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048131469056380439433995 3072197203584570659150993)
                  ·
                    refine ⟨2304147902688427994363245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3072197203584570659150993 2304147902688427994363245)
                    ·
                      refine ⟨864055463508160497886217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2304147902688427994363245 864055463508160497886217)
                      ·
                        rfl

theorem cell23_1682742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1682742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682742 prefixEnd_1682742 := by exact prefixLift 1682742
  have htrace : WordTrace (prefixWord ++ tailWord_1682742) baseStart_1682742 baseEnd_1682742 := by
    simpa [prefixWord, tailWord_1682742, baseEnd_1682742] using wordTrace_append hprefix tailTrace_1682742
  have hstable : (prefixWord ++ tailWord_1682742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682742).length < 2 ^ (prefixWord ++ tailWord_1682742).sum := by decide
  have hdescent : baseEnd_1682742 < baseStart_1682742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682748 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 1, 3, 2]
def baseStart_1682748 : Nat := 118140960795 + 1682748 * 2 ^ 59
def prefixEnd_1682748 : Nat := 4983230072969 + 3 ^ 40 * 1682748 * 2
def baseEnd_1682748 : Nat := 864058544392087474411189

theorem tailTrace_1682748 : CollatzResearch.WordTrace tailWord_1682748 prefixEnd_1682748 864058544392087474411189 := by
  unfold tailWord_1682748
  simp only [CollatzResearch.WordTrace]
  refine ⟨30687430853849430661592449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40916574471799240882123265 30687430853849430661592449)
  ·
    refine ⟨23015573140387072996194337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30687430853849430661592449 23015573140387072996194337)
    ·
      refine ⟨17261679855290304747145753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23015573140387072996194337 17261679855290304747145753)
      ·
        refine ⟨12946259891467728560359315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17261679855290304747145753 12946259891467728560359315)
        ·
          refine ⟨19419389837201592840538973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12946259891467728560359315 19419389837201592840538973)
          ·
            refine ⟨7282271188950597315202115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19419389837201592840538973 7282271188950597315202115)
            ·
              refine ⟨10923406783425895972803173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7282271188950597315202115 10923406783425895972803173)
              ·
                refine ⟨2048138771892355494900595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10923406783425895972803173 2048138771892355494900595)
                ·
                  refine ⟨3072208157838533242350893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048138771892355494900595 3072208157838533242350893)
                  ·
                    refine ⟨1152078059189449965881585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3072208157838533242350893 1152078059189449965881585)
                    ·
                      refine ⟨864058544392087474411189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152078059189449965881585 864058544392087474411189)
                      ·
                        rfl

theorem cell23_1682748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_1682748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682748 prefixEnd_1682748 := by exact prefixLift 1682748
  have htrace : WordTrace (prefixWord ++ tailWord_1682748) baseStart_1682748 baseEnd_1682748 := by
    simpa [prefixWord, tailWord_1682748, baseEnd_1682748] using wordTrace_append hprefix tailTrace_1682748
  have hstable : (prefixWord ++ tailWord_1682748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682748).length < 2 ^ (prefixWord ++ tailWord_1682748).sum := by decide
  have hdescent : baseEnd_1682748 < baseStart_1682748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682761 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 1, 4, 2]
def baseStart_1682761 : Nat := 118140960795 + 1682761 * 2 ^ 59
def prefixEnd_1682761 : Nat := 4983230072969 + 3 ^ 40 * 1682761 * 2
def baseEnd_1682761 : Nat := 864065219640595923548629

theorem tailTrace_1682761 : CollatzResearch.WordTrace tailWord_1682761 prefixEnd_1682761 864065219640595923548629 := by
  unfold tailWord_1682761
  simp only [CollatzResearch.WordTrace]
  refine ⟨61375335856651764543408137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40916890571101176362272091 61375335856651764543408137)
  ·
    refine ⟨46031501892488823407556103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61375335856651764543408137 46031501892488823407556103)
    ·
      refine ⟨69047252838733235111334155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46031501892488823407556103 69047252838733235111334155)
      ·
        refine ⟨103570879258099852667001233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69047252838733235111334155 103570879258099852667001233)
        ·
          refine ⟨77678159443574889500250925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103570879258099852667001233 77678159443574889500250925)
          ·
            refine ⟨29129309791340583562594097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77678159443574889500250925 29129309791340583562594097)
            ·
              refine ⟨21846982343505437671945573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29129309791340583562594097 21846982343505437671945573)
              ·
                refine ⟨4096309189407269563489795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21846982343505437671945573 4096309189407269563489795)
                ·
                  refine ⟨6144463784110904345234693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4096309189407269563489795 6144463784110904345234693)
                  ·
                    refine ⟨1152086959520794564731505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6144463784110904345234693 1152086959520794564731505)
                    ·
                      refine ⟨864065219640595923548629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152086959520794564731505 864065219640595923548629)
                      ·
                        rfl

theorem cell23_1682761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 4, 2].length) (baseStart_1682761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682761 prefixEnd_1682761 := by exact prefixLift 1682761
  have htrace : WordTrace (prefixWord ++ tailWord_1682761) baseStart_1682761 baseEnd_1682761 := by
    simpa [prefixWord, tailWord_1682761, baseEnd_1682761] using wordTrace_append hprefix tailTrace_1682761
  have hstable : (prefixWord ++ tailWord_1682761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682761).length < 2 ^ (prefixWord ++ tailWord_1682761).sum := by decide
  have hdescent : baseEnd_1682761 < baseStart_1682761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682764 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1682764 : Nat := 118140960795 + 1682764 * 2 ^ 59
def prefixEnd_1682764 : Nat := 4983230072969 + 3 ^ 40 * 1682764 * 2
def baseEnd_1682764 : Nat := 864066760082559411811115

theorem tailTrace_1682764 : CollatzResearch.WordTrace tailWord_1682764 prefixEnd_1682764 864066760082559411811115 := by
  unfold tailWord_1682764
  simp only [CollatzResearch.WordTrace]
  refine ⟨30687722637820448027883673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40916963517093930703844897 30687722637820448027883673)
  ·
    refine ⟨23015791978365336020912755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30687722637820448027883673 23015791978365336020912755)
    ·
      refine ⟨34523687967548004031369133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23015791978365336020912755 34523687967548004031369133)
      ·
        refine ⟨12946382987830501511763425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34523687967548004031369133 12946382987830501511763425)
        ·
          refine ⟨9709787240872876133822569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12946382987830501511763425 9709787240872876133822569)
          ·
            refine ⟨7282340430654657100366927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9709787240872876133822569 7282340430654657100366927)
            ·
              refine ⟨10923510645981985650550391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7282340430654657100366927 10923510645981985650550391)
              ·
                refine ⟨16385265968972978475825587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10923510645981985650550391 16385265968972978475825587)
                ·
                  refine ⟨24577898953459467713738381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16385265968972978475825587 24577898953459467713738381)
                  ·
                    refine ⟨9216712107547300392651893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24577898953459467713738381 9216712107547300392651893)
                    ·
                      refine ⟨864066760082559411811115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9216712107547300392651893 864066760082559411811115)
                      ·
                        rfl

theorem cell23_1682764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1682764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682764 prefixEnd_1682764 := by exact prefixLift 1682764
  have htrace : WordTrace (prefixWord ++ tailWord_1682764) baseStart_1682764 baseEnd_1682764 := by
    simpa [prefixWord, tailWord_1682764, baseEnd_1682764] using wordTrace_append hprefix tailTrace_1682764
  have hstable : (prefixWord ++ tailWord_1682764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682764).length < 2 ^ (prefixWord ++ tailWord_1682764).sum := by decide
  have hdescent : baseEnd_1682764 < baseStart_1682764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682778 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2]
def baseStart_1682778 : Nat := 118140960795 + 1682778 * 2 ^ 59
def prefixEnd_1682778 : Nat := 4983230072969 + 3 ^ 40 * 1682778 * 2
def baseEnd_1682778 : Nat := 864073948811722357036051

theorem tailTrace_1682778 : CollatzResearch.WordTrace tailWord_1682778 prefixEnd_1682778 864073948811722357036051 := by
  unfold tailWord_1682778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343988974397544111694247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40917303931726784297851325 15343988974397544111694247)
  ·
    refine ⟨23015983461596316167541371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15343988974397544111694247 23015983461596316167541371)
    ·
      refine ⟨34523975192394474251312057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23015983461596316167541371 34523975192394474251312057)
      ·
        refine ⟨25892981394295855688484043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34523975192394474251312057 25892981394295855688484043)
        ·
          refine ⟨38839472091443783532726065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25892981394295855688484043 38839472091443783532726065)
          ·
            refine ⟨29129604068582837649544549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38839472091443783532726065 29129604068582837649544549)
            ·
              refine ⟨5461800762859282059289603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29129604068582837649544549 5461800762859282059289603)
              ·
                refine ⟨8192701144288923088934405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461800762859282059289603 8192701144288923088934405)
                ·
                  refine ⟨1536131464554173079175201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8192701144288923088934405 1536131464554173079175201)
                  ·
                    refine ⟨1152098598415629809381401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1536131464554173079175201 1152098598415629809381401)
                    ·
                      refine ⟨864073948811722357036051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152098598415629809381401 864073948811722357036051)
                      ·
                        rfl

theorem cell23_1682778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_1682778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682778 prefixEnd_1682778 := by exact prefixLift 1682778
  have htrace : WordTrace (prefixWord ++ tailWord_1682778) baseStart_1682778 baseEnd_1682778 := by
    simpa [prefixWord, tailWord_1682778, baseEnd_1682778] using wordTrace_append hprefix tailTrace_1682778
  have hstable : (prefixWord ++ tailWord_1682778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682778).length < 2 ^ (prefixWord ++ tailWord_1682778).sum := by decide
  have hdescent : baseEnd_1682778 < baseStart_1682778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682864 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_1682864 : Nat := 118140960795 + 1682864 * 2 ^ 59
def prefixEnd_1682864 : Nat := 4983230072969 + 3 ^ 40 * 1682864 * 2
def baseEnd_1682864 : Nat := 864118108148009020560655

theorem tailTrace_1682864 : CollatzResearch.WordTrace tailWord_1682864 prefixEnd_1682864 864118108148009020560655 := by
  unfold tailWord_1682864
  simp only [CollatzResearch.WordTrace]
  refine ⟨30689546287639306567203823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40919395050185742089605097 30689546287639306567203823)
  ·
    refine ⟨46034319431458959850805735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30689546287639306567203823 46034319431458959850805735)
    ·
      refine ⟨69051479147188439776208603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46034319431458959850805735 69051479147188439776208603)
      ·
        refine ⟨103577218720782659664312905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69051479147188439776208603 103577218720782659664312905)
        ·
          refine ⟨77682914040586994748234679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103577218720782659664312905 77682914040586994748234679)
          ·
            refine ⟨116524371060880492122352019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77682914040586994748234679 116524371060880492122352019)
            ·
              refine ⟨174786556591320738183528029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116524371060880492122352019 174786556591320738183528029)
              ·
                refine ⟨65544958721745276818823011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174786556591320738183528029 65544958721745276818823011)
                ·
                  refine ⟨98317438082617915228234517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65544958721745276818823011 98317438082617915228234517)
                  ·
                    refine ⟨4608629910122714776323493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98317438082617915228234517 4608629910122714776323493)
                    ·
                      refine ⟨864118108148009020560655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4608629910122714776323493 864118108148009020560655)
                      ·
                        rfl

theorem cell23_1682864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_1682864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682864 prefixEnd_1682864 := by exact prefixLift 1682864
  have htrace : WordTrace (prefixWord ++ tailWord_1682864) baseStart_1682864 baseEnd_1682864 := by
    simpa [prefixWord, tailWord_1682864, baseEnd_1682864] using wordTrace_append hprefix tailTrace_1682864
  have hstable : (prefixWord ++ tailWord_1682864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682864).length < 2 ^ (prefixWord ++ tailWord_1682864).sum := by decide
  have hdescent : baseEnd_1682864 < baseStart_1682864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682871 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 3]
def baseStart_1682871 : Nat := 118140960795 + 1682871 * 2 ^ 59
def prefixEnd_1682871 : Nat := 4983230072969 + 3 ^ 40 * 1682871 * 2
def baseEnd_1682871 : Nat := 864121702512590493173123

theorem tailTrace_1682871 : CollatzResearch.WordTrace tailWord_1682871 prefixEnd_1682871 864121702512590493173123 := by
  unfold tailWord_1682871
  simp only [CollatzResearch.WordTrace]
  refine ⟨61379347886253253329912467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40919565257502168886608311 61379347886253253329912467)
  ·
    refine ⟨92069021829379879994868701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61379347886253253329912467 92069021829379879994868701)
    ·
      refine ⟨34525883186017454998075763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92069021829379879994868701 34525883186017454998075763)
      ·
        refine ⟨51788824779026182497113645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34525883186017454998075763 51788824779026182497113645)
        ·
          refine ⟨19420809292134818436417617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51788824779026182497113645 19420809292134818436417617)
          ·
            refine ⟨14565606969101113827313213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19420809292134818436417617 14565606969101113827313213)
            ·
              refine ⟨5462102613412917685242455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14565606969101113827313213 5462102613412917685242455)
              ·
                refine ⟨8193153920119376527863683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5462102613412917685242455 8193153920119376527863683)
                ·
                  refine ⟨12289730880179064791795525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8193153920119376527863683 12289730880179064791795525)
                  ·
                    refine ⟨2304324540033574648461661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12289730880179064791795525 2304324540033574648461661)
                    ·
                      refine ⟨864121702512590493173123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2304324540033574648461661 864121702512590493173123)
                      ·
                        rfl

theorem cell23_1682871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_1682871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682871 prefixEnd_1682871 := by exact prefixLift 1682871
  have htrace : WordTrace (prefixWord ++ tailWord_1682871) baseStart_1682871 baseEnd_1682871 := by
    simpa [prefixWord, tailWord_1682871, baseEnd_1682871] using wordTrace_append hprefix tailTrace_1682871
  have hstable : (prefixWord ++ tailWord_1682871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682871).length < 2 ^ (prefixWord ++ tailWord_1682871).sum := by decide
  have hdescent : baseEnd_1682871 < baseStart_1682871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682891 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 6]
def baseStart_1682891 : Nat := 118140960795 + 1682891 * 2 ^ 59
def prefixEnd_1682891 : Nat := 4983230072969 + 3 ^ 40 * 1682891 * 2
def baseEnd_1682891 : Nat := 96014663569520046102559

theorem tailTrace_1682891 : CollatzResearch.WordTrace tailWord_1682891 prefixEnd_1682891 96014663569520046102559 := by
  unfold tailWord_1682891
  simp only [CollatzResearch.WordTrace]
  refine ⟨61380077346180796745640527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40920051564120531163760351 61380077346180796745640527)
  ·
    refine ⟨92070116019271195118460791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61380077346180796745640527 92070116019271195118460791)
    ·
      refine ⟨138105174028906792677691187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92070116019271195118460791 138105174028906792677691187)
      ·
        refine ⟨207157761043360189016536781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138105174028906792677691187 207157761043360189016536781)
        ·
          refine ⟨77684160391260070881201293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207157761043360189016536781 77684160391260070881201293)
          ·
            refine ⟨29131560146722526580450485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77684160391260070881201293 29131560146722526580450485)
            ·
              refine ⟨2731083763755236866917233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29131560146722526580450485 2731083763755236866917233)
              ·
                refine ⟨2048312822816427650187925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731083763755236866917233 2048312822816427650187925)
                ·
                  refine ⟨96014663569520046102559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2048312822816427650187925 96014663569520046102559)
                  ·
                    rfl

theorem cell23_1682891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 6].length) (baseStart_1682891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682891 prefixEnd_1682891 := by exact prefixLift 1682891
  have htrace : WordTrace (prefixWord ++ tailWord_1682891) baseStart_1682891 baseEnd_1682891 := by
    simpa [prefixWord, tailWord_1682891, baseEnd_1682891] using wordTrace_append hprefix tailTrace_1682891
  have hstable : (prefixWord ++ tailWord_1682891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682891).length < 2 ^ (prefixWord ++ tailWord_1682891).sum := by decide
  have hdescent : baseEnd_1682891 < baseStart_1682891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682928 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 1, 5, 2]
def baseStart_1682928 : Nat := 118140960795 + 1682928 * 2 ^ 59
def prefixEnd_1682928 : Nat := 4983230072969 + 3 ^ 40 * 1682928 * 2
def baseEnd_1682928 : Nat := 864150970909896770160361

theorem tailTrace_1682928 : CollatzResearch.WordTrace tailWord_1682928 prefixEnd_1682928 864150970909896770160361 := by
  unfold tailWord_1682928
  simp only [CollatzResearch.WordTrace]
  refine ⟨30690713423523376032368719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40920951231364501376491625 30690713423523376032368719)
  ·
    refine ⟨46036070135285064048553079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30690713423523376032368719 46036070135285064048553079)
    ·
      refine ⟨69054105202927596072829619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46036070135285064048553079 69054105202927596072829619)
      ·
        refine ⟨103581157804391394109244429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69054105202927596072829619 103581157804391394109244429)
        ·
          refine ⟨38842934176646772790966661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103581157804391394109244429 38842934176646772790966661)
          ·
            refine ⟨7283050158121269898306249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38842934176646772790966661 7283050158121269898306249)
            ·
              refine ⟨5462287618590952423729687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7283050158121269898306249 5462287618590952423729687)
              ·
                refine ⟨8193431427886428635594531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5462287618590952423729687 8193431427886428635594531)
                ·
                  refine ⟨12290147141829642953391797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8193431427886428635594531 12290147141829642953391797)
                  ·
                    refine ⟨1152201294546529026880481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12290147141829642953391797 1152201294546529026880481)
                    ·
                      refine ⟨864150970909896770160361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152201294546529026880481 864150970909896770160361)
                      ·
                        rfl

theorem cell23_1682928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 5, 2].length) (baseStart_1682928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682928 prefixEnd_1682928 := by exact prefixLift 1682928
  have htrace : WordTrace (prefixWord ++ tailWord_1682928) baseStart_1682928 baseEnd_1682928 := by
    simpa [prefixWord, tailWord_1682928, baseEnd_1682928] using wordTrace_append hprefix tailTrace_1682928
  have hstable : (prefixWord ++ tailWord_1682928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682928).length < 2 ^ (prefixWord ++ tailWord_1682928).sum := by decide
  have hdescent : baseEnd_1682928 < baseStart_1682928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682935 : List Nat := [1, 1, 3, 1, 1, 1, 1, 9, 1, 1, 3]
def baseStart_1682935 : Nat := 118140960795 + 1682935 * 2 ^ 59
def prefixEnd_1682935 : Nat := 4983230072969 + 3 ^ 40 * 1682935 * 2
def baseEnd_1682935 : Nat := 864154565274478242772829

theorem tailTrace_1682935 : CollatzResearch.WordTrace tailWord_1682935 prefixEnd_1682935 864154565274478242772829 := by
  unfold tailWord_1682935
  simp only [CollatzResearch.WordTrace]
  refine ⟨61381682158021392260242259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40921121438680928173494839 61381682158021392260242259)
  ·
    refine ⟨92072523237032088390363389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61381682158021392260242259 92072523237032088390363389)
    ·
      refine ⟨34527196213887033146386271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92072523237032088390363389 34527196213887033146386271)
      ·
        refine ⟨51790794320830549719579407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34527196213887033146386271 51790794320830549719579407)
        ·
          refine ⟨77686191481245824579369111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51790794320830549719579407 77686191481245824579369111)
          ·
            refine ⟨116529287221868736869053667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77686191481245824579369111 116529287221868736869053667)
            ·
              refine ⟨174793930832803105303580501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116529287221868736869053667 174793930832803105303580501)
              ·
                refine ⟨1024183188473455695138167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 174793930832803105303580501 1024183188473455695138167)
                ·
                  refine ⟨1536274782710183542707251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024183188473455695138167 1536274782710183542707251)
                  ·
                    refine ⟨2304412174065275314060877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1536274782710183542707251 2304412174065275314060877)
                    ·
                      refine ⟨864154565274478242772829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2304412174065275314060877 864154565274478242772829)
                      ·
                        rfl

theorem cell23_1682935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 1, 1, 3].length) (baseStart_1682935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682935 prefixEnd_1682935 := by exact prefixLift 1682935
  have htrace : WordTrace (prefixWord ++ tailWord_1682935) baseStart_1682935 baseEnd_1682935 := by
    simpa [prefixWord, tailWord_1682935, baseEnd_1682935] using wordTrace_append hprefix tailTrace_1682935
  have hstable : (prefixWord ++ tailWord_1682935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682935).length < 2 ^ (prefixWord ++ tailWord_1682935).sum := by decide
  have hdescent : baseEnd_1682935 < baseStart_1682935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682961 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_1682961 : Nat := 118140960795 + 1682961 * 2 ^ 59
def prefixEnd_1682961 : Nat := 4983230072969 + 3 ^ 40 * 1682961 * 2
def baseEnd_1682961 : Nat := 864167915771495141047709

theorem tailTrace_1682961 : CollatzResearch.WordTrace tailWord_1682961 prefixEnd_1682961 864167915771495141047709 := by
  unfold tailWord_1682961
  simp only [CollatzResearch.WordTrace]
  refine ⟨61382630455927198700688737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40921753637284799133792491 61382630455927198700688737)
  ·
    refine ⟨46036972841945399025516553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61382630455927198700688737 46036972841945399025516553)
    ·
      refine ⟨34527729631459049269137415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46036972841945399025516553 34527729631459049269137415)
      ·
        refine ⟨51791594447188573903706123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34527729631459049269137415 51791594447188573903706123)
        ·
          refine ⟨77687391670782860855559185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51791594447188573903706123 77687391670782860855559185)
          ·
            refine ⟨58265543753087145641669389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77687391670782860855559185 58265543753087145641669389)
            ·
              refine ⟨21849578907407679615626021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58265543753087145641669389 21849578907407679615626021)
              ·
                refine ⟨4096796045138939927929879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21849578907407679615626021 4096796045138939927929879)
                ·
                  refine ⟨6145194067708409891894819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4096796045138939927929879 6145194067708409891894819)
                  ·
                    refine ⟨9217791101562614837842229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6145194067708409891894819 9217791101562614837842229)
                    ·
                      refine ⟨864167915771495141047709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9217791101562614837842229 864167915771495141047709)
                      ·
                        rfl

theorem cell23_1682961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_1682961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682961 prefixEnd_1682961 := by exact prefixLift 1682961
  have htrace : WordTrace (prefixWord ++ tailWord_1682961) baseStart_1682961 baseEnd_1682961 := by
    simpa [prefixWord, tailWord_1682961, baseEnd_1682961] using wordTrace_append hprefix tailTrace_1682961
  have hstable : (prefixWord ++ tailWord_1682961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682961).length < 2 ^ (prefixWord ++ tailWord_1682961).sum := by decide
  have hdescent : baseEnd_1682961 < baseStart_1682961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682975 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 3, 2, 2]
def baseStart_1682975 : Nat := 118140960795 + 1682975 * 2 ^ 59
def prefixEnd_1682975 : Nat := 4983230072969 + 3 ^ 40 * 1682975 * 2
def baseEnd_1682975 : Nat := 864175104500658086272645

theorem tailTrace_1682975 : CollatzResearch.WordTrace tailWord_1682975 prefixEnd_1682975 864175104500658086272645 := by
  unfold tailWord_1682975
  simp only [CollatzResearch.WordTrace]
  refine ⟨61383141077876479091698379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40922094051917652727798919 61383141077876479091698379)
  ·
    refine ⟨92074711616814718637547569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61383141077876479091698379 92074711616814718637547569)
    ·
      refine ⟨69056033712611038978160677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92074711616814718637547569 69056033712611038978160677)
      ·
        refine ⟨12948006321114569808405127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69056033712611038978160677 12948006321114569808405127)
        ·
          refine ⟨19422009481671854712607691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12948006321114569808405127 19422009481671854712607691)
          ·
            refine ⟨29133014222507782068911537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19422009481671854712607691 29133014222507782068911537)
            ·
              refine ⟨21849760666880836551683653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29133014222507782068911537 21849760666880836551683653)
              ·
                refine ⟨4096830125040156853440685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21849760666880836551683653 4096830125040156853440685)
                ·
                  refine ⟨1536311296890058820040257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4096830125040156853440685 1536311296890058820040257)
                  ·
                    refine ⟨1152233472667544115030193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1536311296890058820040257 1152233472667544115030193)
                    ·
                      refine ⟨864175104500658086272645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152233472667544115030193 864175104500658086272645)
                      ·
                        rfl

theorem cell23_1682975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_1682975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682975 prefixEnd_1682975 := by exact prefixLift 1682975
  have htrace : WordTrace (prefixWord ++ tailWord_1682975) baseStart_1682975 baseEnd_1682975 := by
    simpa [prefixWord, tailWord_1682975, baseEnd_1682975] using wordTrace_append hprefix tailTrace_1682975
  have hstable : (prefixWord ++ tailWord_1682975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682975).length < 2 ^ (prefixWord ++ tailWord_1682975).sum := by decide
  have hdescent : baseEnd_1682975 < baseStart_1682975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682992 : List Nat := [2, 1, 1, 1, 2, 3, 1, 7, 1, 2, 2]
def baseStart_1682992 : Nat := 118140960795 + 1682992 * 2 ^ 59
def prefixEnd_1682992 : Nat := 4983230072969 + 3 ^ 40 * 1682992 * 2
def baseEnd_1682992 : Nat := 864183833671784519760067

theorem tailTrace_1682992 : CollatzResearch.WordTrace tailWord_1682992 prefixEnd_1682992 864183833671784519760067 := by
  unfold tailWord_1682992
  simp only [CollatzResearch.WordTrace]
  refine ⟨30691880559407445497533615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40922507412543260663378153 30691880559407445497533615)
  ·
    refine ⟨46037820839111168246300423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30691880559407445497533615 46037820839111168246300423)
    ·
      refine ⟨69056731258666752369450635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46037820839111168246300423 69056731258666752369450635)
      ·
        refine ⟨103585096888000128554175953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69056731258666752369450635 103585096888000128554175953)
        ·
          refine ⟨77688822666000096415631965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103585096888000128554175953 77688822666000096415631965)
          ·
            refine ⟨29133308499750036155861987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77688822666000096415631965 29133308499750036155861987)
            ·
              refine ⟨43699962749625054233792981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29133308499750036155861987 43699962749625054233792981)
              ·
                refine ⟨1024217876944337208604523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43699962749625054233792981 1024217876944337208604523)
                ·
                  refine ⟨1536326815416505812906785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024217876944337208604523 1536326815416505812906785)
                  ·
                    refine ⟨1152245111562379359680089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1536326815416505812906785 1152245111562379359680089)
                    ·
                      refine ⟨864183833671784519760067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152245111562379359680089 864183833671784519760067)
                      ·
                        rfl

theorem cell23_1682992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 1, 2, 2].length) (baseStart_1682992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682992 prefixEnd_1682992 := by exact prefixLift 1682992
  have htrace : WordTrace (prefixWord ++ tailWord_1682992) baseStart_1682992 baseEnd_1682992 := by
    simpa [prefixWord, tailWord_1682992, baseEnd_1682992] using wordTrace_append hprefix tailTrace_1682992
  have hstable : (prefixWord ++ tailWord_1682992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682992).length < 2 ^ (prefixWord ++ tailWord_1682992).sum := by decide
  have hdescent : baseEnd_1682992 < baseStart_1682992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682998 : List Nat := [5, 1, 2, 1, 3, 11]
def baseStart_1682998 : Nat := 118140960795 + 1682998 * 2 ^ 59
def prefixEnd_1682998 : Nat := 4983230072969 + 3 ^ 40 * 1682998 * 2
def baseEnd_1682998 : Nat := 3556324751258072001173

theorem tailTrace_1682998 : CollatzResearch.WordTrace tailWord_1682998 prefixEnd_1682998 3556324751258072001173 := by
  unfold tailWord_1682998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836498747299572126236603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40922653304528769346523765 3836498747299572126236603)
  ·
    refine ⟨5754748120949358189354905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3836498747299572126236603 5754748120949358189354905)
    ·
      refine ⟨4316061090712018642016179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5754748120949358189354905 4316061090712018642016179)
      ·
        refine ⟨6474091636068027963024269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4316061090712018642016179 6474091636068027963024269)
        ·
          refine ⟨2427784363525510486134101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6474091636068027963024269 2427784363525510486134101)
          ·
            refine ⟨3556324751258072001173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2427784363525510486134101 3556324751258072001173)
            ·
              rfl

theorem cell23_1682998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 11].length) (baseStart_1682998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1682998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1682998 prefixEnd_1682998 := by exact prefixLift 1682998
  have htrace : WordTrace (prefixWord ++ tailWord_1682998) baseStart_1682998 baseEnd_1682998 := by
    simpa [prefixWord, tailWord_1682998, baseEnd_1682998] using wordTrace_append hprefix tailTrace_1682998
  have hstable : (prefixWord ++ tailWord_1682998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682998).length < 2 ^ (prefixWord ++ tailWord_1682998).sum := by decide
  have hdescent : baseEnd_1682998 < baseStart_1682998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683009 : List Nat := [1, 2, 5, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_1683009 : Nat := 118140960795 + 1683009 * 2 ^ 59
def prefixEnd_1683009 : Nat := 4983230072969 + 3 ^ 40 * 1683009 * 2
def baseEnd_1683009 : Nat := 864192562842910953247489

theorem tailTrace_1683009 : CollatzResearch.WordTrace tailWord_1683009 prefixEnd_1683009 864192562842910953247489 := by
  unfold tailWord_1683009
  simp only [CollatzResearch.WordTrace]
  refine ⟨61384381159753302898436081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40922920773168868598957387 61384381159753302898436081)
  ·
    refine ⟨46038285869814977173827061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61384381159753302898436081 46038285869814977173827061)
    ·
      refine ⟨4316089300295154110046287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46038285869814977173827061 4316089300295154110046287)
      ·
        refine ⟨6474133950442731165069431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4316089300295154110046287 6474133950442731165069431)
        ·
          refine ⟨9711200925664096747604147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6474133950442731165069431 9711200925664096747604147)
          ·
            refine ⟨14566801388496145121406221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9711200925664096747604147 14566801388496145121406221)
            ·
              refine ⟨5462550520686054420527333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14566801388496145121406221 5462550520686054420527333)
              ·
                refine ⟨1024228222628635203848875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5462550520686054420527333 1024228222628635203848875)
                ·
                  refine ⟨1536342333942952805773313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024228222628635203848875 1536342333942952805773313)
                  ·
                    refine ⟨1152256750457214604329985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1536342333942952805773313 1152256750457214604329985)
                    ·
                      refine ⟨864192562842910953247489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152256750457214604329985 864192562842910953247489)
                      ·
                        rfl

theorem cell23_1683009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_1683009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683009 prefixEnd_1683009 := by exact prefixLift 1683009
  have htrace : WordTrace (prefixWord ++ tailWord_1683009) baseStart_1683009 baseEnd_1683009 := by
    simpa [prefixWord, tailWord_1683009, baseEnd_1683009] using wordTrace_append hprefix tailTrace_1683009
  have hstable : (prefixWord ++ tailWord_1683009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683009).length < 2 ^ (prefixWord ++ tailWord_1683009).sum := by decide
  have hdescent : baseEnd_1683009 < baseStart_1683009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683015 : List Nat := [1, 1, 4, 1, 6, 1, 1, 8]
def baseStart_1683015 : Nat := 118140960795 + 1683015 * 2 ^ 59
def prefixEnd_1683015 : Nat := 4983230072969 + 3 ^ 40 * 1683015 * 2
def baseEnd_1683015 : Nat := 32007246063956960361943

theorem tailTrace_1683015 : CollatzResearch.WordTrace tailWord_1683015 prefixEnd_1683015 32007246063956960361943 := by
  unfold tailWord_1683015
  simp only [CollatzResearch.WordTrace]
  refine ⟨61384599997731565923154499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40923066665154377282102999 61384599997731565923154499)
  ·
    refine ⟨92076899996597348884731749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61384599997731565923154499 92076899996597348884731749)
    ·
      refine ⟨17264418749362002915887203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92076899996597348884731749 17264418749362002915887203)
      ·
        refine ⟨25896628124043004373830805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17264418749362002915887203 25896628124043004373830805)
        ·
          refine ⟨1213904443314515830023319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25896628124043004373830805 1213904443314515830023319)
          ·
            refine ⟨1820856664971773745034979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213904443314515830023319 1820856664971773745034979)
            ·
              refine ⟨2731284997457660617552469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820856664971773745034979 2731284997457660617552469)
              ·
                refine ⟨32007246063956960361943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2731284997457660617552469 32007246063956960361943)
                ·
                  rfl

theorem cell23_1683015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 8].length) (baseStart_1683015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683015 prefixEnd_1683015 := by exact prefixLift 1683015
  have htrace : WordTrace (prefixWord ++ tailWord_1683015) baseStart_1683015 baseEnd_1683015 := by
    simpa [prefixWord, tailWord_1683015, baseEnd_1683015] using wordTrace_append hprefix tailTrace_1683015
  have hstable : (prefixWord ++ tailWord_1683015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683015).length < 2 ^ (prefixWord ++ tailWord_1683015).sum := by decide
  have hdescent : baseEnd_1683015 < baseStart_1683015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683025 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 2, 1, 3]
def baseStart_1683025 : Nat := 118140960795 + 1683025 * 2 ^ 59
def prefixEnd_1683025 : Nat := 4983230072969 + 3 ^ 40 * 1683025 * 2
def baseEnd_1683025 : Nat := 864200778533382890647415

theorem tailTrace_1683025 : CollatzResearch.WordTrace tailWord_1683025 prefixEnd_1683025 864200778533382890647415 := by
  unfold tailWord_1683025
  simp only [CollatzResearch.WordTrace]
  refine ⟨61384964727695337631018529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40923309818463558420679019 61384964727695337631018529)
  ·
    refine ⟨46038723545771503223263897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61384964727695337631018529 46038723545771503223263897)
    ·
      refine ⟨34529042659328627417447923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46038723545771503223263897 34529042659328627417447923)
      ·
        refine ⟨51793563988992941126171885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34529042659328627417447923 51793563988992941126171885)
        ·
          refine ⟨19422586495872352922314457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51793563988992941126171885 19422586495872352922314457)
          ·
            refine ⟨14566939871904264691735843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19422586495872352922314457 14566939871904264691735843)
            ·
              refine ⟨21850409807856397037603765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14566939871904264691735843 21850409807856397037603765)
              ·
                refine ⟨2048475919486537222275353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21850409807856397037603765 2048475919486537222275353)
                ·
                  refine ⟨1536356939614902916706515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2048475919486537222275353 1536356939614902916706515)
                  ·
                    refine ⟨2304535409422354375059773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1536356939614902916706515 2304535409422354375059773)
                    ·
                      refine ⟨864200778533382890647415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2304535409422354375059773 864200778533382890647415)
                      ·
                        rfl

theorem cell23_1683025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_1683025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683025 prefixEnd_1683025 := by exact prefixLift 1683025
  have htrace : WordTrace (prefixWord ++ tailWord_1683025) baseStart_1683025 baseEnd_1683025 := by
    simpa [prefixWord, tailWord_1683025, baseEnd_1683025] using wordTrace_append hprefix tailTrace_1683025
  have hstable : (prefixWord ++ tailWord_1683025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683025).length < 2 ^ (prefixWord ++ tailWord_1683025).sum := by decide
  have hdescent : baseEnd_1683025 < baseStart_1683025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683041 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 1, 8]
def baseStart_1683041 : Nat := 118140960795 + 1683041 * 2 ^ 59
def prefixEnd_1683041 : Nat := 4983230072969 + 3 ^ 40 * 1683041 * 2
def baseEnd_1683041 : Nat := 288069664741284942682447

theorem tailTrace_1683041 : CollatzResearch.WordTrace tailWord_1683041 prefixEnd_1683041 288069664741284942682447 := by
  unfold tailWord_1683041
  simp only [CollatzResearch.WordTrace]
  refine ⟨61385548295637372363600977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40923698863758248242400651 61385548295637372363600977)
  ·
    refine ⟨46039161221728029272700733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61385548295637372363600977 46039161221728029272700733)
    ·
      refine ⟨17264685458148010977262775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46039161221728029272700733 17264685458148010977262775)
      ·
        refine ⟨25897028187222016465894163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17264685458148010977262775 25897028187222016465894163)
        ·
          refine ⟨38845542280833024698841245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25897028187222016465894163 38845542280833024698841245)
          ·
            refine ⟨14567078355312384262065467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38845542280833024698841245 14567078355312384262065467)
            ·
              refine ⟨21850617532968576393098201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14567078355312384262065467 21850617532968576393098201)
              ·
                refine ⟨16387963149726432294823651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21850617532968576393098201 16387963149726432294823651)
                ·
                  refine ⟨24581944724589648442235477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16387963149726432294823651 24581944724589648442235477)
                  ·
                    refine ⟨288069664741284942682447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24581944724589648442235477 288069664741284942682447)
                    ·
                      rfl

theorem cell23_1683041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_1683041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683041 prefixEnd_1683041 := by exact prefixLift 1683041
  have htrace : WordTrace (prefixWord ++ tailWord_1683041) baseStart_1683041 baseEnd_1683041 := by
    simpa [prefixWord, tailWord_1683041, baseEnd_1683041] using wordTrace_append hprefix tailTrace_1683041
  have hstable : (prefixWord ++ tailWord_1683041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683041).length < 2 ^ (prefixWord ++ tailWord_1683041).sum := by decide
  have hdescent : baseEnd_1683041 < baseStart_1683041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683051 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 5]
def baseStart_1683051 : Nat := 118140960795 + 1683051 * 2 ^ 59
def prefixEnd_1683051 : Nat := 4983230072969 + 3 ^ 40 * 1683051 * 2
def baseEnd_1683051 : Nat := 864214129030399788922295

theorem tailTrace_1683051 : CollatzResearch.WordTrace tailWord_1683051 prefixEnd_1683051 864214129030399788922295 := by
  unfold tailWord_1683051
  simp only [CollatzResearch.WordTrace]
  refine ⟨61385913025601144071465007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40923942017067429380976671 61385913025601144071465007)
  ·
    refine ⟨92078869538401716107197511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61385913025601144071465007 92078869538401716107197511)
    ·
      refine ⟨138118304307602574160796267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92078869538401716107197511 138118304307602574160796267)
      ·
        refine ⟨207177456461403861241194401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138118304307602574160796267 207177456461403861241194401)
        ·
          refine ⟨155383092346052895930895801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207177456461403861241194401 155383092346052895930895801)
          ·
            refine ⟨116537319259539671948171851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155383092346052895930895801 116537319259539671948171851)
            ·
              refine ⟨174805978889309507922257777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116537319259539671948171851 174805978889309507922257777)
              ·
                refine ⟨131104484166982130941693333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174805978889309507922257777 131104484166982130941693333)
                ·
                  refine ⟨6145522695327287387891875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131104484166982130941693333 6145522695327287387891875)
                  ·
                    refine ⟨9218284042990931081837813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6145522695327287387891875 9218284042990931081837813)
                    ·
                      refine ⟨864214129030399788922295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9218284042990931081837813 864214129030399788922295)
                      ·
                        rfl

theorem cell23_1683051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 5].length) (baseStart_1683051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683051 prefixEnd_1683051 := by exact prefixLift 1683051
  have htrace : WordTrace (prefixWord ++ tailWord_1683051) baseStart_1683051 baseEnd_1683051 := by
    simpa [prefixWord, tailWord_1683051, baseEnd_1683051] using wordTrace_append hprefix tailTrace_1683051
  have hstable : (prefixWord ++ tailWord_1683051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683051).length < 2 ^ (prefixWord ++ tailWord_1683051).sum := by decide
  have hdescent : baseEnd_1683051 < baseStart_1683051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683058 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_1683058 : Nat := 118140960795 + 1683058 * 2 ^ 59
def prefixEnd_1683058 : Nat := 4983230072969 + 3 ^ 40 * 1683058 * 2
def baseEnd_1683058 : Nat := 288072574464993753844921

theorem tailTrace_1683058 : CollatzResearch.WordTrace tailWord_1683058 prefixEnd_1683058 288072574464993753844921 := by
  unfold tailWord_1683058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15346542084143946066742457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40924112224383856177979885 15346542084143946066742457)
  ·
    refine ⟨11509906563107959550056843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15346542084143946066742457 11509906563107959550056843)
    ·
      refine ⟨17264859844661939325085265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11509906563107959550056843 17264859844661939325085265)
      ·
        refine ⟨12948644883496454493813949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17264859844661939325085265 12948644883496454493813949)
        ·
          refine ⟨4855741831311170435180231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12948644883496454493813949 4855741831311170435180231)
          ·
            refine ⟨7283612746966755652770347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855741831311170435180231 7283612746966755652770347)
            ·
              refine ⟨10925419120450133479155521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7283612746966755652770347 10925419120450133479155521)
              ·
                refine ⟨8194064340337600109366641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10925419120450133479155521 8194064340337600109366641)
                ·
                  refine ⟨6145548255253200082024981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8194064340337600109366641 6145548255253200082024981)
                  ·
                    refine ⟨288072574464993753844921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6145548255253200082024981 288072574464993753844921)
                    ·
                      rfl

theorem cell23_1683058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_1683058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683058 prefixEnd_1683058 := by exact prefixLift 1683058
  have htrace : WordTrace (prefixWord ++ tailWord_1683058) baseStart_1683058 baseEnd_1683058 := by
    simpa [prefixWord, tailWord_1683058, baseEnd_1683058] using wordTrace_append hprefix tailTrace_1683058
  have hstable : (prefixWord ++ tailWord_1683058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683058).length < 2 ^ (prefixWord ++ tailWord_1683058).sum := by decide
  have hdescent : baseEnd_1683058 < baseStart_1683058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683082 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2]
def baseStart_1683082 : Nat := 118140960795 + 1683082 * 2 ^ 59
def prefixEnd_1683082 : Nat := 4983230072969 + 3 ^ 40 * 1683082 * 2
def baseEnd_1683082 : Nat := 864230046930689167634653

theorem tailTrace_1683082 : CollatzResearch.WordTrace tailWord_1683082 prefixEnd_1683082 864230046930689167634653 := by
  unfold tailWord_1683082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15346760922122209091460875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40924695792325890910562333 15346760922122209091460875)
  ·
    refine ⟨23020141383183313637191313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15346760922122209091460875 23020141383183313637191313)
    ·
      refine ⟨17265106037387485227893485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23020141383183313637191313 17265106037387485227893485)
      ·
        refine ⟨6474414764020306960460057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17265106037387485227893485 6474414764020306960460057)
        ·
          refine ⟨4855811073015230220345043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6474414764020306960460057 4855811073015230220345043)
          ·
            refine ⟨7283716609522845330517565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855811073015230220345043 7283716609522845330517565)
            ·
              refine ⟨2731393728571066998944087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7283716609522845330517565 2731393728571066998944087)
              ·
                refine ⟨4097090592856600498416131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731393728571066998944087 4097090592856600498416131)
                ·
                  refine ⟨6145635889284900747624197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097090592856600498416131 6145635889284900747624197)
                  ·
                    refine ⟨1152306729240918890179537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6145635889284900747624197 1152306729240918890179537)
                    ·
                      refine ⟨864230046930689167634653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152306729240918890179537 864230046930689167634653)
                      ·
                        rfl

theorem cell23_1683082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_1683082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683082 prefixEnd_1683082 := by exact prefixLift 1683082
  have htrace : WordTrace (prefixWord ++ tailWord_1683082) baseStart_1683082 baseEnd_1683082 := by
    simpa [prefixWord, tailWord_1683082, baseEnd_1683082] using wordTrace_append hprefix tailTrace_1683082
  have hstable : (prefixWord ++ tailWord_1683082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683082).length < 2 ^ (prefixWord ++ tailWord_1683082).sum := by decide
  have hdescent : baseEnd_1683082 < baseStart_1683082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683178 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 8]
def baseStart_1683178 : Nat := 118140960795 + 1683178 * 2 ^ 59
def prefixEnd_1683178 : Nat := 4983230072969 + 3 ^ 40 * 1683178 * 2
def baseEnd_1683178 : Nat := 96031037897057865781579

theorem tailTrace_1683178 : CollatzResearch.WordTrace tailWord_1683178 prefixEnd_1683178 96031037897057865781579 := by
  unfold tailWord_1683178
  simp only [CollatzResearch.WordTrace]
  refine ⟨15347636274035261190334547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40927030064094029840892125 15347636274035261190334547)
  ·
    refine ⟨23021454411052891785501821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15347636274035261190334547 23021454411052891785501821)
    ·
      refine ⟨8633045404144834419563183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23021454411052891785501821 8633045404144834419563183)
      ·
        refine ⟨12949568106217251629344775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8633045404144834419563183 12949568106217251629344775)
        ·
          refine ⟨19424352159325877444017163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12949568106217251629344775 19424352159325877444017163)
          ·
            refine ⟨29136528238988816166025745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19424352159325877444017163 29136528238988816166025745)
            ·
              refine ⟨21852396179241612124519309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29136528238988816166025745 21852396179241612124519309)
              ·
                refine ⟨8194648567215604546694741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21852396179241612124519309 8194648567215604546694741)
                ·
                  refine ⟨96031037897057865781579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8194648567215604546694741 96031037897057865781579)
                  ·
                    rfl

theorem cell23_1683178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_1683178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683178 prefixEnd_1683178 := by exact prefixLift 1683178
  have htrace : WordTrace (prefixWord ++ tailWord_1683178) baseStart_1683178 baseEnd_1683178 := by
    simpa [prefixWord, tailWord_1683178, baseEnd_1683178] using wordTrace_append hprefix tailTrace_1683178
  have hstable : (prefixWord ++ tailWord_1683178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683178).length < 2 ^ (prefixWord ++ tailWord_1683178).sum := by decide
  have hdescent : baseEnd_1683178 < baseStart_1683178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683232 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 4, 3, 2]
def baseStart_1683232 : Nat := 118140960795 + 1683232 * 2 ^ 59
def prefixEnd_1683232 : Nat := 4983230072969 + 3 ^ 40 * 1683232 * 2
def baseEnd_1683232 : Nat := 864307069028863580758963

theorem tailTrace_1683232 : CollatzResearch.WordTrace tailWord_1683232 prefixEnd_1683232 864307069028863580758963 := by
  unfold tailWord_1683232
  simp only [CollatzResearch.WordTrace]
  refine ⟨30696257318972705991901975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40928343091963607989202633 30696257318972705991901975)
  ·
    refine ⟨46044385978459058987852963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30696257318972705991901975 46044385978459058987852963)
    ·
      refine ⟨69066578967688588481779445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46044385978459058987852963 69066578967688588481779445)
      ·
        refine ⟨6474991778220805170166823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69066578967688588481779445 6474991778220805170166823)
        ·
          refine ⟨9712487667331207755250235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6474991778220805170166823 9712487667331207755250235)
          ·
            refine ⟨14568731500996811632875353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9712487667331207755250235 14568731500996811632875353)
            ·
              refine ⟨10926548625747608724656515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14568731500996811632875353 10926548625747608724656515)
              ·
                refine ⟨16389822938621413086984773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10926548625747608724656515 16389822938621413086984773)
                ·
                  refine ⟨3073091800991514953809645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16389822938621413086984773 3073091800991514953809645)
                  ·
                    refine ⟨1152409425371818107678617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3073091800991514953809645 1152409425371818107678617)
                    ·
                      refine ⟨864307069028863580758963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152409425371818107678617 864307069028863580758963)
                      ·
                        rfl

theorem cell23_1683232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_1683232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683232 prefixEnd_1683232 := by exact prefixLift 1683232
  have htrace : WordTrace (prefixWord ++ tailWord_1683232) baseStart_1683232 baseEnd_1683232 := by
    simpa [prefixWord, tailWord_1683232, baseEnd_1683232] using wordTrace_append hprefix tailTrace_1683232
  have hstable : (prefixWord ++ tailWord_1683232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683232).length < 2 ^ (prefixWord ++ tailWord_1683232).sum := by decide
  have hdescent : baseEnd_1683232 < baseStart_1683232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683282 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_1683282 : Nat := 118140960795 + 1683282 * 2 ^ 59
def prefixEnd_1683282 : Nat := 4983230072969 + 3 ^ 40 * 1683282 * 2
def baseEnd_1683282 : Nat := 864332743061588385133733

theorem tailTrace_1683282 : CollatzResearch.WordTrace tailWord_1683282 prefixEnd_1683282 864332743061588385133733 := by
  unfold tailWord_1683282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15348584571941067630781025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40929558858509513682082733 15348584571941067630781025)
  ·
    refine ⟨11511438428955800723085769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15348584571941067630781025 11511438428955800723085769)
    ·
      refine ⟨8633578821716850542314327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11511438428955800723085769 8633578821716850542314327)
      ·
        refine ⟨12950368232575275813471491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8633578821716850542314327 12950368232575275813471491)
        ·
          refine ⟨19425552348862913720207237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12950368232575275813471491 19425552348862913720207237)
          ·
            refine ⟨3642291065411796322538857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19425552348862913720207237 3642291065411796322538857)
            ·
              refine ⟨2731718299058847241904143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3642291065411796322538857 2731718299058847241904143)
              ·
                refine ⟨4097577448588270862856215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731718299058847241904143 4097577448588270862856215)
                ·
                  refine ⟨6146366172882406294284323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097577448588270862856215 6146366172882406294284323)
                  ·
                    refine ⟨9219549259323609441426485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6146366172882406294284323 9219549259323609441426485)
                    ·
                      refine ⟨864332743061588385133733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9219549259323609441426485 864332743061588385133733)
                      ·
                        rfl

theorem cell23_1683282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_1683282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683282 prefixEnd_1683282 := by exact prefixLift 1683282
  have htrace : WordTrace (prefixWord ++ tailWord_1683282) baseStart_1683282 baseEnd_1683282 := by
    simpa [prefixWord, tailWord_1683282, baseEnd_1683282] using wordTrace_append hprefix tailTrace_1683282
  have hstable : (prefixWord ++ tailWord_1683282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683282).length < 2 ^ (prefixWord ++ tailWord_1683282).sum := by decide
  have hdescent : baseEnd_1683282 < baseStart_1683282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683285 : List Nat := [1, 3, 2, 2, 2, 4, 9]
def baseStart_1683285 : Nat := 118140960795 + 1683285 * 2 ^ 59
def prefixEnd_1683285 : Nat := 4983230072969 + 3 ^ 40 * 1683285 * 2
def baseEnd_1683285 : Nat := 10670793623500640412299

theorem tailTrace_1683285 : CollatzResearch.WordTrace tailWord_1683285 prefixEnd_1683285 10670793623500640412299 := by
  unfold tailWord_1683285
  simp only [CollatzResearch.WordTrace]
  refine ⟨61394447706753402035483309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40929631804502268023655539 61394447706753402035483309)
  ·
    refine ⟨23022917890032525763306241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61394447706753402035483309 23022917890032525763306241)
    ·
      refine ⟨17267188417524394322479681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23022917890032525763306241 17267188417524394322479681)
      ·
        refine ⟨12950391313143295741859761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17267188417524394322479681 12950391313143295741859761)
        ·
          refine ⟨9712793484857471806394821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12950391313143295741859761 9712793484857471806394821)
          ·
            refine ⟨1821148778410775963699029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9712793484857471806394821 1821148778410775963699029)
            ·
              refine ⟨10670793623500640412299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1821148778410775963699029 10670793623500640412299)
              ·
                rfl

theorem cell23_1683285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 9].length) (baseStart_1683285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683285 prefixEnd_1683285 := by exact prefixLift 1683285
  have htrace : WordTrace (prefixWord ++ tailWord_1683285) baseStart_1683285 baseEnd_1683285 := by
    simpa [prefixWord, tailWord_1683285, baseEnd_1683285] using wordTrace_append hprefix tailTrace_1683285
  have hstable : (prefixWord ++ tailWord_1683285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683285).length < 2 ^ (prefixWord ++ tailWord_1683285).sum := by decide
  have hdescent : baseEnd_1683285 < baseStart_1683285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683296 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 3, 2, 2]
def baseStart_1683296 : Nat := 118140960795 + 1683296 * 2 ^ 59
def prefixEnd_1683296 : Nat := 4983230072969 + 3 ^ 40 * 1683296 * 2
def baseEnd_1683296 : Nat := 864339931790751330358669

theorem tailTrace_1683296 : CollatzResearch.WordTrace tailWord_1683296 prefixEnd_1683296 864339931790751330358669 := by
  unfold tailWord_1683296
  simp only [CollatzResearch.WordTrace]
  refine ⟨30697424454856775457066871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40929899273142367276089161 30697424454856775457066871)
  ·
    refine ⟨46046136682285163185600307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30697424454856775457066871 46046136682285163185600307)
    ·
      refine ⟨69069205023427744778400461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46046136682285163185600307 69069205023427744778400461)
      ·
        refine ⟨25900951883785404291900173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69069205023427744778400461 25900951883785404291900173)
        ·
          refine ⟨9712856956419526609462565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25900951883785404291900173 9712856956419526609462565)
          ·
            refine ⟨1821160679328661239274231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9712856956419526609462565 1821160679328661239274231)
            ·
              refine ⟨2731741018992991858911347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821160679328661239274231 2731741018992991858911347)
              ·
                refine ⟨4097611528489487788367021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731741018992991858911347 4097611528489487788367021)
                ·
                  refine ⟨1536604323183557920637633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4097611528489487788367021 1536604323183557920637633)
                  ·
                    refine ⟨1152453242387668440478225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1536604323183557920637633 1152453242387668440478225)
                    ·
                      refine ⟨864339931790751330358669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152453242387668440478225 864339931790751330358669)
                      ·
                        rfl

theorem cell23_1683296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_1683296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683296 prefixEnd_1683296 := by exact prefixLift 1683296
  have htrace : WordTrace (prefixWord ++ tailWord_1683296) baseStart_1683296 baseEnd_1683296 := by
    simpa [prefixWord, tailWord_1683296, baseEnd_1683296] using wordTrace_append hprefix tailTrace_1683296
  have hstable : (prefixWord ++ tailWord_1683296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683296).length < 2 ^ (prefixWord ++ tailWord_1683296).sum := by decide
  have hdescent : baseEnd_1683296 < baseStart_1683296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683306 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1683306 : Nat := 118140960795 + 1683306 * 2 ^ 59
def prefixEnd_1683306 : Nat := 4983230072969 + 3 ^ 40 * 1683306 * 2
def baseEnd_1683306 : Nat := 288115022199098763744541

theorem tailTrace_1683306 : CollatzResearch.WordTrace tailWord_1683306 prefixEnd_1683306 288115022199098763744541 := by
  unfold tailWord_1683306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15348803409919330655499443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40930142426451548414665181 15348803409919330655499443)
  ·
    refine ⟨23023205114878995983249165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15348803409919330655499443 23023205114878995983249165)
    ·
      refine ⟨8633701918079623493718437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23023205114878995983249165 8633701918079623493718437)
      ·
        refine ⟨1618819109639929405072207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8633701918079623493718437 1618819109639929405072207)
        ·
          refine ⟨2428228664459894107608311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618819109639929405072207 2428228664459894107608311)
          ·
            refine ⟨3642342996689841161412467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428228664459894107608311 3642342996689841161412467)
            ·
              refine ⟨5463514495034761742118701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3642342996689841161412467 5463514495034761742118701)
              ·
                refine ⟨2048817935638035653294513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5463514495034761742118701 2048817935638035653294513)
                ·
                  refine ⟨1536613451728526739970885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2048817935638035653294513 1536613451728526739970885)
                  ·
                    refine ⟨288115022199098763744541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1536613451728526739970885 288115022199098763744541)
                    ·
                      rfl

theorem cell23_1683306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1683306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683306 prefixEnd_1683306 := by exact prefixLift 1683306
  have htrace : WordTrace (prefixWord ++ tailWord_1683306) baseStart_1683306 baseEnd_1683306 := by
    simpa [prefixWord, tailWord_1683306, baseEnd_1683306] using wordTrace_append hprefix tailTrace_1683306
  have hstable : (prefixWord ++ tailWord_1683306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683306).length < 2 ^ (prefixWord ++ tailWord_1683306).sum := by decide
  have hdescent : baseEnd_1683306 < baseStart_1683306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683346 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1683346 : Nat := 118140960795 + 1683346 * 2 ^ 59
def prefixEnd_1683346 : Nat := 4983230072969 + 3 ^ 40 * 1683346 * 2
def baseEnd_1683346 : Nat := 864365605823476134733439

theorem tailTrace_1683346 : CollatzResearch.WordTrace tailWord_1683346 prefixEnd_1683346 864365605823476134733439 := by
  unfold tailWord_1683346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15349168139883102363363473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40931115039688272968969261 15349168139883102363363473)
  ·
    refine ⟨11511876104912326772522605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15349168139883102363363473 11511876104912326772522605)
    ·
      refine ⟨4316953539342122539695977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11511876104912326772522605 4316953539342122539695977)
      ·
        refine ⟨3237715154506591904771983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4316953539342122539695977 3237715154506591904771983)
        ·
          refine ⟨4856572731759887857157975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3237715154506591904771983 4856572731759887857157975)
          ·
            refine ⟨7284859097639831785736963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4856572731759887857157975 7284859097639831785736963)
            ·
              refine ⟨10927288646459747678605445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7284859097639831785736963 10927288646459747678605445)
              ·
                refine ⟨2048866621211202689738521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10927288646459747678605445 2048866621211202689738521)
                ·
                  refine ⟨1536649965908402017303891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2048866621211202689738521 1536649965908402017303891)
                  ·
                    refine ⟨2304974948862603025955837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1536649965908402017303891 2304974948862603025955837)
                    ·
                      refine ⟨864365605823476134733439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2304974948862603025955837 864365605823476134733439)
                      ·
                        rfl

theorem cell23_1683346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1683346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683346 prefixEnd_1683346 := by exact prefixLift 1683346
  have htrace : WordTrace (prefixWord ++ tailWord_1683346) baseStart_1683346 baseEnd_1683346 := by
    simpa [prefixWord, tailWord_1683346, baseEnd_1683346] using wordTrace_append hprefix tailTrace_1683346
  have hstable : (prefixWord ++ tailWord_1683346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683346).length < 2 ^ (prefixWord ++ tailWord_1683346).sum := by decide
  have hdescent : baseEnd_1683346 < baseStart_1683346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683375 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 7]
def baseStart_1683375 : Nat := 118140960795 + 1683375 * 2 ^ 59
def prefixEnd_1683375 : Nat := 4983230072969 + 3 ^ 40 * 1683375 * 2
def baseEnd_1683375 : Nat := 96042277418050724585645

theorem tailTrace_1683375 : CollatzResearch.WordTrace tailWord_1683375 prefixEnd_1683375 96042277418050724585645 := by
  unfold tailWord_1683375
  simp only [CollatzResearch.WordTrace]
  refine ⟨61397730276427347406259579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40931820184284898270839719 61397730276427347406259579)
  ·
    refine ⟨92096595414641021109389369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61397730276427347406259579 92096595414641021109389369)
    ·
      refine ⟨69072446560980765832042027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92096595414641021109389369 69072446560980765832042027)
      ·
        refine ⟨103608669841471148748063041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69072446560980765832042027 103608669841471148748063041)
        ·
          refine ⟨77706502381103361561047281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103608669841471148748063041 77706502381103361561047281)
          ·
            refine ⟨58279876785827521170785461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77706502381103361561047281 58279876785827521170785461)
            ·
              refine ⟨5463738448671330109761137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58279876785827521170785461 5463738448671330109761137)
              ·
                refine ⟨4097803836503497582320853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5463738448671330109761137 4097803836503497582320853)
                ·
                  refine ⟨96042277418050724585645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4097803836503497582320853 96042277418050724585645)
                  ·
                    rfl

theorem cell23_1683375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 7].length) (baseStart_1683375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683375 prefixEnd_1683375 := by exact prefixLift 1683375
  have htrace : WordTrace (prefixWord ++ tailWord_1683375) baseStart_1683375 baseEnd_1683375 := by
    simpa [prefixWord, tailWord_1683375, baseEnd_1683375] using wordTrace_append hprefix tailTrace_1683375
  have hstable : (prefixWord ++ tailWord_1683375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683375).length < 2 ^ (prefixWord ++ tailWord_1683375).sum := by decide
  have hdescent : baseEnd_1683375 < baseStart_1683375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683402 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_1683402 : Nat := 118140960795 + 1683402 * 2 ^ 59
def prefixEnd_1683402 : Nat := 4983230072969 + 3 ^ 40 * 1683402 * 2
def baseEnd_1683402 : Nat := 864394360740127915633181

theorem tailTrace_1683402 : CollatzResearch.WordTrace tailWord_1683402 prefixEnd_1683402 864394360740127915633181 := by
  unfold tailWord_1683402
  simp only [CollatzResearch.WordTrace]
  refine ⟨15349678761832382754373115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40932476698219687344994973 15349678761832382754373115)
  ·
    refine ⟨23024518142748574131559673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15349678761832382754373115 23024518142748574131559673)
    ·
      refine ⟨17268388607061430598669755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23024518142748574131559673 17268388607061430598669755)
      ·
        refine ⟨25902582910592145898004633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17268388607061430598669755 25902582910592145898004633)
        ·
          refine ⟨19426937182944109423503475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25902582910592145898004633 19426937182944109423503475)
          ·
            refine ⟨29140405774416164135255213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19426937182944109423503475 29140405774416164135255213)
            ·
              refine ⟨10927652165406061550720705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29140405774416164135255213 10927652165406061550720705)
              ·
                refine ⟨8195739124054546163040529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10927652165406061550720705 8195739124054546163040529)
                ·
                  refine ⟨6146804343040909622280397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8195739124054546163040529 6146804343040909622280397)
                  ·
                    refine ⟨2305051628640341108355149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6146804343040909622280397 2305051628640341108355149)
                    ·
                      refine ⟨864394360740127915633181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2305051628640341108355149 864394360740127915633181)
                      ·
                        rfl

theorem cell23_1683402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_1683402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683402 prefixEnd_1683402 := by exact prefixLift 1683402
  have htrace : WordTrace (prefixWord ++ tailWord_1683402) baseStart_1683402 baseEnd_1683402 := by
    simpa [prefixWord, tailWord_1683402, baseEnd_1683402] using wordTrace_append hprefix tailTrace_1683402
  have hstable : (prefixWord ++ tailWord_1683402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683402).length < 2 ^ (prefixWord ++ tailWord_1683402).sum := by decide
  have hdescent : baseEnd_1683402 < baseStart_1683402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683415 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1683415 : Nat := 118140960795 + 1683415 * 2 ^ 59
def prefixEnd_1683415 : Nat := 4983230072969 + 3 ^ 40 * 1683415 * 2
def baseEnd_1683415 : Nat := 864401035988636364770621

theorem tailTrace_1683415 : CollatzResearch.WordTrace tailWord_1683415 prefixEnd_1683415 864401035988636364770621 := by
  unfold tailWord_1683415
  simp only [CollatzResearch.WordTrace]
  refine ⟨61399189196282434237715699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40932792797521622825143799 61399189196282434237715699)
  ·
    refine ⟨92098783794423651356573549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61399189196282434237715699 92098783794423651356573549)
    ·
      refine ⟨34537043922908869258715081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92098783794423651356573549 34537043922908869258715081)
      ·
        refine ⟨25902782942181651944036311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34537043922908869258715081 25902782942181651944036311)
        ·
          refine ⟨38854174413272477916054467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25902782942181651944036311 38854174413272477916054467)
          ·
            refine ⟨58281261619908716874081701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38854174413272477916054467 58281261619908716874081701)
            ·
              refine ⟨10927736553732884413890319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58281261619908716874081701 10927736553732884413890319)
              ·
                refine ⟨16391604830599326620835479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10927736553732884413890319 16391604830599326620835479)
                ·
                  refine ⟨24587407245898989931253219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16391604830599326620835479 24587407245898989931253219)
                  ·
                    refine ⟨36881110868848484896879829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24587407245898989931253219 36881110868848484896879829)
                    ·
                      refine ⟨864401035988636364770621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36881110868848484896879829 864401035988636364770621)
                      ·
                        rfl

theorem cell23_1683415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1683415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683415 prefixEnd_1683415 := by exact prefixLift 1683415
  have htrace : WordTrace (prefixWord ++ tailWord_1683415) baseStart_1683415 baseEnd_1683415 := by
    simpa [prefixWord, tailWord_1683415, baseEnd_1683415] using wordTrace_append hprefix tailTrace_1683415
  have hstable : (prefixWord ++ tailWord_1683415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683415).length < 2 ^ (prefixWord ++ tailWord_1683415).sum := by decide
  have hdescent : baseEnd_1683415 < baseStart_1683415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683455 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_1683455 : Nat := 118140960795 + 1683455 * 2 ^ 59
def prefixEnd_1683455 : Nat := 4983230072969 + 3 ^ 40 * 1683455 * 2
def baseEnd_1683455 : Nat := 864421575214816208270437

theorem tailTrace_1683455 : CollatzResearch.WordTrace tailWord_1683455 prefixEnd_1683455 864421575214816208270437 := by
  unfold tailWord_1683455
  simp only [CollatzResearch.WordTrace]
  refine ⟨61400648116137521069171819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40933765410758347379447879 61400648116137521069171819)
  ·
    refine ⟨92100972174206281603757729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61400648116137521069171819 92100972174206281603757729)
    ·
      refine ⟨69075729130654711202818297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92100972174206281603757729 69075729130654711202818297)
      ·
        refine ⟨51806796847991033402113723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69075729130654711202818297 51806796847991033402113723)
        ·
          refine ⟨77710195271986550103170585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51806796847991033402113723 77710195271986550103170585)
          ·
            refine ⟨58282646453989912577377939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77710195271986550103170585 58282646453989912577377939)
            ·
              refine ⟨87423969680984868866066909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58282646453989912577377939 87423969680984868866066909)
              ·
                refine ⟨32783988630369325824775091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87423969680984868866066909 32783988630369325824775091)
                ·
                  refine ⟨49175982945553988737162637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32783988630369325824775091 49175982945553988737162637)
                  ·
                    refine ⟨18440993604582745776435989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49175982945553988737162637 18440993604582745776435989)
                    ·
                      refine ⟨864421575214816208270437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18440993604582745776435989 864421575214816208270437)
                      ·
                        rfl

theorem cell23_1683455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_1683455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683455 prefixEnd_1683455 := by exact prefixLift 1683455
  have htrace : WordTrace (prefixWord ++ tailWord_1683455) baseStart_1683455 baseEnd_1683455 := by
    simpa [prefixWord, tailWord_1683455, baseEnd_1683455] using wordTrace_append hprefix tailTrace_1683455
  have hstable : (prefixWord ++ tailWord_1683455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683455).length < 2 ^ (prefixWord ++ tailWord_1683455).sum := by decide
  have hdescent : baseEnd_1683455 < baseStart_1683455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683559 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 4, 4]
def baseStart_1683559 : Nat := 118140960795 + 1683559 * 2 ^ 59
def prefixEnd_1683559 : Nat := 4983230072969 + 3 ^ 40 * 1683559 * 2
def baseEnd_1683559 : Nat := 288158325734294600456653

theorem tailTrace_1683559 : CollatzResearch.WordTrace tailWord_1683559 prefixEnd_1683559 288158325734294600456653 := by
  unfold tailWord_1683559
  simp only [CollatzResearch.WordTrace]
  refine ⟨61404441307760746830957731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40936294205173831220638487 61404441307760746830957731)
  ·
    refine ⟨92106661961641120246436597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61404441307760746830957731 92106661961641120246436597)
    ·
      refine ⟨8634999558903855023103431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92106661961641120246436597 8634999558903855023103431)
      ·
        refine ⟨12952499338355782534655147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8634999558903855023103431 12952499338355782534655147)
        ·
          refine ⟨19428749007533673801982721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12952499338355782534655147 19428749007533673801982721)
          ·
            refine ⟨14571561755650255351487041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19428749007533673801982721 14571561755650255351487041)
            ·
              refine ⟨10928671316737691513615281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14571561755650255351487041 10928671316737691513615281)
              ·
                refine ⟨8196503487553268635211461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10928671316737691513615281 8196503487553268635211461)
                ·
                  refine ⟨1536844403916237869102149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8196503487553268635211461 1536844403916237869102149)
                  ·
                    refine ⟨288158325734294600456653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1536844403916237869102149 288158325734294600456653)
                    ·
                      rfl

theorem cell23_1683559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_1683559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683559 prefixEnd_1683559 := by exact prefixLift 1683559
  have htrace : WordTrace (prefixWord ++ tailWord_1683559) baseStart_1683559 baseEnd_1683559 := by
    simpa [prefixWord, tailWord_1683559, baseEnd_1683559] using wordTrace_append hprefix tailTrace_1683559
  have hstable : (prefixWord ++ tailWord_1683559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683559).length < 2 ^ (prefixWord ++ tailWord_1683559).sum := by decide
  have hdescent : baseEnd_1683559 < baseStart_1683559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683566 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1683566 : Nat := 118140960795 + 1683566 * 2 ^ 59
def prefixEnd_1683566 : Nat := 4983230072969 + 3 ^ 40 * 1683566 * 2
def baseEnd_1683566 : Nat := 864478571567465273982427

theorem tailTrace_1683566 : CollatzResearch.WordTrace tailWord_1683566 prefixEnd_1683566 864478571567465273982427 := by
  unfold tailWord_1683566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7675587077341923378307819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40936464412490258017641701 7675587077341923378307819)
  ·
    refine ⟨11513380616012885067461729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7675587077341923378307819 11513380616012885067461729)
    ·
      refine ⟨8635035462009663800596297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11513380616012885067461729 8635035462009663800596297)
      ·
        refine ⟨6476276596507247850447223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8635035462009663800596297 6476276596507247850447223)
        ·
          refine ⟨9714414894760871775670835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6476276596507247850447223 9714414894760871775670835)
          ·
            refine ⟨14571622342141307663506253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9714414894760871775670835 14571622342141307663506253)
            ·
              refine ⟨5464358378302990373814845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14571622342141307663506253 5464358378302990373814845)
              ·
                refine ⟨2049134391863621390180567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5464358378302990373814845 2049134391863621390180567)
                ·
                  refine ⟨3073701587795432085270851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049134391863621390180567 3073701587795432085270851)
                  ·
                    refine ⟨4610552381693148127906277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3073701587795432085270851 4610552381693148127906277)
                    ·
                      refine ⟨864478571567465273982427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4610552381693148127906277 864478571567465273982427)
                      ·
                        rfl

theorem cell23_1683566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1683566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683566 prefixEnd_1683566 := by exact prefixLift 1683566
  have htrace : WordTrace (prefixWord ++ tailWord_1683566) baseStart_1683566 baseEnd_1683566 := by
    simpa [prefixWord, tailWord_1683566, baseEnd_1683566] using wordTrace_append hprefix tailTrace_1683566
  have hstable : (prefixWord ++ tailWord_1683566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683566).length < 2 ^ (prefixWord ++ tailWord_1683566).sum := by decide
  have hdescent : baseEnd_1683566 < baseStart_1683566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683609 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 2, 7, 2]
def baseStart_1683609 : Nat := 118140960795 + 1683609 * 2 ^ 59
def prefixEnd_1683609 : Nat := 4983230072969 + 3 ^ 40 * 1683609 * 2
def baseEnd_1683609 : Nat := 864500651235608605744729

theorem tailTrace_1683609 : CollatzResearch.WordTrace tailWord_1683609 prefixEnd_1683609 864500651235608605744729 := by
  unfold tailWord_1683609
  simp only [CollatzResearch.WordTrace]
  refine ⟨61406264957579605370277881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40937509971719736913518587 61406264957579605370277881)
  ·
    refine ⟨46054698718184704027708411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61406264957579605370277881 46054698718184704027708411)
    ·
      refine ⟨69082048077277056041562617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46054698718184704027708411 69082048077277056041562617)
      ·
        refine ⟨51811536057957792031171963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69082048077277056041562617 51811536057957792031171963)
        ·
          refine ⟨77717304086936688046757945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51811536057957792031171963 77717304086936688046757945)
          ·
            refine ⟨58287978065202516035068459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77717304086936688046757945 58287978065202516035068459)
            ·
              refine ⟨87431967097803774052602689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58287978065202516035068459 87431967097803774052602689)
              ·
                refine ⟨65573975323352830539452017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87431967097803774052602689 65573975323352830539452017)
                ·
                  refine ⟨49180481492514622904589013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65573975323352830539452017 49180481492514622904589013)
                  ·
                    refine ⟨1152667534980811474326305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49180481492514622904589013 1152667534980811474326305)
                    ·
                      refine ⟨864500651235608605744729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152667534980811474326305 864500651235608605744729)
                      ·
                        rfl

theorem cell23_1683609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_1683609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683609 prefixEnd_1683609 := by exact prefixLift 1683609
  have htrace : WordTrace (prefixWord ++ tailWord_1683609) baseStart_1683609 baseEnd_1683609 := by
    simpa [prefixWord, tailWord_1683609, baseEnd_1683609] using wordTrace_append hprefix tailTrace_1683609
  have hstable : (prefixWord ++ tailWord_1683609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683609).length < 2 ^ (prefixWord ++ tailWord_1683609).sum := by decide
  have hdescent : baseEnd_1683609 < baseStart_1683609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683616 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 4, 1, 3]
def baseStart_1683616 : Nat := 118140960795 + 1683616 * 2 ^ 59
def prefixEnd_1683616 : Nat := 4983230072969 + 3 ^ 40 * 1683616 * 2
def baseEnd_1683616 : Nat := 864504245600190078357197

theorem tailTrace_1683616 : CollatzResearch.WordTrace tailWord_1683616 prefixEnd_1683616 864504245600190078357197 := by
  unfold tailWord_1683616
  simp only [CollatzResearch.WordTrace]
  refine ⟨30703260134277122782891351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40937680179036163710521801 30703260134277122782891351)
  ·
    refine ⟨46054890201415684174337027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30703260134277122782891351 46054890201415684174337027)
    ·
      refine ⟨69082335302123526261505541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46054890201415684174337027 69082335302123526261505541)
      ·
        refine ⟨12952937869148161174032289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69082335302123526261505541 12952937869148161174032289)
        ·
          refine ⟨9714703401861120880524217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12952937869148161174032289 9714703401861120880524217)
          ·
            refine ⟨7286027551395840660393163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9714703401861120880524217 7286027551395840660393163)
            ·
              refine ⟨10929041327093760990589745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286027551395840660393163 10929041327093760990589745)
              ·
                refine ⟨8196780995320320742942309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10929041327093760990589745 8196780995320320742942309)
                ·
                  refine ⟨1536896436622560139301683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8196780995320320742942309 1536896436622560139301683)
                  ·
                    refine ⟨2305344654933840208952525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1536896436622560139301683 2305344654933840208952525)
                    ·
                      refine ⟨864504245600190078357197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2305344654933840208952525 864504245600190078357197)
                      ·
                        rfl

theorem cell23_1683616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_1683616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683616 prefixEnd_1683616 := by exact prefixLift 1683616
  have htrace : WordTrace (prefixWord ++ tailWord_1683616) baseStart_1683616 baseEnd_1683616 := by
    simpa [prefixWord, tailWord_1683616, baseEnd_1683616] using wordTrace_append hprefix tailTrace_1683616
  have hstable : (prefixWord ++ tailWord_1683616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683616).length < 2 ^ (prefixWord ++ tailWord_1683616).sum := by decide
  have hdescent : baseEnd_1683616 < baseStart_1683616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683617 : List Nat := [1, 2, 3, 3, 1, 4, 1, 3, 1, 2, 2]
def baseStart_1683617 : Nat := 118140960795 + 1683617 * 2 ^ 59
def prefixEnd_1683617 : Nat := 4983230072969 + 3 ^ 40 * 1683617 * 2
def baseEnd_1683617 : Nat := 864504759080844574444693

theorem tailTrace_1683617 : CollatzResearch.WordTrace tailWord_1683617 prefixEnd_1683617 864504759080844574444693 := by
  unfold tailWord_1683617
  simp only [CollatzResearch.WordTrace]
  refine ⟨61406556741550622736569105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40937704494367081824379403 61406556741550622736569105)
  ·
    refine ⟨46054917556162967052426829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61406556741550622736569105 46054917556162967052426829)
    ·
      refine ⟨17270594083561112644660061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46054917556162967052426829 17270594083561112644660061)
      ·
        refine ⟨6476472781335417241747523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17270594083561112644660061 6476472781335417241747523)
        ·
          refine ⟨9714709172003125862621285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6476472781335417241747523 9714709172003125862621285)
          ·
            refine ⟨1821507969750586099241491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9714709172003125862621285 1821507969750586099241491)
            ·
              refine ⟨2732261954625879148862237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821507969750586099241491 2732261954625879148862237)
              ·
                refine ⟨1024598232984704680823339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2732261954625879148862237 1024598232984704680823339)
                ·
                  refine ⟨1536897349477057021235009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024598232984704680823339 1536897349477057021235009)
                  ·
                    refine ⟨1152673012107792765926257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1536897349477057021235009 1152673012107792765926257)
                    ·
                      refine ⟨864504759080844574444693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152673012107792765926257 864504759080844574444693)
                      ·
                        rfl

theorem cell23_1683617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_1683617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683617 prefixEnd_1683617 := by exact prefixLift 1683617
  have htrace : WordTrace (prefixWord ++ tailWord_1683617) baseStart_1683617 baseEnd_1683617 := by
    simpa [prefixWord, tailWord_1683617, baseEnd_1683617] using wordTrace_append hprefix tailTrace_1683617
  have hstable : (prefixWord ++ tailWord_1683617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683617).length < 2 ^ (prefixWord ++ tailWord_1683617).sum := by decide
  have hdescent : baseEnd_1683617 < baseStart_1683617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683656 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 1, 4, 2]
def baseStart_1683656 : Nat := 118140960795 + 1683656 * 2 ^ 59
def prefixEnd_1683656 : Nat := 4983230072969 + 3 ^ 40 * 1683656 * 2
def baseEnd_1683656 : Nat := 864524784826369921857013

theorem tailTrace_1683656 : CollatzResearch.WordTrace tailWord_1683656 prefixEnd_1683656 864524784826369921857013 := by
  unfold tailWord_1683656
  simp only [CollatzResearch.WordTrace]
  refine ⟨30703989594204666198619411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40938652792272888264825881 30703989594204666198619411)
  ·
    refine ⟨46055984391306999297929117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30703989594204666198619411 46055984391306999297929117)
    ·
      refine ⟨17270994146740124736723419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46055984391306999297929117 17270994146740124736723419)
      ·
        refine ⟨25906491220110187105085129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17270994146740124736723419 25906491220110187105085129)
        ·
          refine ⟨19429868415082640328813847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25906491220110187105085129 19429868415082640328813847)
          ·
            refine ⟨29144802622623960493220771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19429868415082640328813847 29144802622623960493220771)
            ·
              refine ⟨43717203933935940739831157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29144802622623960493220771 43717203933935940739831157)
              ·
                refine ⟨4098487868806494444359171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43717203933935940739831157 4098487868806494444359171)
                ·
                  refine ⟨6147731803209741666538757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4098487868806494444359171 6147731803209741666538757)
                  ·
                    refine ⟨1152699713101826562476017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6147731803209741666538757 1152699713101826562476017)
                    ·
                      refine ⟨864524784826369921857013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152699713101826562476017 864524784826369921857013)
                      ·
                        rfl

theorem cell23_1683656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_1683656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683656 prefixEnd_1683656 := by exact prefixLift 1683656
  have htrace : WordTrace (prefixWord ++ tailWord_1683656) baseStart_1683656 baseEnd_1683656 := by
    simpa [prefixWord, tailWord_1683656, baseEnd_1683656] using wordTrace_append hprefix tailTrace_1683656
  have hstable : (prefixWord ++ tailWord_1683656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683656).length < 2 ^ (prefixWord ++ tailWord_1683656).sum := by decide
  have hdescent : baseEnd_1683656 < baseStart_1683656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683660 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1683660 : Nat := 118140960795 + 1683660 * 2 ^ 59
def prefixEnd_1683660 : Nat := 4983230072969 + 3 ^ 40 * 1683660 * 2
def baseEnd_1683660 : Nat := 864526838748987906206995

theorem tailTrace_1683660 : CollatzResearch.WordTrace tailWord_1683660 prefixEnd_1683660 864526838748987906206995 := by
  unfold tailWord_1683660
  simp only [CollatzResearch.WordTrace]
  refine ⟨30704062540197420540192217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40938750053596560720256289 30704062540197420540192217)
  ·
    refine ⟨23028046905148065405144163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30704062540197420540192217 23028046905148065405144163)
    ·
      refine ⟨34542070357722098107716245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23028046905148065405144163 34542070357722098107716245)
      ·
        refine ⟨1619159548018223348799199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34542070357722098107716245 1619159548018223348799199)
        ·
          refine ⟨2428739322027335023198799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619159548018223348799199 2428739322027335023198799)
          ·
            refine ⟨3643108983041002534798199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428739322027335023198799 3643108983041002534798199)
            ·
              refine ⟨5464663474561503802197299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643108983041002534798199 5464663474561503802197299)
              ·
                refine ⟨8196995211842255703295949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5464663474561503802197299 8196995211842255703295949)
                ·
                  refine ⟨3073873204440845888735981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8196995211842255703295949 3073873204440845888735981)
                  ·
                    refine ⟨1152702451665317208275993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3073873204440845888735981 1152702451665317208275993)
                    ·
                      refine ⟨864526838748987906206995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152702451665317208275993 864526838748987906206995)
                      ·
                        rfl

theorem cell23_1683660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1683660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683660 prefixEnd_1683660 := by exact prefixLift 1683660
  have htrace : WordTrace (prefixWord ++ tailWord_1683660) baseStart_1683660 baseEnd_1683660 := by
    simpa [prefixWord, tailWord_1683660, baseEnd_1683660] using wordTrace_append hprefix tailTrace_1683660
  have hstable : (prefixWord ++ tailWord_1683660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683660).length < 2 ^ (prefixWord ++ tailWord_1683660).sum := by decide
  have hdescent : baseEnd_1683660 < baseStart_1683660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683677 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1683677 : Nat := 118140960795 + 1683677 * 2 ^ 59
def prefixEnd_1683677 : Nat := 4983230072969 + 3 ^ 40 * 1683677 * 2
def baseEnd_1683677 : Nat := 864535567920114339694417

theorem tailTrace_1683677 : CollatzResearch.WordTrace tailWord_1683677 prefixEnd_1683677 864535567920114339694417 := by
  unfold tailWord_1683677
  simp only [CollatzResearch.WordTrace]
  refine ⟨61408745121333252983753285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40939163414222168655835523 61408745121333252983753285)
  ·
    refine ⟨11514139710249984934453741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61408745121333252983753285 11514139710249984934453741)
    ·
      refine ⟨4317802391343744350420153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11514139710249984934453741 4317802391343744350420153)
      ·
        refine ⟨3238351793507808262815115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4317802391343744350420153 3238351793507808262815115)
        ·
          refine ⟨4857527690261712394222673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238351793507808262815115 4857527690261712394222673)
          ·
            refine ⟨3643145767696284295667005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4857527690261712394222673 3643145767696284295667005)
            ·
              refine ⟨1366179662886106610875127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3643145767696284295667005 1366179662886106610875127)
              ·
                refine ⟨2049269494329159916312691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366179662886106610875127 2049269494329159916312691)
                ·
                  refine ⟨3073904241493739874469037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049269494329159916312691 3073904241493739874469037)
                  ·
                    refine ⟨1152714090560152452925889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3073904241493739874469037 1152714090560152452925889)
                    ·
                      refine ⟨864535567920114339694417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152714090560152452925889 864535567920114339694417)
                      ·
                        rfl

theorem cell23_1683677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1683677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683677 prefixEnd_1683677 := by exact prefixLift 1683677
  have htrace : WordTrace (prefixWord ++ tailWord_1683677) baseStart_1683677 baseEnd_1683677 := by
    simpa [prefixWord, tailWord_1683677, baseEnd_1683677] using wordTrace_append hprefix tailTrace_1683677
  have hstable : (prefixWord ++ tailWord_1683677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683677).length < 2 ^ (prefixWord ++ tailWord_1683677).sum := by decide
  have hdescent : baseEnd_1683677 < baseStart_1683677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683689 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 4, 3, 3]
def baseStart_1683689 : Nat := 118140960795 + 1683689 * 2 ^ 59
def prefixEnd_1683689 : Nat := 4983230072969 + 3 ^ 40 * 1683689 * 2
def baseEnd_1683689 : Nat := 864541729687968292744361

theorem tailTrace_1683689 : CollatzResearch.WordTrace tailWord_1683689 prefixEnd_1683689 864541729687968292744361 := by
  unfold tailWord_1683689
  simp only [CollatzResearch.WordTrace]
  refine ⟨61409182797289779033190121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40939455198193186022126747 61409182797289779033190121)
  ·
    refine ⟨46056887097967334274892591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61409182797289779033190121 46056887097967334274892591)
    ·
      refine ⟨69085330646951001412338887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46056887097967334274892591 69085330646951001412338887)
      ·
        refine ⟨103627995970426502118508331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69085330646951001412338887 103627995970426502118508331)
        ·
          refine ⟨155441993955639753177762497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103627995970426502118508331 155441993955639753177762497)
          ·
            refine ⟨116581495466729814883321873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155441993955639753177762497 116581495466729814883321873)
            ·
              refine ⟨87436121600047361162491405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116581495466729814883321873 87436121600047361162491405)
              ·
                refine ⟨32788545600017760435934277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87436121600047361162491405 32788545600017760435934277)
                ·
                  refine ⟨6147852300003330081737677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32788545600017760435934277 6147852300003330081737677)
                  ·
                    refine ⟨2305444612501248780651629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6147852300003330081737677 2305444612501248780651629)
                    ·
                      refine ⟨864541729687968292744361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2305444612501248780651629 864541729687968292744361)
                      ·
                        rfl

theorem cell23_1683689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3, 3].length) (baseStart_1683689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683689 prefixEnd_1683689 := by exact prefixLift 1683689
  have htrace : WordTrace (prefixWord ++ tailWord_1683689) baseStart_1683689 baseEnd_1683689 := by
    simpa [prefixWord, tailWord_1683689, baseEnd_1683689] using wordTrace_append hprefix tailTrace_1683689
  have hstable : (prefixWord ++ tailWord_1683689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683689).length < 2 ^ (prefixWord ++ tailWord_1683689).sum := by decide
  have hdescent : baseEnd_1683689 < baseStart_1683689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683690 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_1683690 : Nat := 118140960795 + 1683690 * 2 ^ 59
def prefixEnd_1683690 : Nat := 4983230072969 + 3 ^ 40 * 1683690 * 2
def baseEnd_1683690 : Nat := 864542243168622788831857

theorem tailTrace_1683690 : CollatzResearch.WordTrace tailWord_1683690 prefixEnd_1683690 864542243168622788831857 := by
  unfold tailWord_1683690
  simp only [CollatzResearch.WordTrace]
  refine ⟨15352304817571539050994131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40939479513524104135984349 15352304817571539050994131)
  ·
    refine ⟨23028457226357308576491197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15352304817571539050994131 23028457226357308576491197)
    ·
      refine ⟨8635671459883990716184199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23028457226357308576491197 8635671459883990716184199)
      ·
        refine ⟨12953507189825986074276299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8635671459883990716184199 12953507189825986074276299)
        ·
          refine ⟨19430260784738979111414449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12953507189825986074276299 19430260784738979111414449)
          ·
            refine ⟨14572695588554234333560837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19430260784738979111414449 14572695588554234333560837)
            ·
              refine ⟨2732380422853918937542657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14572695588554234333560837 2732380422853918937542657)
              ·
                refine ⟨2049285317140439203156993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2732380422853918937542657 2049285317140439203156993)
                ·
                  refine ⟨1536963987855329402367745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2049285317140439203156993 1536963987855329402367745)
                  ·
                    refine ⟨1152722990891497051775809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1536963987855329402367745 1152722990891497051775809)
                    ·
                      refine ⟨864542243168622788831857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152722990891497051775809 864542243168622788831857)
                      ·
                        rfl

theorem cell23_1683690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_1683690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683690 prefixEnd_1683690 := by exact prefixLift 1683690
  have htrace : WordTrace (prefixWord ++ tailWord_1683690) baseStart_1683690 baseEnd_1683690 := by
    simpa [prefixWord, tailWord_1683690, baseEnd_1683690] using wordTrace_append hprefix tailTrace_1683690
  have hstable : (prefixWord ++ tailWord_1683690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683690).length < 2 ^ (prefixWord ++ tailWord_1683690).sum := by decide
  have hdescent : baseEnd_1683690 < baseStart_1683690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683706 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3]
def baseStart_1683706 : Nat := 118140960795 + 1683706 * 2 ^ 59
def prefixEnd_1683706 : Nat := 4983230072969 + 3 ^ 40 * 1683706 * 2
def baseEnd_1683706 : Nat := 864550458859094726231783

theorem tailTrace_1683706 : CollatzResearch.WordTrace tailWord_1683706 prefixEnd_1683706 864550458859094726231783 := by
  unfold tailWord_1683706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15352450709557047734139743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40939868558818793957705981 15352450709557047734139743)
  ·
    refine ⟨23028676064335571601209615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15352450709557047734139743 23028676064335571601209615)
    ·
      refine ⟨34543014096503357401814423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23028676064335571601209615 34543014096503357401814423)
      ·
        refine ⟨51814521144755036102721635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34543014096503357401814423 51814521144755036102721635)
        ·
          refine ⟨77721781717132554154082453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51814521144755036102721635 77721781717132554154082453)
          ·
            refine ⟨3643208517990588475972615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77721781717132554154082453 3643208517990588475972615)
            ·
              refine ⟨5464812776985882713958923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643208517990588475972615 5464812776985882713958923)
              ·
                refine ⟨8197219165478824070938385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5464812776985882713958923 8197219165478824070938385)
                ·
                  refine ⟨6147914374109118053203789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8197219165478824070938385 6147914374109118053203789)
                  ·
                    refine ⟨2305467890290919269951421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6147914374109118053203789 2305467890290919269951421)
                    ·
                      refine ⟨864550458859094726231783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2305467890290919269951421 864550458859094726231783)
                      ·
                        rfl

theorem cell23_1683706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_1683706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683706 prefixEnd_1683706 := by exact prefixLift 1683706
  have htrace : WordTrace (prefixWord ++ tailWord_1683706) baseStart_1683706 baseEnd_1683706 := by
    simpa [prefixWord, tailWord_1683706, baseEnd_1683706] using wordTrace_append hprefix tailTrace_1683706
  have hstable : (prefixWord ++ tailWord_1683706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683706).length < 2 ^ (prefixWord ++ tailWord_1683706).sum := by decide
  have hdescent : baseEnd_1683706 < baseStart_1683706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683709 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_1683709 : Nat := 118140960795 + 1683709 * 2 ^ 59
def prefixEnd_1683709 : Nat := 4983230072969 + 3 ^ 40 * 1683709 * 2
def baseEnd_1683709 : Nat := 288183999767019404831423

theorem tailTrace_1683709 : CollatzResearch.WordTrace tailWord_1683709 prefixEnd_1683709 288183999767019404831423 := by
  unfold tailWord_1683709
  simp only [CollatzResearch.WordTrace]
  refine ⟨61409912257217322448918181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40939941504811548299278787 61409912257217322448918181)
  ·
    refine ⟨11514358548228247959172159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61409912257217322448918181 11514358548228247959172159)
    ·
      refine ⟨17271537822342371938758239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11514358548228247959172159 17271537822342371938758239)
      ·
        refine ⟨25907306733513557908137359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17271537822342371938758239 25907306733513557908137359)
        ·
          refine ⟨38860960100270336862206039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25907306733513557908137359 38860960100270336862206039)
          ·
            refine ⟨58291440150405505293309059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38860960100270336862206039 58291440150405505293309059)
            ·
              refine ⟨87437160225608257939963589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58291440150405505293309059 87437160225608257939963589)
              ·
                refine ⟨16394467542301548363743173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87437160225608257939963589 16394467542301548363743173)
                ·
                  refine ⟨3073962664181540318201845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16394467542301548363743173 3073962664181540318201845)
                  ·
                    refine ⟨288183999767019404831423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3073962664181540318201845 288183999767019404831423)
                    ·
                      rfl

theorem cell23_1683709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_1683709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683709 prefixEnd_1683709 := by exact prefixLift 1683709
  have htrace : WordTrace (prefixWord ++ tailWord_1683709) baseStart_1683709 baseEnd_1683709 := by
    simpa [prefixWord, tailWord_1683709, baseEnd_1683709] using wordTrace_append hprefix tailTrace_1683709
  have hstable : (prefixWord ++ tailWord_1683709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683709).length < 2 ^ (prefixWord ++ tailWord_1683709).sum := by decide
  have hdescent : baseEnd_1683709 < baseStart_1683709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683756 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_1683756 : Nat := 118140960795 + 1683756 * 2 ^ 59
def prefixEnd_1683756 : Nat := 4983230072969 + 3 ^ 40 * 1683756 * 2
def baseEnd_1683756 : Nat := 288192044297273176868851

theorem tailTrace_1683756 : CollatzResearch.WordTrace tailWord_1683756 prefixEnd_1683756 288192044297273176868851 := by
  unfold tailWord_1683756
  simp only [CollatzResearch.WordTrace]
  refine ⟨30705813244023524737939561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40941084325364699650586081 30705813244023524737939561)
  ·
    refine ⟨23029359933017643553454671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30705813244023524737939561 23029359933017643553454671)
    ·
      refine ⟨34544039899526465330182007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23029359933017643553454671 34544039899526465330182007)
      ·
        refine ⟨51816059849289697995273011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34544039899526465330182007 51816059849289697995273011)
        ·
          refine ⟨77724089773934546992909517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51816059849289697995273011 77724089773934546992909517)
          ·
            refine ⟨29146533665225455122341069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77724089773934546992909517 29146533665225455122341069)
            ·
              refine ⟨10929950124459545670877901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29146533665225455122341069 10929950124459545670877901)
              ·
                refine ⟨4098731296672329626579213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10929950124459545670877901 4098731296672329626579213)
                ·
                  refine ⟨1537024236252123609967205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4098731296672329626579213 1537024236252123609967205)
                  ·
                    refine ⟨288192044297273176868851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1537024236252123609967205 288192044297273176868851)
                    ·
                      rfl

theorem cell23_1683756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_1683756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683756 prefixEnd_1683756 := by exact prefixLift 1683756
  have htrace : WordTrace (prefixWord ++ tailWord_1683756) baseStart_1683756 baseEnd_1683756 := by
    simpa [prefixWord, tailWord_1683756, baseEnd_1683756] using wordTrace_append hprefix tailTrace_1683756
  have hstable : (prefixWord ++ tailWord_1683756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683756).length < 2 ^ (prefixWord ++ tailWord_1683756).sum := by decide
  have hdescent : baseEnd_1683756 < baseStart_1683756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683809 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1683809 : Nat := 118140960795 + 1683809 * 2 ^ 59
def prefixEnd_1683809 : Nat := 4983230072969 + 3 ^ 40 * 1683809 * 2
def baseEnd_1683809 : Nat := 864603347366507823243809

theorem tailTrace_1683809 : CollatzResearch.WordTrace tailWord_1683809 prefixEnd_1683809 864603347366507823243809 := by
  unfold tailWord_1683809
  simp only [CollatzResearch.WordTrace]
  refine ⟨61413559556855039527558481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40942373037903359685038987 61413559556855039527558481)
  ·
    refine ⟨46060169667641279645668861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61413559556855039527558481 46060169667641279645668861)
    ·
      refine ⟨17272563625365479867125823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46060169667641279645668861 17272563625365479867125823)
      ·
        refine ⟨25908845438048219800688735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17272563625365479867125823 25908845438048219800688735)
        ·
          refine ⟨38863268157072329701033103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25908845438048219800688735 38863268157072329701033103)
          ·
            refine ⟨58294902235608494551549655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38863268157072329701033103 58294902235608494551549655)
            ·
              refine ⟨87442353353412741827324483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58294902235608494551549655 87442353353412741827324483)
              ·
                refine ⟨131163530030119112740986725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87442353353412741827324483 131163530030119112740986725)
                ·
                  refine ⟨24593161880647333638935011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131163530030119112740986725 24593161880647333638935011)
                  ·
                    refine ⟨36889742820971000458402517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24593161880647333638935011 36889742820971000458402517)
                    ·
                      refine ⟨864603347366507823243809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36889742820971000458402517 864603347366507823243809)
                      ·
                        rfl

theorem cell23_1683809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1683809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683809 prefixEnd_1683809 := by exact prefixLift 1683809
  have htrace : WordTrace (prefixWord ++ tailWord_1683809) baseStart_1683809 baseEnd_1683809 := by
    simpa [prefixWord, tailWord_1683809, baseEnd_1683809] using wordTrace_append hprefix tailTrace_1683809
  have hstable : (prefixWord ++ tailWord_1683809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683809).length < 2 ^ (prefixWord ++ tailWord_1683809).sum := by decide
  have hdescent : baseEnd_1683809 < baseStart_1683809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683820 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 6]
def baseStart_1683820 : Nat := 118140960795 + 1683820 * 2 ^ 59
def prefixEnd_1683820 : Nat := 4983230072969 + 3 ^ 40 * 1683820 * 2
def baseEnd_1683820 : Nat := 96067666183745253356251

theorem tailTrace_1683820 : CollatzResearch.WordTrace tailWord_1683820 prefixEnd_1683820 96067666183745253356251 := by
  unfold tailWord_1683820
  simp only [CollatzResearch.WordTrace]
  refine ⟨30706980379907594203104457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40942640506543458937472609 30706980379907594203104457)
  ·
    refine ⟨23030235284930695652328343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30706980379907594203104457 23030235284930695652328343)
    ·
      refine ⟨34545352927396043478492515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23030235284930695652328343 34545352927396043478492515)
      ·
        refine ⟨51818029391094065217738773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34545352927396043478492515 51818029391094065217738773)
        ·
          refine ⟨2428970127707534307081505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51818029391094065217738773 2428970127707534307081505)
          ·
            refine ⟨1821727595780650730311129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2428970127707534307081505 1821727595780650730311129)
            ·
              refine ⟨1366295696835488047733347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1821727595780650730311129 1366295696835488047733347)
              ·
                refine ⟨2049443545253232071600021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366295696835488047733347 2049443545253232071600021)
                ·
                  refine ⟨96067666183745253356251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2049443545253232071600021 96067666183745253356251)
                  ·
                    rfl

theorem cell23_1683820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_1683820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683820 prefixEnd_1683820 := by exact prefixLift 1683820
  have htrace : WordTrace (prefixWord ++ tailWord_1683820) baseStart_1683820 baseEnd_1683820 := by
    simpa [prefixWord, tailWord_1683820, baseEnd_1683820] using wordTrace_append hprefix tailTrace_1683820
  have hstable : (prefixWord ++ tailWord_1683820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683820).length < 2 ^ (prefixWord ++ tailWord_1683820).sum := by decide
  have hdescent : baseEnd_1683820 < baseStart_1683820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683863 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 2, 4]
def baseStart_1683863 : Nat := 118140960795 + 1683863 * 2 ^ 59
def prefixEnd_1683863 : Nat := 4983230072969 + 3 ^ 40 * 1683863 * 2
def baseEnd_1683863 : Nat := 288210358440616870656187

theorem tailTrace_1683863 : CollatzResearch.WordTrace tailWord_1683863 prefixEnd_1683863 288210358440616870656187 := by
  unfold tailWord_1683863
  simp only [CollatzResearch.WordTrace]
  refine ⟨61415529098659406750024243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40943686065772937833349495 61415529098659406750024243)
  ·
    refine ⟨92123293647989110125036365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61415529098659406750024243 92123293647989110125036365)
    ·
      refine ⟨34546235117995916296888637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92123293647989110125036365 34546235117995916296888637)
      ·
        refine ⟨12954838169248468611333239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34546235117995916296888637 12954838169248468611333239)
        ·
          refine ⟨19432257253872702916999859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12954838169248468611333239 19432257253872702916999859)
          ·
            refine ⟨29148385880809054375499789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19432257253872702916999859 29148385880809054375499789)
            ·
              refine ⟨10930644705303395390812421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29148385880809054375499789 10930644705303395390812421)
              ·
                refine ⟨2049495882244386635777329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10930644705303395390812421 2049495882244386635777329)
                ·
                  refine ⟨1537121911683289976832997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2049495882244386635777329 1537121911683289976832997)
                  ·
                    refine ⟨288210358440616870656187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1537121911683289976832997 288210358440616870656187)
                    ·
                      rfl

theorem cell23_1683863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_1683863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683863 prefixEnd_1683863 := by exact prefixLift 1683863
  have htrace : WordTrace (prefixWord ++ tailWord_1683863) baseStart_1683863 baseEnd_1683863 := by
    simpa [prefixWord, tailWord_1683863, baseEnd_1683863] using wordTrace_append hprefix tailTrace_1683863
  have hstable : (prefixWord ++ tailWord_1683863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683863).length < 2 ^ (prefixWord ++ tailWord_1683863).sum := by decide
  have hdescent : baseEnd_1683863 < baseStart_1683863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683864 : List Nat := [2, 1, 2, 5, 1, 1, 4, 2, 1, 1, 3]
def baseStart_1683864 : Nat := 118140960795 + 1683864 * 2 ^ 59
def prefixEnd_1683864 : Nat := 4983230072969 + 3 ^ 40 * 1683864 * 2
def baseEnd_1683864 : Nat := 864631588802505108056057

theorem tailTrace_1683864 : CollatzResearch.WordTrace tailWord_1683864 prefixEnd_1683864 864631588802505108056057 := by
  unfold tailWord_1683864
  simp only [CollatzResearch.WordTrace]
  refine ⟨30707782785827891960405323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40943710381103855947207097 30707782785827891960405323)
  ·
    refine ⟨46061674178741837940607985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30707782785827891960405323 46061674178741837940607985)
    ·
      refine ⟨34546255634056378455455989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46061674178741837940607985 34546255634056378455455989)
      ·
        refine ⟨3238711465692785480198999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34546255634056378455455989 3238711465692785480198999)
        ·
          refine ⟨4858067198539178220298499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238711465692785480198999 4858067198539178220298499)
          ·
            refine ⟨7287100797808767330447749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4858067198539178220298499 7287100797808767330447749)
            ·
              refine ⟨1366331399589143874458953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7287100797808767330447749 1366331399589143874458953)
              ·
                refine ⟨1024748549691857905844215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366331399589143874458953 1024748549691857905844215)
                ·
                  refine ⟨1537122824537786858766323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024748549691857905844215 1537122824537786858766323)
                  ·
                    refine ⟨2305684236806680288149485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1537122824537786858766323 2305684236806680288149485)
                    ·
                      refine ⟨864631588802505108056057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2305684236806680288149485 864631588802505108056057)
                      ·
                        rfl

theorem cell23_1683864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_1683864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683864 prefixEnd_1683864 := by exact prefixLift 1683864
  have htrace : WordTrace (prefixWord ++ tailWord_1683864) baseStart_1683864 baseEnd_1683864 := by
    simpa [prefixWord, tailWord_1683864, baseEnd_1683864] using wordTrace_append hprefix tailTrace_1683864
  have hstable : (prefixWord ++ tailWord_1683864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683864).length < 2 ^ (prefixWord ++ tailWord_1683864).sum := by decide
  have hdescent : baseEnd_1683864 < baseStart_1683864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683870 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1683870 : Nat := 118140960795 + 1683870 * 2 ^ 59
def prefixEnd_1683870 : Nat := 4983230072969 + 3 ^ 40 * 1683870 * 2
def baseEnd_1683870 : Nat := 864634669686432084581029

theorem tailTrace_1683870 : CollatzResearch.WordTrace tailWord_1683870 prefixEnd_1683870 864634669686432084581029 := by
  unfold tailWord_1683870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7676973051204255868191133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40943856273089364630352709 7676973051204255868191133)
  ·
    refine ⟨2878864894201595950571675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7676973051204255868191133 2878864894201595950571675)
    ·
      refine ⟨4318297341302393925857513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2878864894201595950571675 4318297341302393925857513)
      ·
        refine ⟨3238723005976795444393135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4318297341302393925857513 3238723005976795444393135)
        ·
          refine ⟨4858084508965193166589703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238723005976795444393135 4858084508965193166589703)
          ·
            refine ⟨7287126763447789749884555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4858084508965193166589703 7287126763447789749884555)
            ·
              refine ⟨10930690145171684624826833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7287126763447789749884555 10930690145171684624826833)
              ·
                refine ⟨8198017608878763468620125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10930690145171684624826833 8198017608878763468620125)
                ·
                  refine ⟨3074256603329536300732547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8198017608878763468620125 3074256603329536300732547)
                  ·
                    refine ⟨4611384904994304451098821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3074256603329536300732547 4611384904994304451098821)
                    ·
                      refine ⟨864634669686432084581029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4611384904994304451098821 864634669686432084581029)
                      ·
                        rfl

theorem cell23_1683870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1683870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683870 prefixEnd_1683870 := by exact prefixLift 1683870
  have htrace : WordTrace (prefixWord ++ tailWord_1683870) baseStart_1683870 baseEnd_1683870 := by
    simpa [prefixWord, tailWord_1683870, baseEnd_1683870] using wordTrace_append hprefix tailTrace_1683870
  have hstable : (prefixWord ++ tailWord_1683870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683870).length < 2 ^ (prefixWord ++ tailWord_1683870).sum := by decide
  have hdescent : baseEnd_1683870 < baseStart_1683870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683876 : List Nat := [2, 3, 1, 2, 1, 1, 5, 8]
def baseStart_1683876 : Nat := 118140960795 + 1683876 * 2 ^ 59
def prefixEnd_1683876 : Nat := 4983230072969 + 3 ^ 40 * 1683876 * 2
def baseEnd_1683876 : Nat := 32023620391494780040963

theorem tailTrace_1683876 : CollatzResearch.WordTrace tailWord_1683876 prefixEnd_1683876 32023620391494780040963 := by
  unfold tailWord_1683876
  simp only [CollatzResearch.WordTrace]
  refine ⟨30708001623806154985123741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40944002165074873313498321 30708001623806154985123741)
  ·
    refine ⟨11515500608927308119421403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30708001623806154985123741 11515500608927308119421403)
    ·
      refine ⟨17273250913390962179132105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11515500608927308119421403 17273250913390962179132105)
      ·
        refine ⟨12954938185043221634349079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17273250913390962179132105 12954938185043221634349079)
        ·
          refine ⟨19432407277564832451523619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12954938185043221634349079 19432407277564832451523619)
          ·
            refine ⟨29148610916347248677285429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19432407277564832451523619 29148610916347248677285429)
            ·
              refine ⟨2732682273407554563495509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29148610916347248677285429 2732682273407554563495509)
              ·
                refine ⟨32023620391494780040963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2732682273407554563495509 32023620391494780040963)
                ·
                  rfl

theorem cell23_1683876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 8].length) (baseStart_1683876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683876 prefixEnd_1683876 := by exact prefixLift 1683876
  have htrace : WordTrace (prefixWord ++ tailWord_1683876) baseStart_1683876 baseEnd_1683876 := by
    simpa [prefixWord, tailWord_1683876, baseEnd_1683876] using wordTrace_append hprefix tailTrace_1683876
  have hstable : (prefixWord ++ tailWord_1683876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683876).length < 2 ^ (prefixWord ++ tailWord_1683876).sum := by decide
  have hdescent : baseEnd_1683876 < baseStart_1683876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683880 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1683880 : Nat := 118140960795 + 1683880 * 2 ^ 59
def prefixEnd_1683880 : Nat := 4983230072969 + 3 ^ 40 * 1683880 * 2
def baseEnd_1683880 : Nat := 288213268164325681818661

theorem tailTrace_1683880 : CollatzResearch.WordTrace tailWord_1683880 prefixEnd_1683880 288213268164325681818661 := by
  unfold tailWord_1683880
  simp only [CollatzResearch.WordTrace]
  refine ⟨30708074569798909326696547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40944099426398545768928729 30708074569798909326696547)
  ·
    refine ⟨46062111854698363990044821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30708074569798909326696547 46062111854698363990044821)
    ·
      refine ⟨2159161493188985812033351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46062111854698363990044821 2159161493188985812033351)
      ·
        refine ⟨3238742239783478718050027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2159161493188985812033351 3238742239783478718050027)
        ·
          refine ⟨4858113359675218077075041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238742239783478718050027 4858113359675218077075041)
          ·
            refine ⟨3643585019756413557806281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4858113359675218077075041 3643585019756413557806281)
            ·
              refine ⟨2732688764817310168354711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3643585019756413557806281 2732688764817310168354711)
              ·
                refine ⟨4099033147225965252532067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2732688764817310168354711 4099033147225965252532067)
                ·
                  refine ⟨6148549720838947878798101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099033147225965252532067 6148549720838947878798101)
                  ·
                    refine ⟨288213268164325681818661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6148549720838947878798101 288213268164325681818661)
                    ·
                      rfl

theorem cell23_1683880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1683880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683880 prefixEnd_1683880 := by exact prefixLift 1683880
  have htrace : WordTrace (prefixWord ++ tailWord_1683880) baseStart_1683880 baseEnd_1683880 := by
    simpa [prefixWord, tailWord_1683880, baseEnd_1683880] using wordTrace_append hprefix tailTrace_1683880
  have hstable : (prefixWord ++ tailWord_1683880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683880).length < 2 ^ (prefixWord ++ tailWord_1683880).sum := by decide
  have hdescent : baseEnd_1683880 < baseStart_1683880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683936 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 2, 6]
def baseStart_1683936 : Nat := 118140960795 + 1683936 * 2 ^ 59
def prefixEnd_1683936 : Nat := 4983230072969 + 3 ^ 40 * 1683936 * 2
def baseEnd_1683936 : Nat := 288222853136542942118575

theorem tailTrace_1683936 : CollatzResearch.WordTrace tailWord_1683936 prefixEnd_1683936 288222853136542942118575 := by
  unfold tailWord_1683936
  simp only [CollatzResearch.WordTrace]
  refine ⟨30709095813697470108715831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40945461084929960144954441 30709095813697470108715831)
  ·
    refine ⟨46063643720546205163073747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30709095813697470108715831 46063643720546205163073747)
    ·
      refine ⟨69095465580819307744610621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46063643720546205163073747 69095465580819307744610621)
      ·
        refine ⟨25910799592807240404228983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69095465580819307744610621 25910799592807240404228983)
        ·
          refine ⟨38866199389210860606343475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25910799592807240404228983 38866199389210860606343475)
          ·
            refine ⟨58299299083816290909515213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38866199389210860606343475 58299299083816290909515213)
            ·
              refine ⟨21862237156431109091068205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58299299083816290909515213 21862237156431109091068205)
              ·
                refine ⟨8198338933661665909150577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21862237156431109091068205 8198338933661665909150577)
                ·
                  refine ⟨6148754200246249431862933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8198338933661665909150577 6148754200246249431862933)
                  ·
                    refine ⟨288222853136542942118575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6148754200246249431862933 288222853136542942118575)
                    ·
                      rfl

theorem cell23_1683936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_1683936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683936 prefixEnd_1683936 := by exact prefixLift 1683936
  have htrace : WordTrace (prefixWord ++ tailWord_1683936) baseStart_1683936 baseEnd_1683936 := by
    simpa [prefixWord, tailWord_1683936, baseEnd_1683936] using wordTrace_append hprefix tailTrace_1683936
  have hstable : (prefixWord ++ tailWord_1683936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683936).length < 2 ^ (prefixWord ++ tailWord_1683936).sum := by decide
  have hdescent : baseEnd_1683936 < baseStart_1683936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683937 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 2, 1, 3]
def baseStart_1683937 : Nat := 118140960795 + 1683937 * 2 ^ 59
def prefixEnd_1683937 : Nat := 4983230072969 + 3 ^ 40 * 1683937 * 2
def baseEnd_1683937 : Nat := 864669072890283322443221

theorem tailTrace_1683937 : CollatzResearch.WordTrace tailWord_1683937 prefixEnd_1683937 864669072890283322443221 := by
  unfold tailWord_1683937
  simp only [CollatzResearch.WordTrace]
  refine ⟨61418228100391317388218065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40945485400260878258812043 61418228100391317388218065)
  ·
    refine ⟨46063671075293488041163549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61418228100391317388218065 46063671075293488041163549)
    ·
      refine ⟨17273876653235058015436331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46063671075293488041163549 17273876653235058015436331)
      ·
        refine ⟨25910814979852587023154497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17273876653235058015436331 25910814979852587023154497)
        ·
          refine ⟨19433111234889440267365873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25910814979852587023154497 19433111234889440267365873)
          ·
            refine ⟨14574833426167080200524405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19433111234889440267365873 14574833426167080200524405)
            ·
              refine ⟨1366390633703163768799163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14574833426167080200524405 1366390633703163768799163)
              ·
                refine ⟨2049585950554745653198745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366390633703163768799163 2049585950554745653198745)
                ·
                  refine ⟨1537189462916059239899059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2049585950554745653198745 1537189462916059239899059)
                  ·
                    refine ⟨2305784194374088859848589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1537189462916059239899059 2305784194374088859848589)
                    ·
                      refine ⟨864669072890283322443221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2305784194374088859848589 864669072890283322443221)
                      ·
                        rfl

theorem cell23_1683937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_1683937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683937 prefixEnd_1683937 := by exact prefixLift 1683937
  have htrace : WordTrace (prefixWord ++ tailWord_1683937) baseStart_1683937 baseEnd_1683937 := by
    simpa [prefixWord, tailWord_1683937, baseEnd_1683937] using wordTrace_append hprefix tailTrace_1683937
  have hstable : (prefixWord ++ tailWord_1683937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683937).length < 2 ^ (prefixWord ++ tailWord_1683937).sum := by decide
  have hdescent : baseEnd_1683937 < baseStart_1683937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683960 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 6, 2, 2]
def baseStart_1683960 : Nat := 118140960795 + 1683960 * 2 ^ 59
def prefixEnd_1683960 : Nat := 4983230072969 + 3 ^ 40 * 1683960 * 2
def baseEnd_1683960 : Nat := 864680882945336732455615

theorem tailTrace_1683960 : CollatzResearch.WordTrace tailWord_1683960 prefixEnd_1683960 864680882945336732455615 := by
  unfold tailWord_1683960
  simp only [CollatzResearch.WordTrace]
  refine ⟨30709533489653996158152667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40946044652871994877536889 30709533489653996158152667)
  ·
    refine ⟨46064300234480994237229001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30709533489653996158152667 46064300234480994237229001)
    ·
      refine ⟨34548225175860745677921751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46064300234480994237229001 34548225175860745677921751)
      ·
        refine ⟨51822337763791118516882627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34548225175860745677921751 51822337763791118516882627)
        ·
          refine ⟨77733506645686677775323941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51822337763791118516882627 77733506645686677775323941)
          ·
            refine ⟨14575032496066252082873239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77733506645686677775323941 14575032496066252082873239)
            ·
              refine ⟨21862548744099378124309859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14575032496066252082873239 21862548744099378124309859)
              ·
                refine ⟨32793823116149067186464789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21862548744099378124309859 32793823116149067186464789)
                ·
                  refine ⟨1537210458569487524365537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32793823116149067186464789 1537210458569487524365537)
                  ·
                    refine ⟨1152907843927115643274153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1537210458569487524365537 1152907843927115643274153)
                    ·
                      refine ⟨864680882945336732455615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152907843927115643274153 864680882945336732455615)
                      ·
                        rfl

theorem cell23_1683960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_1683960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683960 prefixEnd_1683960 := by exact prefixLift 1683960
  have htrace : WordTrace (prefixWord ++ tailWord_1683960) baseStart_1683960 baseEnd_1683960 := by
    simpa [prefixWord, tailWord_1683960, baseEnd_1683960] using wordTrace_append hprefix tailTrace_1683960
  have hstable : (prefixWord ++ tailWord_1683960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683960).length < 2 ^ (prefixWord ++ tailWord_1683960).sum := by decide
  have hdescent : baseEnd_1683960 < baseStart_1683960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683976 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1683976 : Nat := 118140960795 + 1683976 * 2 ^ 59
def prefixEnd_1683976 : Nat := 4983230072969 + 3 ^ 40 * 1683976 * 2
def baseEnd_1683976 : Nat := 864689098635808669855541

theorem tailTrace_1683976 : CollatzResearch.WordTrace tailWord_1683976 prefixEnd_1683976 864689098635808669855541 := by
  unfold tailWord_1683976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30709825273625013524443891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40946433698166684699258521 30709825273625013524443891)
  ·
    refine ⟨46064737910437520286665837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30709825273625013524443891 46064737910437520286665837)
    ·
      refine ⟨17274276716414070107499689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46064737910437520286665837 17274276716414070107499689)
      ·
        refine ⟨12955707537310552580624767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17274276716414070107499689 12955707537310552580624767)
        ·
          refine ⟨19433561305965828870937151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12955707537310552580624767 19433561305965828870937151)
          ·
            refine ⟨29150341958948743306405727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19433561305965828870937151 29150341958948743306405727)
            ·
              refine ⟨43725512938423114959608591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29150341958948743306405727 43725512938423114959608591)
              ·
                refine ⟨65588269407634672439412887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43725512938423114959608591 65588269407634672439412887)
                ·
                  refine ⟨98382404111452008659119331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65588269407634672439412887 98382404111452008659119331)
                  ·
                    refine ⟨147573606167178012988678997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98382404111452008659119331 147573606167178012988678997)
                    ·
                      refine ⟨864689098635808669855541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 147573606167178012988678997 864689098635808669855541)
                      ·
                        rfl

theorem cell23_1683976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1683976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683976 prefixEnd_1683976 := by exact prefixLift 1683976
  have htrace : WordTrace (prefixWord ++ tailWord_1683976) baseStart_1683976 baseEnd_1683976 := by
    simpa [prefixWord, tailWord_1683976, baseEnd_1683976] using wordTrace_append hprefix tailTrace_1683976
  have hstable : (prefixWord ++ tailWord_1683976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683976).length < 2 ^ (prefixWord ++ tailWord_1683976).sum := by decide
  have hdescent : baseEnd_1683976 < baseStart_1683976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683994 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2]
def baseStart_1683994 : Nat := 118140960795 + 1683994 * 2 ^ 59
def prefixEnd_1683994 : Nat := 4983230072969 + 3 ^ 40 * 1683994 * 2
def baseEnd_1683994 : Nat := 864698341287589599430459

theorem tailTrace_1683994 : CollatzResearch.WordTrace tailWord_1683994 prefixEnd_1683994 864698341287589599430459 := by
  unfold tailWord_1683994
  simp only [CollatzResearch.WordTrace]
  refine ⟨15355076765296204030760759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40946871374123210748695357 15355076765296204030760759)
  ·
    refine ⟨23032615147944306046141139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15355076765296204030760759 23032615147944306046141139)
    ·
      refine ⟨34548922721916459069211709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23032615147944306046141139 34548922721916459069211709)
      ·
        refine ⟨12955846020718672150954391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34548922721916459069211709 12955846020718672150954391)
        ·
          refine ⟨19433769031078008226431587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12955846020718672150954391 19433769031078008226431587)
          ·
            refine ⟨29150653546617012339647381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19433769031078008226431587 29150653546617012339647381)
            ·
              refine ⟨1366436884997672453420971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29150653546617012339647381 1366436884997672453420971)
              ·
                refine ⟨2049655327496508680131457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366436884997672453420971 2049655327496508680131457)
                ·
                  refine ⟨1537241495622381510098593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2049655327496508680131457 1537241495622381510098593)
                  ·
                    refine ⟨1152931121716786132573945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1537241495622381510098593 1152931121716786132573945)
                    ·
                      refine ⟨864698341287589599430459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1152931121716786132573945 864698341287589599430459)
                      ·
                        rfl

theorem cell23_1683994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_1683994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1683994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1683994 prefixEnd_1683994 := by exact prefixLift 1683994
  have htrace : WordTrace (prefixWord ++ tailWord_1683994) baseStart_1683994 baseEnd_1683994 := by
    simpa [prefixWord, tailWord_1683994, baseEnd_1683994] using wordTrace_append hprefix tailTrace_1683994
  have hstable : (prefixWord ++ tailWord_1683994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683994).length < 2 ^ (prefixWord ++ tailWord_1683994).sum := by decide
  have hdescent : baseEnd_1683994 < baseStart_1683994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684133 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_1684133 : Nat := 118140960795 + 1684133 * 2 ^ 59
def prefixEnd_1684133 : Nat := 4983230072969 + 3 ^ 40 * 1684133 * 2
def baseEnd_1684133 : Nat := 288256571699521518530773

theorem tailTrace_1684133 : CollatzResearch.WordTrace tailWord_1684133 prefixEnd_1684133 288256571699521518530773 := by
  unfold tailWord_1684133
  simp only [CollatzResearch.WordTrace]
  refine ⟨61425376807681242862353053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40950251205120828574902035 61425376807681242862353053)
  ·
    refine ⟨23034516302880466073382395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61425376807681242862353053 23034516302880466073382395)
    ·
      refine ⟨34551774454320699110073593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23034516302880466073382395 34551774454320699110073593)
      ·
        refine ⟨25913830840740524332555195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34551774454320699110073593 25913830840740524332555195)
        ·
          refine ⟨38870746261110786498832793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25913830840740524332555195 38870746261110786498832793)
          ·
            refine ⟨29153059695833089874124595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38870746261110786498832793 29153059695833089874124595)
            ·
              refine ⟨43729589543749634811186893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29153059695833089874124595 43729589543749634811186893)
              ·
                refine ⟨16398596078906113054195085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43729589543749634811186893 16398596078906113054195085)
                ·
                  refine ⟨6149473529589792395323157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16398596078906113054195085 6149473529589792395323157)
                  ·
                    refine ⟨288256571699521518530773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6149473529589792395323157 288256571699521518530773)
                    ·
                      rfl

theorem cell23_1684133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_1684133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684133 prefixEnd_1684133 := by exact prefixLift 1684133
  have htrace : WordTrace (prefixWord ++ tailWord_1684133) baseStart_1684133 baseEnd_1684133 := by
    simpa [prefixWord, tailWord_1684133, baseEnd_1684133] using wordTrace_append hprefix tailTrace_1684133
  have hstable : (prefixWord ++ tailWord_1684133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684133).length < 2 ^ (prefixWord ++ tailWord_1684133).sum := by decide
  have hdescent : baseEnd_1684133 < baseStart_1684133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684151 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 3, 1, 3]
def baseStart_1684151 : Nat := 118140960795 + 1684151 * 2 ^ 59
def prefixEnd_1684151 : Nat := 4983230072969 + 3 ^ 40 * 1684151 * 2
def baseEnd_1684151 : Nat := 864778957750345485167237

theorem tailTrace_1684151 : CollatzResearch.WordTrace tailWord_1684151 prefixEnd_1684151 864778957750345485167237 := by
  unfold tailWord_1684151
  simp only [CollatzResearch.WordTrace]
  refine ⟨61426033321616031936508307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40950688881077354624338871 61426033321616031936508307)
  ·
    refine ⟨92139049982424047904762461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61426033321616031936508307 92139049982424047904762461)
    ·
      refine ⟨34552143743409017964285923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92139049982424047904762461 34552143743409017964285923)
      ·
        refine ⟨51828215615113526946428885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34552143743409017964285923 51828215615113526946428885)
        ·
          refine ⟨1214723803479223287806927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 51828215615113526946428885 1214723803479223287806927)
          ·
            refine ⟨1822085705218834931710391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214723803479223287806927 1822085705218834931710391)
            ·
              refine ⟨2733128557828252397565587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822085705218834931710391 2733128557828252397565587)
              ·
                refine ⟨4099692836742378596348381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733128557828252397565587 4099692836742378596348381)
                ·
                  refine ⟨1537384813778391973630643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4099692836742378596348381 1537384813778391973630643)
                  ·
                    refine ⟨2306077220667587960445965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1537384813778391973630643 2306077220667587960445965)
                    ·
                      refine ⟨864778957750345485167237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2306077220667587960445965 864778957750345485167237)
                      ·
                        rfl

theorem cell23_1684151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_1684151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684151 prefixEnd_1684151 := by exact prefixLift 1684151
  have htrace : WordTrace (prefixWord ++ tailWord_1684151) baseStart_1684151 baseEnd_1684151 := by
    simpa [prefixWord, tailWord_1684151, baseEnd_1684151] using wordTrace_append hprefix tailTrace_1684151
  have hstable : (prefixWord ++ tailWord_1684151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684151).length < 2 ^ (prefixWord ++ tailWord_1684151).sum := by decide
  have hdescent : baseEnd_1684151 < baseStart_1684151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684160 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 5]
def baseStart_1684160 : Nat := 118140960795 + 1684160 * 2 ^ 59
def prefixEnd_1684160 : Nat := 4983230072969 + 3 ^ 40 * 1684160 * 2
def baseEnd_1684160 : Nat := 864783579076235949954695

theorem tailTrace_1684160 : CollatzResearch.WordTrace tailWord_1684160 prefixEnd_1684160 864783579076235949954695 := by
  unfold tailWord_1684160
  simp only [CollatzResearch.WordTrace]
  refine ⟨30713180789291713236792967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40950907719055617649057289 30713180789291713236792967)
  ·
    refine ⟨46069771183937569855189451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30713180789291713236792967 46069771183937569855189451)
    ·
      refine ⟨69104656775906354782784177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46069771183937569855189451 69104656775906354782784177)
      ·
        refine ⟨51828492581929766087088133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69104656775906354782784177 51828492581929766087088133)
        ·
          refine ⟨9717842359111831141329025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51828492581929766087088133 9717842359111831141329025)
          ·
            refine ⟨7288381769333873355996769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9717842359111831141329025 7288381769333873355996769)
            ·
              refine ⟨5466286327000405016997577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7288381769333873355996769 5466286327000405016997577)
              ·
                refine ⟨4099714745250303762748183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5466286327000405016997577 4099714745250303762748183)
                ·
                  refine ⟨6149572117875455644122275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099714745250303762748183 6149572117875455644122275)
                  ·
                    refine ⟨9224358176813183466183413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6149572117875455644122275 9224358176813183466183413)
                    ·
                      refine ⟨864783579076235949954695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9224358176813183466183413 864783579076235949954695)
                      ·
                        rfl

theorem cell23_1684160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_1684160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684160 prefixEnd_1684160 := by exact prefixLift 1684160
  have htrace : WordTrace (prefixWord ++ tailWord_1684160) baseStart_1684160 baseEnd_1684160 := by
    simpa [prefixWord, tailWord_1684160, baseEnd_1684160] using wordTrace_append hprefix tailTrace_1684160
  have hstable : (prefixWord ++ tailWord_1684160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684160).length < 2 ^ (prefixWord ++ tailWord_1684160).sum := by decide
  have hdescent : baseEnd_1684160 < baseStart_1684160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684170 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_1684170 : Nat := 118140960795 + 1684170 * 2 ^ 59
def prefixEnd_1684170 : Nat := 4983230072969 + 3 ^ 40 * 1684170 * 2
def baseEnd_1684170 : Nat := 864788713882780910829649

theorem tailTrace_1684170 : CollatzResearch.WordTrace tailWord_1684170 prefixEnd_1684170 864788713882780910829649 := by
  unfold tailWord_1684170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15356681577136799545362491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40951150872364798787633309 15356681577136799545362491)
  ·
    refine ⟨23035022365705199318043737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15356681577136799545362491 23035022365705199318043737)
    ·
      refine ⟨17276266774278899488532803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23035022365705199318043737 17276266774278899488532803)
      ·
        refine ⟨25914400161418349232799205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17276266774278899488532803 25914400161418349232799205)
        ·
          refine ⟨4858950030265940481149851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25914400161418349232799205 4858950030265940481149851)
          ·
            refine ⟨7288425045398910721724777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4858950030265940481149851 7288425045398910721724777)
            ·
              refine ⟨5466318784049183041293583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7288425045398910721724777 5466318784049183041293583)
              ·
                refine ⟨8199478176073774561940375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466318784049183041293583 8199478176073774561940375)
                ·
                  refine ⟨12299217264110661842910563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199478176073774561940375 12299217264110661842910563)
                  ·
                    refine ⟨18448825896165992764365845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12299217264110661842910563 18448825896165992764365845)
                    ·
                      refine ⟨864788713882780910829649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18448825896165992764365845 864788713882780910829649)
                      ·
                        rfl

theorem cell23_1684170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_1684170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684170 prefixEnd_1684170 := by exact prefixLift 1684170
  have htrace : WordTrace (prefixWord ++ tailWord_1684170) baseStart_1684170 baseEnd_1684170 := by
    simpa [prefixWord, tailWord_1684170, baseEnd_1684170] using wordTrace_append hprefix tailTrace_1684170
  have hstable : (prefixWord ++ tailWord_1684170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684170).length < 2 ^ (prefixWord ++ tailWord_1684170).sum := by decide
  have hdescent : baseEnd_1684170 < baseStart_1684170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684174 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_1684174 : Nat := 118140960795 + 1684174 * 2 ^ 59
def prefixEnd_1684174 : Nat := 4983230072969 + 3 ^ 40 * 1684174 * 2
def baseEnd_1684174 : Nat := 864790767805398895179631

theorem tailTrace_1684174 : CollatzResearch.WordTrace tailWord_1684174 prefixEnd_1684174 864790767805398895179631 := by
  unfold tailWord_1684174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7678359025066588358074447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40951248133688471243063717 7678359025066588358074447)
  ·
    refine ⟨11517538537599882537111671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7678359025066588358074447 11517538537599882537111671)
    ·
      refine ⟨17276307806399823805667507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11517538537599882537111671 17276307806399823805667507)
      ·
        refine ⟨25914461709599735708501261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17276307806399823805667507 25914461709599735708501261)
        ·
          refine ⟨9717923141099900890687973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25914461709599735708501261 9717923141099900890687973)
          ·
            refine ⟨1822110588956231417003995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9717923141099900890687973 1822110588956231417003995)
            ·
              refine ⟨2733165883434347125505993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822110588956231417003995 2733165883434347125505993)
              ·
                refine ⟨2049874412575760344129495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2733165883434347125505993 2049874412575760344129495)
                ·
                  refine ⟨3074811618863640516194243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049874412575760344129495 3074811618863640516194243)
                  ·
                    refine ⟨4612217428295460774291365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3074811618863640516194243 4612217428295460774291365)
                    ·
                      refine ⟨864790767805398895179631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4612217428295460774291365 864790767805398895179631)
                      ·
                        rfl

theorem cell23_1684174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_1684174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684174 prefixEnd_1684174 := by exact prefixLift 1684174
  have htrace : WordTrace (prefixWord ++ tailWord_1684174) baseStart_1684174 baseEnd_1684174 := by
    simpa [prefixWord, tailWord_1684174, baseEnd_1684174] using wordTrace_append hprefix tailTrace_1684174
  have hstable : (prefixWord ++ tailWord_1684174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684174).length < 2 ^ (prefixWord ++ tailWord_1684174).sum := by decide
  have hdescent : baseEnd_1684174 < baseStart_1684174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684210 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_1684210 : Nat := 118140960795 + 1684210 * 2 ^ 59
def prefixEnd_1684210 : Nat := 4983230072969 + 3 ^ 40 * 1684210 * 2
def baseEnd_1684210 : Nat := 288269751036320251443155

theorem tailTrace_1684210 : CollatzResearch.WordTrace tailWord_1684210 prefixEnd_1684210 288269751036320251443155 := by
  unfold tailWord_1684210
  simp only [CollatzResearch.WordTrace]
  refine ⟨15357046307100571253226521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40952123485601523341937389 15357046307100571253226521)
  ·
    refine ⟨11517784730325428439919891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15357046307100571253226521 11517784730325428439919891)
    ·
      refine ⟨17276677095488142659879837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11517784730325428439919891 17276677095488142659879837)
      ·
        refine ⟨6478753910808053497454939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17276677095488142659879837 6478753910808053497454939)
        ·
          refine ⟨9718130866212080246182409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6478753910808053497454939 9718130866212080246182409)
          ·
            refine ⟨7288598149659060184636807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9718130866212080246182409 7288598149659060184636807)
            ·
              refine ⟨10932897224488590276955211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7288598149659060184636807 10932897224488590276955211)
              ·
                refine ⟨16399345836732885415432817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10932897224488590276955211 16399345836732885415432817)
                ·
                  refine ⟨12299509377549664061574613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16399345836732885415432817 12299509377549664061574613)
                  ·
                    refine ⟨288269751036320251443155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12299509377549664061574613 288269751036320251443155)
                    ·
                      rfl

theorem cell23_1684210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_1684210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684210 prefixEnd_1684210 := by exact prefixLift 1684210
  have htrace : WordTrace (prefixWord ++ tailWord_1684210) baseStart_1684210 baseEnd_1684210 := by
    simpa [prefixWord, tailWord_1684210, baseEnd_1684210] using wordTrace_append hprefix tailTrace_1684210
  have hstable : (prefixWord ++ tailWord_1684210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684210).length < 2 ^ (prefixWord ++ tailWord_1684210).sum := by decide
  have hdescent : baseEnd_1684210 < baseStart_1684210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684234 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2]
def baseStart_1684234 : Nat := 118140960795 + 1684234 * 2 ^ 59
def prefixEnd_1684234 : Nat := 4983230072969 + 3 ^ 40 * 1684234 * 2
def baseEnd_1684234 : Nat := 864821576644668660429355

theorem tailTrace_1684234 : CollatzResearch.WordTrace tailWord_1684234 prefixEnd_1684234 864821576644668660429355 := by
  unfold tailWord_1684234
  simp only [CollatzResearch.WordTrace]
  refine ⟨15357265145078834277944939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40952707053543558074519837 15357265145078834277944939)
  ·
    refine ⟨23035897717618251416917409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15357265145078834277944939 23035897717618251416917409)
    ·
      refine ⟨17276923288213688562688057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23035897717618251416917409 17276923288213688562688057)
      ·
        refine ⟨12957692466160266422016043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17276923288213688562688057 12957692466160266422016043)
        ·
          refine ⟨19436538699240399633024065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12957692466160266422016043 19436538699240399633024065)
          ·
            refine ⟨14577404024430299724768049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19436538699240399633024065 14577404024430299724768049)
            ·
              refine ⟨10933053018322724793576037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14577404024430299724768049 10933053018322724793576037)
              ·
                refine ⟨2049947440935510898795507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10933053018322724793576037 2049947440935510898795507)
                ·
                  refine ⟨3074921161403266348193261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049947440935510898795507 3074921161403266348193261)
                  ·
                    refine ⟨1153095435526224880572473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3074921161403266348193261 1153095435526224880572473)
                    ·
                      refine ⟨864821576644668660429355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1153095435526224880572473 864821576644668660429355)
                      ·
                        rfl

theorem cell23_1684234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_1684234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684234 prefixEnd_1684234 := by exact prefixLift 1684234
  have htrace : WordTrace (prefixWord ++ tailWord_1684234) baseStart_1684234 baseEnd_1684234 := by
    simpa [prefixWord, tailWord_1684234, baseEnd_1684234] using wordTrace_append hprefix tailTrace_1684234
  have hstable : (prefixWord ++ tailWord_1684234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684234).length < 2 ^ (prefixWord ++ tailWord_1684234).sum := by decide
  have hdescent : baseEnd_1684234 < baseStart_1684234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684250 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1684250 : Nat := 118140960795 + 1684250 * 2 ^ 59
def prefixEnd_1684250 : Nat := 4983230072969 + 3 ^ 40 * 1684250 * 2
def baseEnd_1684250 : Nat := 864829792335140597829281

theorem tailTrace_1684250 : CollatzResearch.WordTrace tailWord_1684250 prefixEnd_1684250 864829792335140597829281 := by
  unfold tailWord_1684250
  simp only [CollatzResearch.WordTrace]
  refine ⟨15357411037064342961090551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40953096098838247896241469 15357411037064342961090551)
  ·
    refine ⟨23036116555596514441635827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15357411037064342961090551 23036116555596514441635827)
    ·
      refine ⟨34554174833394771662453741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23036116555596514441635827 34554174833394771662453741)
      ·
        refine ⟨12957815562523039373420153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34554174833394771662453741 12957815562523039373420153)
        ·
          refine ⟨9718361671892279530065115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12957815562523039373420153 9718361671892279530065115)
          ·
            refine ⟨14577542507838419295097673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9718361671892279530065115 14577542507838419295097673)
            ·
              refine ⟨10933156880878814471323255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14577542507838419295097673 10933156880878814471323255)
              ·
                refine ⟨16399735321318221706984883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10933156880878814471323255 16399735321318221706984883)
                ·
                  refine ⟨24599602981977332560477325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16399735321318221706984883 24599602981977332560477325)
                  ·
                    refine ⟨9224851118241499710178997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24599602981977332560477325 9224851118241499710178997)
                    ·
                      refine ⟨864829792335140597829281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9224851118241499710178997 864829792335140597829281)
                      ·
                        rfl

theorem cell23_1684250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1684250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684250 prefixEnd_1684250 := by exact prefixLift 1684250
  have htrace : WordTrace (prefixWord ++ tailWord_1684250) baseStart_1684250 baseEnd_1684250 := by
    simpa [prefixWord, tailWord_1684250, baseEnd_1684250] using wordTrace_append hprefix tailTrace_1684250
  have hstable : (prefixWord ++ tailWord_1684250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684250).length < 2 ^ (prefixWord ++ tailWord_1684250).sum := by decide
  have hdescent : baseEnd_1684250 < baseStart_1684250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684277 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1684277 : Nat := 118140960795 + 1684277 * 2 ^ 59
def prefixEnd_1684277 : Nat := 4983230072969 + 3 ^ 40 * 1684277 * 2
def baseEnd_1684277 : Nat := 864843656312811992191657

theorem tailTrace_1684277 : CollatzResearch.WordTrace tailWord_1684277 prefixEnd_1684277 864843656312811992191657 := by
  unfold tailWord_1684277
  simp only [CollatzResearch.WordTrace]
  refine ⟨61430628919159555455595085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40953752612773036970396723 61430628919159555455595085)
  ·
    refine ⟨23036485844684833295848157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61430628919159555455595085 23036485844684833295848157)
    ·
      refine ⟨8638682191756812485943059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23036485844684833295848157 8638682191756812485943059)
      ·
        refine ⟨12958023287635218728914589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8638682191756812485943059 12958023287635218728914589)
        ·
          refine ⟨4859258732863207023342971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12958023287635218728914589 4859258732863207023342971)
          ·
            refine ⟨7288888099294810535014457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859258732863207023342971 7288888099294810535014457)
            ·
              refine ⟨5466666074471107901260843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7288888099294810535014457 5466666074471107901260843)
              ·
                refine ⟨8199999111706661851891265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466666074471107901260843 8199999111706661851891265)
                ·
                  refine ⟨6149999333779996388918449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8199999111706661851891265 6149999333779996388918449)
                  ·
                    refine ⟨4612499500334997291688837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6149999333779996388918449 4612499500334997291688837)
                    ·
                      refine ⟨864843656312811992191657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4612499500334997291688837 864843656312811992191657)
                      ·
                        rfl

theorem cell23_1684277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1684277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684277 prefixEnd_1684277 := by exact prefixLift 1684277
  have htrace : WordTrace (prefixWord ++ tailWord_1684277) baseStart_1684277 baseEnd_1684277 := by
    simpa [prefixWord, tailWord_1684277, baseEnd_1684277] using wordTrace_append hprefix tailTrace_1684277
  have hstable : (prefixWord ++ tailWord_1684277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684277).length < 2 ^ (prefixWord ++ tailWord_1684277).sum := by decide
  have hdescent : baseEnd_1684277 < baseStart_1684277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684327 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1684327 : Nat := 118140960795 + 1684327 * 2 ^ 59
def prefixEnd_1684327 : Nat := 4983230072969 + 3 ^ 40 * 1684327 * 2
def baseEnd_1684327 : Nat := 864869330345536796566427

theorem tailTrace_1684327 : CollatzResearch.WordTrace tailWord_1684327 prefixEnd_1684327 864869330345536796566427 := by
  unfold tailWord_1684327
  simp only [CollatzResearch.WordTrace]
  refine ⟨61432452568978413994915235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40954968379318942663276823 61432452568978413994915235)
  ·
    refine ⟨92148678853467620992372853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61432452568978413994915235 92148678853467620992372853)
    ·
      refine ⟨8638938642512589468034955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92148678853467620992372853 8638938642512589468034955)
      ·
        refine ⟨12958407963768884202052433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8638938642512589468034955 12958407963768884202052433)
        ·
          refine ⟨9718805972826663151539325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12958407963768884202052433 9718805972826663151539325)
          ·
            refine ⟨3644552239809998681827247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9718805972826663151539325 3644552239809998681827247)
            ·
              refine ⟨5466828359714998022740871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3644552239809998681827247 5466828359714998022740871)
              ·
                refine ⟨8200242539572497034111307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466828359714998022740871 8200242539572497034111307)
                ·
                  refine ⟨12300363809358745551166961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8200242539572497034111307 12300363809358745551166961)
                  ·
                    refine ⟨9225272857019059163375221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12300363809358745551166961 9225272857019059163375221)
                    ·
                      refine ⟨864869330345536796566427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9225272857019059163375221 864869330345536796566427)
                      ·
                        rfl

theorem cell23_1684327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1684327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684327 prefixEnd_1684327 := by exact prefixLift 1684327
  have htrace : WordTrace (prefixWord ++ tailWord_1684327) baseStart_1684327 baseEnd_1684327 := by
    simpa [prefixWord, tailWord_1684327, baseEnd_1684327] using wordTrace_append hprefix tailTrace_1684327
  have hstable : (prefixWord ++ tailWord_1684327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684327).length < 2 ^ (prefixWord ++ tailWord_1684327).sum := by decide
  have hdescent : baseEnd_1684327 < baseStart_1684327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684347 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 3, 4]
def baseStart_1684347 : Nat := 118140960795 + 1684347 * 2 ^ 59
def prefixEnd_1684347 : Nat := 4983230072969 + 3 ^ 40 * 1684347 * 2
def baseEnd_1684347 : Nat := 288293199986208906105445

theorem tailTrace_1684347 : CollatzResearch.WordTrace tailWord_1684347 prefixEnd_1684347 288293199986208906105445 := by
  unfold tailWord_1684347
  simp only [CollatzResearch.WordTrace]
  refine ⟨61433182028905957410643295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40955454685937304940428863 61433182028905957410643295)
  ·
    refine ⟨92149773043358936115964943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61433182028905957410643295 92149773043358936115964943)
    ·
      refine ⟨138224659565038404173947415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92149773043358936115964943 138224659565038404173947415)
      ·
        refine ⟨207336989347557606260921123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138224659565038404173947415 207336989347557606260921123)
        ·
          refine ⟨311005484021336409391381685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207336989347557606260921123 311005484021336409391381685)
          ·
            refine ⟨29156764127000288380442033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 311005484021336409391381685 29156764127000288380442033)
            ·
              refine ⟨21867573095250216285331525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29156764127000288380442033 21867573095250216285331525)
              ·
                refine ⟨4100169955359415553499661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21867573095250216285331525 4100169955359415553499661)
                ·
                  refine ⟨1537563733259780832562373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4100169955359415553499661 1537563733259780832562373)
                  ·
                    refine ⟨288293199986208906105445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1537563733259780832562373 288293199986208906105445)
                    ·
                      rfl

theorem cell23_1684347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 4].length) (baseStart_1684347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684347 prefixEnd_1684347 := by exact prefixLift 1684347
  have htrace : WordTrace (prefixWord ++ tailWord_1684347) baseStart_1684347 baseEnd_1684347 := by
    simpa [prefixWord, tailWord_1684347, baseEnd_1684347] using wordTrace_append hprefix tailTrace_1684347
  have hstable : (prefixWord ++ tailWord_1684347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684347).length < 2 ^ (prefixWord ++ tailWord_1684347).sum := by decide
  have hdescent : baseEnd_1684347 < baseStart_1684347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684381 : List Nat := [1, 4, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1684381 : Nat := 118140960795 + 1684381 * 2 ^ 59
def prefixEnd_1684381 : Nat := 4983230072969 + 3 ^ 40 * 1684381 * 2
def baseEnd_1684381 : Nat := 288299019433626528430393

theorem tailTrace_1684381 : CollatzResearch.WordTrace tailWord_1684381 prefixEnd_1684381 288299019433626528430393 := by
  unfold tailWord_1684381
  simp only [CollatzResearch.WordTrace]
  refine ⟨61434422110782781217380997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40956281407188520811587331 61434422110782781217380997)
  ·
    refine ⟨11518954145771771478258937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61434422110782781217380997 11518954145771771478258937)
    ·
      refine ⟨8639215609328828608694203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11518954145771771478258937 8639215609328828608694203)
      ·
        refine ⟨12958823413993242913041305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8639215609328828608694203 12958823413993242913041305)
        ·
          refine ⟨9719117560494932184780979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12958823413993242913041305 9719117560494932184780979)
          ·
            refine ⟨14578676340742398277171469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9719117560494932184780979 14578676340742398277171469)
            ·
              refine ⟨5467003627778399353939301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14578676340742398277171469 5467003627778399353939301)
              ·
                refine ⟨1025063180208449878863619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5467003627778399353939301 1025063180208449878863619)
                ·
                  refine ⟨1537594770312674818295429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025063180208449878863619 1537594770312674818295429)
                  ·
                    refine ⟨288299019433626528430393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1537594770312674818295429 288299019433626528430393)
                    ·
                      rfl

theorem cell23_1684381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1684381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684381 prefixEnd_1684381 := by exact prefixLift 1684381
  have htrace : WordTrace (prefixWord ++ tailWord_1684381) baseStart_1684381 baseEnd_1684381 := by
    simpa [prefixWord, tailWord_1684381, baseEnd_1684381] using wordTrace_append hprefix tailTrace_1684381
  have hstable : (prefixWord ++ tailWord_1684381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684381).length < 2 ^ (prefixWord ++ tailWord_1684381).sum := by decide
  have hdescent : baseEnd_1684381 < baseStart_1684381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684407 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 3, 5]
def baseStart_1684407 : Nat := 118140960795 + 1684407 * 2 ^ 59
def prefixEnd_1684407 : Nat := 4983230072969 + 3 ^ 40 * 1684407 * 2
def baseEnd_1684407 : Nat := 288303469599298827855353

theorem tailTrace_1684407 : CollatzResearch.WordTrace tailWord_1684407 prefixEnd_1684407 288303469599298827855353 := by
  unfold tailWord_1684407
  simp only [CollatzResearch.WordTrace]
  refine ⟨61435370408688587657827475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40956913605792391771884983 61435370408688587657827475)
  ·
    refine ⟨92153055613032881486741213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61435370408688587657827475 92153055613032881486741213)
    ·
      refine ⟨34557395854887330557527955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92153055613032881486741213 34557395854887330557527955)
      ·
        refine ⟨51836093782330995836291933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34557395854887330557527955 51836093782330995836291933)
        ·
          refine ⟨19438535168374123438609475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51836093782330995836291933 19438535168374123438609475)
          ·
            refine ⟨29157802752561185157914213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19438535168374123438609475 29157802752561185157914213)
            ·
              refine ⟨5467088016105222217108915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29157802752561185157914213 5467088016105222217108915)
              ·
                refine ⟨8200632024157833325663373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467088016105222217108915 8200632024157833325663373)
                ·
                  refine ⟨3075237009059187497123765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8200632024157833325663373 3075237009059187497123765)
                  ·
                    refine ⟨288303469599298827855353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3075237009059187497123765 288303469599298827855353)
                    ·
                      rfl

theorem cell23_1684407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_1684407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684407 prefixEnd_1684407 := by exact prefixLift 1684407
  have htrace : WordTrace (prefixWord ++ tailWord_1684407) baseStart_1684407 baseEnd_1684407 := by
    simpa [prefixWord, tailWord_1684407, baseEnd_1684407] using wordTrace_append hprefix tailTrace_1684407
  have hstable : (prefixWord ++ tailWord_1684407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684407).length < 2 ^ (prefixWord ++ tailWord_1684407).sum := by decide
  have hdescent : baseEnd_1684407 < baseStart_1684407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684438 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_1684438 : Nat := 118140960795 + 1684438 * 2 ^ 59
def prefixEnd_1684438 : Nat := 4983230072969 + 3 ^ 40 * 1684438 * 2
def baseEnd_1684438 : Nat := 864926326698185862278417

theorem tailTrace_1684438 : CollatzResearch.WordTrace tailWord_1684438 prefixEnd_1684438 864926326698185862278417 := by
  unfold tailWord_1684438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3839781316973517497012873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40957667381050853301470645 3839781316973517497012873)
  ·
    refine ⟨2879835987730138122759655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3839781316973517497012873 2879835987730138122759655)
    ·
      refine ⟨4319753981595207184139483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2879835987730138122759655 4319753981595207184139483)
      ·
        refine ⟨6479630972392810776209225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319753981595207184139483 6479630972392810776209225)
        ·
          refine ⟨4859723229294608082156919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6479630972392810776209225 4859723229294608082156919)
          ·
            refine ⟨7289584843941912123235379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859723229294608082156919 7289584843941912123235379)
            ·
              refine ⟨10934377265912868184853069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7289584843941912123235379 10934377265912868184853069)
              ·
                refine ⟨4100391474717325569319901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10934377265912868184853069 4100391474717325569319901)
                ·
                  refine ⟨1537646803018997088494963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4100391474717325569319901 1537646803018997088494963)
                  ·
                    refine ⟨2306470204528495632742445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1537646803018997088494963 2306470204528495632742445)
                    ·
                      refine ⟨864926326698185862278417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2306470204528495632742445 864926326698185862278417)
                      ·
                        rfl

theorem cell23_1684438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_1684438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684438 prefixEnd_1684438 := by exact prefixLift 1684438
  have htrace : WordTrace (prefixWord ++ tailWord_1684438) baseStart_1684438 baseEnd_1684438 := by
    simpa [prefixWord, tailWord_1684438, baseEnd_1684438] using wordTrace_append hprefix tailTrace_1684438
  have hstable : (prefixWord ++ tailWord_1684438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684438).length < 2 ^ (prefixWord ++ tailWord_1684438).sum := by decide
  have hdescent : baseEnd_1684438 < baseStart_1684438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684481 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_1684481 : Nat := 118140960795 + 1684481 * 2 ^ 59
def prefixEnd_1684481 : Nat := 4983230072969 + 3 ^ 40 * 1684481 * 2
def baseEnd_1684481 : Nat := 864948406366329194040719

theorem tailTrace_1684481 : CollatzResearch.WordTrace tailWord_1684481 prefixEnd_1684481 864948406366329194040719 := by
  unfold tailWord_1684481
  simp only [CollatzResearch.WordTrace]
  refine ⟨61438069410420498296021297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40958712940280332197347531 61438069410420498296021297)
  ·
    refine ⟨46078552057815373722015973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61438069410420498296021297 46078552057815373722015973)
    ·
      refine ⟨8639728510840382572877995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46078552057815373722015973 8639728510840382572877995)
      ·
        refine ⟨12959592766260573859316993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8639728510840382572877995 12959592766260573859316993)
        ·
          refine ⟨9719694574695430394487745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12959592766260573859316993 9719694574695430394487745)
          ·
            refine ⟨7289770931021572795865809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9719694574695430394487745 7289770931021572795865809)
            ·
              refine ⟨5467328198266179596899357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289770931021572795865809 5467328198266179596899357)
              ·
                refine ⟨2050248074349817348837259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5467328198266179596899357 2050248074349817348837259)
                ·
                  refine ⟨3075372111524726023255889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050248074349817348837259 3075372111524726023255889)
                  ·
                    refine ⟨2306529083643544517441917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3075372111524726023255889 2306529083643544517441917)
                    ·
                      refine ⟨864948406366329194040719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2306529083643544517441917 864948406366329194040719)
                      ·
                        rfl

theorem cell23_1684481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_1684481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684481 prefixEnd_1684481 := by exact prefixLift 1684481
  have htrace : WordTrace (prefixWord ++ tailWord_1684481) baseStart_1684481 baseEnd_1684481 := by
    simpa [prefixWord, tailWord_1684481, baseEnd_1684481] using wordTrace_append hprefix tailTrace_1684481
  have hstable : (prefixWord ++ tailWord_1684481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684481).length < 2 ^ (prefixWord ++ tailWord_1684481).sum := by decide
  have hdescent : baseEnd_1684481 < baseStart_1684481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684545 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1684545 : Nat := 118140960795 + 1684545 * 2 ^ 59
def prefixEnd_1684545 : Nat := 4983230072969 + 3 ^ 40 * 1684545 * 2
def baseEnd_1684545 : Nat := 864981269128216943640425

theorem tailTrace_1684545 : CollatzResearch.WordTrace tailWord_1684545 prefixEnd_1684545 864981269128216943640425 := by
  unfold tailWord_1684545
  simp only [CollatzResearch.WordTrace]
  refine ⟨61440403682188637226351089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40960269121459091484234059 61440403682188637226351089)
  ·
    refine ⟨46080302761641477919763317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61440403682188637226351089 46080302761641477919763317)
    ·
      refine ⟨4320028383903888554977811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46080302761641477919763317 4320028383903888554977811)
      ·
        refine ⟨6480042575855832832466717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4320028383903888554977811 6480042575855832832466717)
        ·
          refine ⟨2430015965945937312175019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6480042575855832832466717 2430015965945937312175019)
          ·
            refine ⟨3645023948918905968262529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430015965945937312175019 3645023948918905968262529)
            ·
              refine ⟨2733767961689179476196897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645023948918905968262529 2733767961689179476196897)
              ·
                refine ⟨2050325971266884607147673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2733767961689179476196897 2050325971266884607147673)
                ·
                  refine ⟨1537744478450163455360755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2050325971266884607147673 1537744478450163455360755)
                  ·
                    refine ⟨2306616717675245183041133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1537744478450163455360755 2306616717675245183041133)
                    ·
                      refine ⟨864981269128216943640425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2306616717675245183041133 864981269128216943640425)
                      ·
                        rfl

theorem cell23_1684545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1684545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684545 prefixEnd_1684545 := by exact prefixLift 1684545
  have htrace : WordTrace (prefixWord ++ tailWord_1684545) baseStart_1684545 baseEnd_1684545 := by
    simpa [prefixWord, tailWord_1684545, baseEnd_1684545] using wordTrace_append hprefix tailTrace_1684545
  have hstable : (prefixWord ++ tailWord_1684545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684545).length < 2 ^ (prefixWord ++ tailWord_1684545).sum := by decide
  have hdescent : baseEnd_1684545 < baseStart_1684545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684554 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_1684554 : Nat := 118140960795 + 1684554 * 2 ^ 59
def prefixEnd_1684554 : Nat := 4983230072969 + 3 ^ 40 * 1684554 * 2
def baseEnd_1684554 : Nat := 864985890454107408427883

theorem tailTrace_1684554 : CollatzResearch.WordTrace tailWord_1684554 prefixEnd_1684554 864985890454107408427883 := by
  unfold tailWord_1684554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15360182984789007940857179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40960487959437354508952477 15360182984789007940857179)
  ·
    refine ⟨23040274477183511911285769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15360182984789007940857179 23040274477183511911285769)
    ·
      refine ⟨17280205857887633933464327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23040274477183511911285769 17280205857887633933464327)
      ·
        refine ⟨25920308786831450900196491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17280205857887633933464327 25920308786831450900196491)
        ·
          refine ⟨38880463180247176350294737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25920308786831450900196491 38880463180247176350294737)
          ·
            refine ⟨29160347385185382262721053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38880463180247176350294737 29160347385185382262721053)
            ·
              refine ⟨10935130269444518348520395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29160347385185382262721053 10935130269444518348520395)
              ·
                refine ⟨16402695404166777522780593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10935130269444518348520395 16402695404166777522780593)
                ·
                  refine ⟨12302021553125083142085445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16402695404166777522780593 12302021553125083142085445)
                  ·
                    refine ⟨2306629041210953089141021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12302021553125083142085445 2306629041210953089141021)
                    ·
                      refine ⟨864985890454107408427883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2306629041210953089141021 864985890454107408427883)
                      ·
                        rfl

theorem cell23_1684554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_1684554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684554 prefixEnd_1684554 := by exact prefixLift 1684554
  have htrace : WordTrace (prefixWord ++ tailWord_1684554) baseStart_1684554 baseEnd_1684554 := by
    simpa [prefixWord, tailWord_1684554, baseEnd_1684554] using wordTrace_append hprefix tailTrace_1684554
  have hstable : (prefixWord ++ tailWord_1684554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684554).length < 2 ^ (prefixWord ++ tailWord_1684554).sum := by decide
  have hdescent : baseEnd_1684554 < baseStart_1684554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684564 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1684564 : Nat := 118140960795 + 1684564 * 2 ^ 59
def prefixEnd_1684564 : Nat := 4983230072969 + 3 ^ 40 * 1684564 * 2
def baseEnd_1684564 : Nat := 864991025260652369302837

theorem tailTrace_1684564 : CollatzResearch.WordTrace tailWord_1684564 prefixEnd_1684564 864991025260652369302837 := by
  unfold tailWord_1684564
  simp only [CollatzResearch.WordTrace]
  refine ⟨30720548334559901735646373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40960731112746535647528497 30720548334559901735646373)
  ·
    refine ⟨5760102812729981575433695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30720548334559901735646373 5760102812729981575433695)
    ·
      refine ⟨8640154219094972363150543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5760102812729981575433695 8640154219094972363150543)
      ·
        refine ⟨12960231328642458544725815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8640154219094972363150543 12960231328642458544725815)
        ·
          refine ⟨19440346992963687817088723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12960231328642458544725815 19440346992963687817088723)
          ·
            refine ⟨29160520489445531725633085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19440346992963687817088723 29160520489445531725633085)
            ·
              refine ⟨10935195183542074397112407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29160520489445531725633085 10935195183542074397112407)
              ·
                refine ⟨16402792775313111595668611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10935195183542074397112407 16402792775313111595668611)
                ·
                  refine ⟨24604189162969667393502917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16402792775313111595668611 24604189162969667393502917)
                  ·
                    refine ⟨4613285468056812636281797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24604189162969667393502917 4613285468056812636281797)
                    ·
                      refine ⟨864991025260652369302837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4613285468056812636281797 864991025260652369302837)
                      ·
                        rfl

theorem cell23_1684564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1684564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684564 prefixEnd_1684564 := by exact prefixLift 1684564
  have htrace : WordTrace (prefixWord ++ tailWord_1684564) baseStart_1684564 baseEnd_1684564 := by
    simpa [prefixWord, tailWord_1684564, baseEnd_1684564] using wordTrace_append hprefix tailTrace_1684564
  have hstable : (prefixWord ++ tailWord_1684564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684564).length < 2 ^ (prefixWord ++ tailWord_1684564).sum := by decide
  have hdescent : baseEnd_1684564 < baseStart_1684564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684568 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 2, 2, 2]
def baseStart_1684568 : Nat := 118140960795 + 1684568 * 2 ^ 59
def prefixEnd_1684568 : Nat := 4983230072969 + 3 ^ 40 * 1684568 * 2
def baseEnd_1684568 : Nat := 864993079183270353652819

theorem tailTrace_1684568 : CollatzResearch.WordTrace tailWord_1684568 prefixEnd_1684568 864993079183270353652819 := by
  unfold tailWord_1684568
  simp only [CollatzResearch.WordTrace]
  refine ⟨30720621280552656077219179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40960828374070208102958905 30720621280552656077219179)
  ·
    refine ⟨46080931920828984115828769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30720621280552656077219179 46080931920828984115828769)
    ·
      refine ⟨34560698940621738086871577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46080931920828984115828769 34560698940621738086871577)
      ·
        refine ⟨25920524205466303565153683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34560698940621738086871577 25920524205466303565153683)
        ·
          refine ⟨38880786308199455347730525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25920524205466303565153683 38880786308199455347730525)
          ·
            refine ⟨14580294865574795755398947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38880786308199455347730525 14580294865574795755398947)
            ·
              refine ⟨21870442298362193633098421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14580294865574795755398947 21870442298362193633098421)
              ·
                refine ⟨2050353965471455653102977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21870442298362193633098421 2050353965471455653102977)
                ·
                  refine ⟨1537765474103591739827233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2050353965471455653102977 1537765474103591739827233)
                  ·
                    refine ⟨1153324105577693804870425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1537765474103591739827233 1153324105577693804870425)
                    ·
                      refine ⟨864993079183270353652819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1153324105577693804870425 864993079183270353652819)
                      ·
                        rfl

theorem cell23_1684568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_1684568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684568 prefixEnd_1684568 := by exact prefixLift 1684568
  have htrace : WordTrace (prefixWord ++ tailWord_1684568) baseStart_1684568 baseEnd_1684568 := by
    simpa [prefixWord, tailWord_1684568, baseEnd_1684568] using wordTrace_append hprefix tailTrace_1684568
  have hstable : (prefixWord ++ tailWord_1684568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684568).length < 2 ^ (prefixWord ++ tailWord_1684568).sum := by decide
  have hdescent : baseEnd_1684568 < baseStart_1684568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684591 : List Nat := [1, 1, 2, 1, 3, 3, 4, 3, 5]
def baseStart_1684591 : Nat := 118140960795 + 1684591 * 2 ^ 59
def prefixEnd_1684591 : Nat := 4983230072969 + 3 ^ 40 * 1684591 * 2
def baseEnd_1684591 : Nat := 96111654359813751518357

theorem tailTrace_1684591 : CollatzResearch.WordTrace tailWord_1684591 prefixEnd_1684591 96111654359813751518357 := by
  unfold tailWord_1684591
  simp only [CollatzResearch.WordTrace]
  refine ⟨61442081440021987082525627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40961387626681324721683751 61442081440021987082525627)
  ·
    refine ⟨92163122160032980623788441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61442081440021987082525627 92163122160032980623788441)
    ·
      refine ⟨69122341620024735467841331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92163122160032980623788441 69122341620024735467841331)
      ·
        refine ⟨103683512430037103201761997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69122341620024735467841331 103683512430037103201761997)
        ·
          refine ⟨38881317161263913700660749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103683512430037103201761997 38881317161263913700660749)
          ·
            refine ⟨14580493935473967637747781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38881317161263913700660749 14580493935473967637747781)
            ·
              refine ⟨2733842612901368932077709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14580493935473967637747781 2733842612901368932077709)
              ·
                refine ⟨1025190979838013349529141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2733842612901368932077709 1025190979838013349529141)
                ·
                  refine ⟨96111654359813751518357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1025190979838013349529141 96111654359813751518357)
                  ·
                    rfl

theorem cell23_1684591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 5].length) (baseStart_1684591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684591 prefixEnd_1684591 := by exact prefixLift 1684591
  have htrace : WordTrace (prefixWord ++ tailWord_1684591) baseStart_1684591 baseEnd_1684591 := by
    simpa [prefixWord, tailWord_1684591, baseEnd_1684591] using wordTrace_append hprefix tailTrace_1684591
  have hstable : (prefixWord ++ tailWord_1684591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684591).length < 2 ^ (prefixWord ++ tailWord_1684591).sum := by decide
  have hdescent : baseEnd_1684591 < baseStart_1684591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684604 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_1684604 : Nat := 118140960795 + 1684604 * 2 ^ 59
def prefixEnd_1684604 : Nat := 4983230072969 + 3 ^ 40 * 1684604 * 2
def baseEnd_1684604 : Nat := 288337188162277404267551

theorem tailTrace_1684604 : CollatzResearch.WordTrace tailWord_1684604 prefixEnd_1684604 288337188162277404267551 := by
  unfold tailWord_1684604
  simp only [CollatzResearch.WordTrace]
  refine ⟨30721277794487445151374433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40961703725983260201832577 30721277794487445151374433)
  ·
    refine ⟨23040958345865583863530825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30721277794487445151374433 23040958345865583863530825)
    ·
      refine ⟨17280718759399187897648119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23040958345865583863530825 17280718759399187897648119)
      ·
        refine ⟨25921078139098781846472179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17280718759399187897648119 25921078139098781846472179)
        ·
          refine ⟨38881617208648172769708269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25921078139098781846472179 38881617208648172769708269)
          ·
            refine ⟨14580606453243064788640601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38881617208648172769708269 14580606453243064788640601)
            ·
              refine ⟨10935454839932298591480451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14580606453243064788640601 10935454839932298591480451)
              ·
                refine ⟨16403182259898447887220677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10935454839932298591480451 16403182259898447887220677)
                ·
                  refine ⟨3075596673730958978853877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16403182259898447887220677 3075596673730958978853877)
                  ·
                    refine ⟨288337188162277404267551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3075596673730958978853877 288337188162277404267551)
                    ·
                      rfl

theorem cell23_1684604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_1684604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684604 prefixEnd_1684604 := by exact prefixLift 1684604
  have htrace : WordTrace (prefixWord ++ tailWord_1684604) baseStart_1684604 baseEnd_1684604 := by
    simpa [prefixWord, tailWord_1684604, baseEnd_1684604] using wordTrace_append hprefix tailTrace_1684604
  have hstable : (prefixWord ++ tailWord_1684604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684604).length < 2 ^ (prefixWord ++ tailWord_1684604).sum := by decide
  have hdescent : baseEnd_1684604 < baseStart_1684604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684624 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 4]
def baseStart_1684624 : Nat := 118140960795 + 1684624 * 2 ^ 59
def prefixEnd_1684624 : Nat := 4983230072969 + 3 ^ 40 * 1684624 * 2
def baseEnd_1684624 : Nat := 865021834099922134552561

theorem tailTrace_1684624 : CollatzResearch.WordTrace tailWord_1684624 prefixEnd_1684624 865021834099922134552561 := by
  unfold tailWord_1684624
  simp only [CollatzResearch.WordTrace]
  refine ⟨30721642524451216859238463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40962190032601622478984617 30721642524451216859238463)
  ·
    refine ⟨46082463786676825288857695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30721642524451216859238463 46082463786676825288857695)
    ·
      refine ⟨69123695680015237933286543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46082463786676825288857695 69123695680015237933286543)
      ·
        refine ⟨103685543520022856899929815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69123695680015237933286543 103685543520022856899929815)
        ·
          refine ⟨155528315280034285349894723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103685543520022856899929815 155528315280034285349894723)
          ·
            refine ⟨233292472920051428024842085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155528315280034285349894723 233292472920051428024842085)
            ·
              refine ⟨43742338672509642754657891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233292472920051428024842085 43742338672509642754657891)
              ·
                refine ⟨65613508008764464131986837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43742338672509642754657891 65613508008764464131986837)
                ·
                  refine ⟨3075633187910834256186883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65613508008764464131986837 3075633187910834256186883)
                  ·
                    refine ⟨4613449781866251384280325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3075633187910834256186883 4613449781866251384280325)
                    ·
                      refine ⟨865021834099922134552561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4613449781866251384280325 865021834099922134552561)
                      ·
                        rfl

theorem cell23_1684624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_1684624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684624 prefixEnd_1684624 := by exact prefixLift 1684624
  have htrace : WordTrace (prefixWord ++ tailWord_1684624) baseStart_1684624 baseEnd_1684624 := by
    simpa [prefixWord, tailWord_1684624, baseEnd_1684624] using wordTrace_append hprefix tailTrace_1684624
  have hstable : (prefixWord ++ tailWord_1684624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684624).length < 2 ^ (prefixWord ++ tailWord_1684624).sum := by decide
  have hdescent : baseEnd_1684624 < baseStart_1684624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684641 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1684641 : Nat := 118140960795 + 1684641 * 2 ^ 59
def prefixEnd_1684641 : Nat := 4983230072969 + 3 ^ 40 * 1684641 * 2
def baseEnd_1684641 : Nat := 865030563271048568039983

theorem tailTrace_1684641 : CollatzResearch.WordTrace tailWord_1684641 prefixEnd_1684641 865030563271048568039983 := by
  unfold tailWord_1684641
  simp only [CollatzResearch.WordTrace]
  refine ⟨61443905089840845621845777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40962603393227230414563851 61443905089840845621845777)
  ·
    refine ⟨46082928817380634216384333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61443905089840845621845777 46082928817380634216384333)
    ·
      refine ⟨17281098306517737831144125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46082928817380634216384333 17281098306517737831144125)
      ·
        refine ⟨6480411864944151686679047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17281098306517737831144125 6480411864944151686679047)
        ·
          refine ⟨9720617797416227530018571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6480411864944151686679047 9720617797416227530018571)
          ·
            refine ⟨14580926696124341295027857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9720617797416227530018571 14580926696124341295027857)
            ·
              refine ⟨10935695022093255971270893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14580926696124341295027857 10935695022093255971270893)
              ·
                refine ⟨4100885633284970989226585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10935695022093255971270893 4100885633284970989226585)
                ·
                  refine ⟨3075664224963728241919939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4100885633284970989226585 3075664224963728241919939)
                  ·
                    refine ⟨4613496337445592362879909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3075664224963728241919939 4613496337445592362879909)
                    ·
                      refine ⟨865030563271048568039983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4613496337445592362879909 865030563271048568039983)
                      ·
                        rfl

theorem cell23_1684641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1684641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684641 prefixEnd_1684641 := by exact prefixLift 1684641
  have htrace : WordTrace (prefixWord ++ tailWord_1684641) baseStart_1684641 baseEnd_1684641 := by
    simpa [prefixWord, tailWord_1684641, baseEnd_1684641] using wordTrace_append hprefix tailTrace_1684641
  have hstable : (prefixWord ++ tailWord_1684641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684641).length < 2 ^ (prefixWord ++ tailWord_1684641).sum := by decide
  have hdescent : baseEnd_1684641 < baseStart_1684641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684642 : List Nat := [3, 3, 1, 3, 3, 1, 1, 3, 5]
def baseStart_1684642 : Nat := 118140960795 + 1684642 * 2 ^ 59
def prefixEnd_1684642 : Nat := 4983230072969 + 3 ^ 40 * 1684642 * 2
def baseEnd_1684642 : Nat := 96114564083522562680831

theorem tailTrace_1684642 : CollatzResearch.WordTrace tailWord_1684642 prefixEnd_1684642 96114564083522562680831 := by
  unfold tailWord_1684642
  simp only [CollatzResearch.WordTrace]
  refine ⟨15360985390709305698158045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40962627708558148528421453 15360985390709305698158045)
  ·
    refine ⟨5760369521515989636809267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15360985390709305698158045 5760369521515989636809267)
    ·
      refine ⟨8640554282273984455213901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5760369521515989636809267 8640554282273984455213901)
      ·
        refine ⟨3240207855852744170705213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8640554282273984455213901 3240207855852744170705213)
        ·
          refine ⟨1215077945944779064014455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3240207855852744170705213 1215077945944779064014455)
          ·
            refine ⟨1822616918917168596021683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215077945944779064014455 1822616918917168596021683)
            ·
              refine ⟨2733925378375752894032525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822616918917168596021683 2733925378375752894032525)
              ·
                refine ⟨1025222016890907335262197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2733925378375752894032525 1025222016890907335262197)
                ·
                  refine ⟨96114564083522562680831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1025222016890907335262197 96114564083522562680831)
                  ·
                    rfl

theorem cell23_1684642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_1684642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684642 prefixEnd_1684642 := by exact prefixLift 1684642
  have htrace : WordTrace (prefixWord ++ tailWord_1684642) baseStart_1684642 baseEnd_1684642 := by
    simpa [prefixWord, tailWord_1684642, baseEnd_1684642] using wordTrace_append hprefix tailTrace_1684642
  have hstable : (prefixWord ++ tailWord_1684642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684642).length < 2 ^ (prefixWord ++ tailWord_1684642).sum := by decide
  have hdescent : baseEnd_1684642 < baseStart_1684642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684668 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_1684668 : Nat := 118140960795 + 1684668 * 2 ^ 59
def prefixEnd_1684668 : Nat := 4983230072969 + 3 ^ 40 * 1684668 * 2
def baseEnd_1684668 : Nat := 288348142416239987467453

theorem tailTrace_1684668 : CollatzResearch.WordTrace tailWord_1684668 prefixEnd_1684668 288348142416239987467453 := by
  unfold tailWord_1684668
  simp only [CollatzResearch.WordTrace]
  refine ⟨30722444930371514616539329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40963259907162019488719105 30722444930371514616539329)
  ·
    refine ⟨23041833697778635962404497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30722444930371514616539329 23041833697778635962404497)
    ·
      refine ⟨17281375273333976971803373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23041833697778635962404497 17281375273333976971803373)
      ·
        refine ⟨6480515727500241364426265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17281375273333976971803373 6480515727500241364426265)
        ·
          refine ⟨4860386795625181023319699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6480515727500241364426265 4860386795625181023319699)
          ·
            refine ⟨7290580193437771534979549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860386795625181023319699 7290580193437771534979549)
            ·
              refine ⟨2733967572539164325617331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7290580193437771534979549 2733967572539164325617331)
              ·
                refine ⟨4100951358808746488425997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733967572539164325617331 4100951358808746488425997)
                ·
                  refine ⟨1537856759553279933159749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4100951358808746488425997 1537856759553279933159749)
                  ·
                    refine ⟨288348142416239987467453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1537856759553279933159749 288348142416239987467453)
                    ·
                      rfl

theorem cell23_1684668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_1684668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684668 prefixEnd_1684668 := by exact prefixLift 1684668
  have htrace : WordTrace (prefixWord ++ tailWord_1684668) baseStart_1684668 baseEnd_1684668 := by
    simpa [prefixWord, tailWord_1684668, baseEnd_1684668] using wordTrace_append hprefix tailTrace_1684668
  have hstable : (prefixWord ++ tailWord_1684668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684668).length < 2 ^ (prefixWord ++ tailWord_1684668).sum := by decide
  have hdescent : baseEnd_1684668 < baseStart_1684668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684719 : List Nat := [1, 1, 2, 1, 8, 1, 2, 2, 1, 4]
def baseStart_1684719 : Nat := 118140960795 + 1684719 * 2 ^ 59
def prefixEnd_1684719 : Nat := 4983230072969 + 3 ^ 40 * 1684719 * 2
def baseEnd_1684719 : Nat := 288356871587366420954875

theorem tailTrace_1684719 : CollatzResearch.WordTrace tailWord_1684719 prefixEnd_1684719 288356871587366420954875 := by
  unfold tailWord_1684719
  simp only [CollatzResearch.WordTrace]
  refine ⟨61446749983558264943185211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40964499989038843295456807 61446749983558264943185211)
  ·
    refine ⟨92170124975337397414777817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61446749983558264943185211 92170124975337397414777817)
    ·
      refine ⟨69127593731503048061083363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92170124975337397414777817 69127593731503048061083363)
      ·
        refine ⟨103691390597254572091625045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69127593731503048061083363 103691390597254572091625045)
        ·
          refine ⟨1215133483561577016698731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 103691390597254572091625045 1215133483561577016698731)
          ·
            refine ⟨1822700225342365525048097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215133483561577016698731 1822700225342365525048097)
            ·
              refine ⟨1367025169006774143786073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1822700225342365525048097 1367025169006774143786073)
              ·
                refine ⟨1025268876755080607839555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367025169006774143786073 1025268876755080607839555)
                ·
                  refine ⟨1537903315132620911759333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025268876755080607839555 1537903315132620911759333)
                  ·
                    refine ⟨288356871587366420954875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1537903315132620911759333 288356871587366420954875)
                    ·
                      rfl

theorem cell23_1684719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 1, 4].length) (baseStart_1684719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684719 prefixEnd_1684719 := by exact prefixLift 1684719
  have htrace : WordTrace (prefixWord ++ tailWord_1684719) baseStart_1684719 baseEnd_1684719 := by
    simpa [prefixWord, tailWord_1684719, baseEnd_1684719] using wordTrace_append hprefix tailTrace_1684719
  have hstable : (prefixWord ++ tailWord_1684719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684719).length < 2 ^ (prefixWord ++ tailWord_1684719).sum := by decide
  have hdescent : baseEnd_1684719 < baseStart_1684719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684741 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_1684741 : Nat := 118140960795 + 1684741 * 2 ^ 59
def prefixEnd_1684741 : Nat := 4983230072969 + 3 ^ 40 * 1684741 * 2
def baseEnd_1684741 : Nat := 288360637112166058929841

theorem tailTrace_1684741 : CollatzResearch.WordTrace tailWord_1684741 prefixEnd_1684741 288360637112166058929841 := by
  unfold tailWord_1684741
  simp only [CollatzResearch.WordTrace]
  refine ⟨61447552389478562700486077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40965034926319041800324051 61447552389478562700486077)
  ·
    refine ⟨23042832146054461012682279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61447552389478562700486077 23042832146054461012682279)
    ·
      refine ⟨34564248219081691519023419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23042832146054461012682279 34564248219081691519023419)
      ·
        refine ⟨51846372328622537278535129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34564248219081691519023419 51846372328622537278535129)
        ·
          refine ⟨38884779246466902958901347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51846372328622537278535129 38884779246466902958901347)
          ·
            refine ⟨58327168869700354438352021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38884779246466902958901347 58327168869700354438352021)
            ·
              refine ⟨2734086040767204114297751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58327168869700354438352021 2734086040767204114297751)
              ·
                refine ⟨4101129061150806171446627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734086040767204114297751 4101129061150806171446627)
                ·
                  refine ⟨6151693591726209257169941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101129061150806171446627 6151693591726209257169941)
                  ·
                    refine ⟨288360637112166058929841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6151693591726209257169941 288360637112166058929841)
                    ·
                      rfl

theorem cell23_1684741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_1684741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684741 prefixEnd_1684741 := by exact prefixLift 1684741
  have htrace : WordTrace (prefixWord ++ tailWord_1684741) baseStart_1684741 baseEnd_1684741 := by
    simpa [prefixWord, tailWord_1684741, baseEnd_1684741] using wordTrace_append hprefix tailTrace_1684741
  have hstable : (prefixWord ++ tailWord_1684741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684741).length < 2 ^ (prefixWord ++ tailWord_1684741).sum := by decide
  have hdescent : baseEnd_1684741 < baseStart_1684741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684765 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1684765 : Nat := 118140960795 + 1684765 * 2 ^ 59
def prefixEnd_1684765 : Nat := 4983230072969 + 3 ^ 40 * 1684765 * 2
def baseEnd_1684765 : Nat := 865094234872206082889413

theorem tailTrace_1684765 : CollatzResearch.WordTrace tailWord_1684765 prefixEnd_1684765 865094234872206082889413 := by
  unfold tailWord_1684765
  simp only [CollatzResearch.WordTrace]
  refine ⟨61448427741391614799359749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40965618494261076532906499 61448427741391614799359749)
  ·
    refine ⟨11521580201510927774879953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61448427741391614799359749 11521580201510927774879953)
    ·
      refine ⟨8641185151133195831159965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11521580201510927774879953 8641185151133195831159965)
      ·
        refine ⟨3240444431674948436684987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8641185151133195831159965 3240444431674948436684987)
        ·
          refine ⟨4860666647512422655027481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240444431674948436684987 4860666647512422655027481)
          ·
            refine ⟨3645499985634316991270611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4860666647512422655027481 3645499985634316991270611)
            ·
              refine ⟨5468249978451475486905917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3645499985634316991270611 5468249978451475486905917)
              ·
                refine ⟨2050593741919303307589719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5468249978451475486905917 2050593741919303307589719)
                ·
                  refine ⟨3075890612878954961384579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050593741919303307589719 3075890612878954961384579)
                  ·
                    refine ⟨4613835919318432442076869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3075890612878954961384579 4613835919318432442076869)
                    ·
                      refine ⟨865094234872206082889413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4613835919318432442076869 865094234872206082889413)
                      ·
                        rfl

theorem cell23_1684765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1684765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684765 prefixEnd_1684765 := by exact prefixLift 1684765
  have htrace : WordTrace (prefixWord ++ tailWord_1684765) baseStart_1684765 baseEnd_1684765 := by
    simpa [prefixWord, tailWord_1684765, baseEnd_1684765] using wordTrace_append hprefix tailTrace_1684765
  have hstable : (prefixWord ++ tailWord_1684765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684765).length < 2 ^ (prefixWord ++ tailWord_1684765).sum := by decide
  have hdescent : baseEnd_1684765 < baseStart_1684765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684825 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 1, 3, 2]
def baseStart_1684825 : Nat := 118140960795 + 1684825 * 2 ^ 59
def prefixEnd_1684825 : Nat := 4983230072969 + 3 ^ 40 * 1684825 * 2
def baseEnd_1684825 : Nat := 865125043711475848139137

theorem tailTrace_1684825 : CollatzResearch.WordTrace tailWord_1684825 prefixEnd_1684825 865125043711475848139137 := by
  unfold tailWord_1684825
  simp only [CollatzResearch.WordTrace]
  refine ⟨61450616121174245046543929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40967077414116163364362619 61450616121174245046543929)
  ·
    refine ⟨46087962090880683784907947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61450616121174245046543929 46087962090880683784907947)
    ·
      refine ⟨69131943136321025677361921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46087962090880683784907947 69131943136321025677361921)
      ·
        refine ⟨51848957352240769258021441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69131943136321025677361921 51848957352240769258021441)
        ·
          refine ⟨38886718014180576943516081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51848957352240769258021441 38886718014180576943516081)
          ·
            refine ⟨29165038510635432707637061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38886718014180576943516081 29165038510635432707637061)
            ·
              refine ⟨5468444720744143632681949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29165038510635432707637061 5468444720744143632681949)
              ·
                refine ⟨2050666770279053862255731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5468444720744143632681949 2050666770279053862255731)
                ·
                  refine ⟨3076000155418580793383597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050666770279053862255731 3076000155418580793383597)
                  ·
                    refine ⟨1153500058281967797518849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3076000155418580793383597 1153500058281967797518849)
                    ·
                      refine ⟨865125043711475848139137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1153500058281967797518849 865125043711475848139137)
                      ·
                        rfl

theorem cell23_1684825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_1684825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684825 prefixEnd_1684825 := by exact prefixLift 1684825
  have htrace : WordTrace (prefixWord ++ tailWord_1684825) baseStart_1684825 baseEnd_1684825 := by
    simpa [prefixWord, tailWord_1684825, baseEnd_1684825] using wordTrace_append hprefix tailTrace_1684825
  have hstable : (prefixWord ++ tailWord_1684825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684825).length < 2 ^ (prefixWord ++ tailWord_1684825).sum := by decide
  have hdescent : baseEnd_1684825 < baseStart_1684825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684861 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 9]
def baseStart_1684861 : Nat := 118140960795 + 1684861 * 2 ^ 59
def prefixEnd_1684861 : Nat := 4983230072969 + 3 ^ 40 * 1684861 * 2
def baseEnd_1684861 : Nat := 96127058779448634143219

theorem tailTrace_1684861 : CollatzResearch.WordTrace tailWord_1684861 prefixEnd_1684861 96127058779448634143219 := by
  unfold tailWord_1684861
  simp only [CollatzResearch.WordTrace]
  refine ⟨61451929149043823194854437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40967952766029215463236291 61451929149043823194854437)
  ·
    refine ⟨11522236715445716849035207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61451929149043823194854437 11522236715445716849035207)
    ·
      refine ⟨17283355073168575273552811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11522236715445716849035207 17283355073168575273552811)
      ·
        refine ⟨25925032609752862910329217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17283355073168575273552811 25925032609752862910329217)
        ·
          refine ⟨19443774457314647182746913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25925032609752862910329217 19443774457314647182746913)
          ·
            refine ⟨14582830842985985387060185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19443774457314647182746913 14582830842985985387060185)
            ·
              refine ⟨10937123132239489040295139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14582830842985985387060185 10937123132239489040295139)
              ·
                refine ⟨16405684698359233560442709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10937123132239489040295139 16405684698359233560442709)
                ·
                  refine ⟨96127058779448634143219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16405684698359233560442709 96127058779448634143219)
                  ·
                    rfl

theorem cell23_1684861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_1684861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684861 prefixEnd_1684861 := by exact prefixLift 1684861
  have htrace : WordTrace (prefixWord ++ tailWord_1684861) baseStart_1684861 baseEnd_1684861 := by
    simpa [prefixWord, tailWord_1684861, baseEnd_1684861] using wordTrace_append hprefix tailTrace_1684861
  have hstable : (prefixWord ++ tailWord_1684861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684861).length < 2 ^ (prefixWord ++ tailWord_1684861).sum := by decide
  have hdescent : baseEnd_1684861 < baseStart_1684861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684895 : List Nat := [1, 1, 2, 5, 1, 3, 1, 4, 5]
def baseStart_1684895 : Nat := 118140960795 + 1684895 * 2 ^ 59
def prefixEnd_1684895 : Nat := 4983230072969 + 3 ^ 40 * 1684895 * 2
def baseEnd_1684895 : Nat := 96128998595254508251535

theorem tailTrace_1684895 : CollatzResearch.WordTrace tailWord_1684895 prefixEnd_1684895 96128998595254508251535 := by
  unfold tailWord_1684895
  simp only [CollatzResearch.WordTrace]
  refine ⟨61453169230920647001592139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40968779487280431334394759 61453169230920647001592139)
  ·
    refine ⟨92179753846380970502388209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61453169230920647001592139 92179753846380970502388209)
    ·
      refine ⟨69134815384785727876791157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92179753846380970502388209 69134815384785727876791157)
      ·
        refine ⟨6481388942323661988449171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69134815384785727876791157 6481388942323661988449171)
        ·
          refine ⟨9722083413485492982673757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6481388942323661988449171 9722083413485492982673757)
          ·
            refine ⟨3645781280057059868502659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9722083413485492982673757 3645781280057059868502659)
            ·
              refine ⟨5468671920085589802753989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3645781280057059868502659 5468671920085589802753989)
              ·
                refine ⟨1025375985016048088016373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5468671920085589802753989 1025375985016048088016373)
                ·
                  refine ⟨96128998595254508251535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1025375985016048088016373 96128998595254508251535)
                  ·
                    rfl

theorem cell23_1684895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 5].length) (baseStart_1684895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684895 prefixEnd_1684895 := by exact prefixLift 1684895
  have htrace : WordTrace (prefixWord ++ tailWord_1684895) baseStart_1684895 baseEnd_1684895 := by
    simpa [prefixWord, tailWord_1684895, baseEnd_1684895] using wordTrace_append hprefix tailTrace_1684895
  have hstable : (prefixWord ++ tailWord_1684895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684895).length < 2 ^ (prefixWord ++ tailWord_1684895).sum := by decide
  have hdescent : baseEnd_1684895 < baseStart_1684895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684901 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_1684901 : Nat := 118140960795 + 1684901 * 2 ^ 59
def prefixEnd_1684901 : Nat := 4983230072969 + 3 ^ 40 * 1684901 * 2
def baseEnd_1684901 : Nat := 865164068241217550788787

theorem tailTrace_1684901 : CollatzResearch.WordTrace tailWord_1684901 prefixEnd_1684901 865164068241217550788787 := by
  unfold tailWord_1684901
  simp only [CollatzResearch.WordTrace]
  refine ⟨61453388068898910026310557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40968925379265940017540371 61453388068898910026310557)
  ·
    refine ⟨23045020525837091259866459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61453388068898910026310557 23045020525837091259866459)
    ·
      refine ⟨34567530788755636889799689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23045020525837091259866459 34567530788755636889799689)
      ·
        refine ⟨25925648091566727667349767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34567530788755636889799689 25925648091566727667349767)
        ·
          refine ⟨38888472137350091501024651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25925648091566727667349767 38888472137350091501024651)
          ·
            refine ⟨58332708206025137251536977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38888472137350091501024651 58332708206025137251536977)
            ·
              refine ⟨43749531154518852938652733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58332708206025137251536977 43749531154518852938652733)
              ·
                refine ⟨16406074182944569851994775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43749531154518852938652733 16406074182944569851994775)
                ·
                  refine ⟨24609111274416854777992163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16406074182944569851994775 24609111274416854777992163)
                  ·
                    refine ⟨36913666911625282166988245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24609111274416854777992163 36913666911625282166988245)
                    ·
                      refine ⟨865164068241217550788787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36913666911625282166988245 865164068241217550788787)
                      ·
                        rfl

theorem cell23_1684901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_1684901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684901 prefixEnd_1684901 := by exact prefixLift 1684901
  have htrace : WordTrace (prefixWord ++ tailWord_1684901) baseStart_1684901 baseEnd_1684901 := by
    simpa [prefixWord, tailWord_1684901, baseEnd_1684901] using wordTrace_append hprefix tailTrace_1684901
  have hstable : (prefixWord ++ tailWord_1684901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684901).length < 2 ^ (prefixWord ++ tailWord_1684901).sum := by decide
  have hdescent : baseEnd_1684901 < baseStart_1684901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684965 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1684965 : Nat := 118140960795 + 1684965 * 2 ^ 59
def prefixEnd_1684965 : Nat := 4983230072969 + 3 ^ 40 * 1684965 * 2
def baseEnd_1684965 : Nat := 865196931003105300388493

theorem tailTrace_1684965 : CollatzResearch.WordTrace tailWord_1684965 prefixEnd_1684965 865196931003105300388493 := by
  unfold tailWord_1684965
  simp only [CollatzResearch.WordTrace]
  refine ⟨61455722340667048956640349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40970481560444699304426899 61455722340667048956640349)
  ·
    refine ⟨23045895877750143358740131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61455722340667048956640349 23045895877750143358740131)
    ·
      refine ⟨34568843816625215038110197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23045895877750143358740131 34568843816625215038110197)
      ·
        refine ⟨3240829107808613909822831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34568843816625215038110197 3240829107808613909822831)
        ·
          refine ⟨4861243661712920864734247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240829107808613909822831 4861243661712920864734247)
          ·
            refine ⟨7291865492569381297101371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861243661712920864734247 7291865492569381297101371)
            ·
              refine ⟨10937798238854071945652057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291865492569381297101371 10937798238854071945652057)
              ·
                refine ⟨8203348679140553959239043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10937798238854071945652057 8203348679140553959239043)
                ·
                  refine ⟨12305023018710830938858565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8203348679140553959239043 12305023018710830938858565)
                  ·
                    refine ⟨2307191816008280801035981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12305023018710830938858565 2307191816008280801035981)
                    ·
                      refine ⟨865196931003105300388493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2307191816008280801035981 865196931003105300388493)
                      ·
                        rfl

theorem cell23_1684965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1684965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684965 prefixEnd_1684965 := by exact prefixLift 1684965
  have htrace : WordTrace (prefixWord ++ tailWord_1684965) baseStart_1684965 baseEnd_1684965 := by
    simpa [prefixWord, tailWord_1684965, baseEnd_1684965] using wordTrace_append hprefix tailTrace_1684965
  have hstable : (prefixWord ++ tailWord_1684965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684965).length < 2 ^ (prefixWord ++ tailWord_1684965).sum := by decide
  have hdescent : baseEnd_1684965 < baseStart_1684965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684989 : List Nat := [1, 4, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_1684989 : Nat := 118140960795 + 1684989 * 2 ^ 59
def prefixEnd_1684989 : Nat := 4983230072969 + 3 ^ 40 * 1684989 * 2
def baseEnd_1684989 : Nat := 288403084846271068829461

theorem tailTrace_1684989 : CollatzResearch.WordTrace tailWord_1684989 prefixEnd_1684989 288403084846271068829461 := by
  unfold tailWord_1684989
  simp only [CollatzResearch.WordTrace]
  refine ⟨61456597692580101055514021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40971065128386734037009347 61456597692580101055514021)
  ·
    refine ⟨11523112067358768947908879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61456597692580101055514021 11523112067358768947908879)
    ·
      refine ⟨17284668101038153421863319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11523112067358768947908879 17284668101038153421863319)
      ·
        refine ⟨25927002151557230132794979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17284668101038153421863319 25927002151557230132794979)
        ·
          refine ⟨38890503227335845199192469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25927002151557230132794979 38890503227335845199192469)
          ·
            refine ⟨1822992338781367743712147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38890503227335845199192469 1822992338781367743712147)
            ·
              refine ⟨2734488508172051615568221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822992338781367743712147 2734488508172051615568221)
              ·
                refine ⟨1025433190564519355838083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2734488508172051615568221 1025433190564519355838083)
                ·
                  refine ⟨1538149785846779033757125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025433190564519355838083 1538149785846779033757125)
                  ·
                    refine ⟨288403084846271068829461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1538149785846779033757125 288403084846271068829461)
                    ·
                      rfl

theorem cell23_1684989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_1684989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1684989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1684989 prefixEnd_1684989 := by exact prefixLift 1684989
  have htrace : WordTrace (prefixWord ++ tailWord_1684989) baseStart_1684989 baseEnd_1684989 := by
    simpa [prefixWord, tailWord_1684989, baseEnd_1684989] using wordTrace_append hprefix tailTrace_1684989
  have hstable : (prefixWord ++ tailWord_1684989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684989).length < 2 ^ (prefixWord ++ tailWord_1684989).sum := by decide
  have hdescent : baseEnd_1684989 < baseStart_1684989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685006 : List Nat := [4, 1, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_1685006 : Nat := 118140960795 + 1685006 * 2 ^ 59
def prefixEnd_1685006 : Nat := 4983230072969 + 3 ^ 40 * 1685006 * 2
def baseEnd_1685006 : Nat := 288405994569979879991935

theorem tailTrace_1685006 : CollatzResearch.WordTrace tailWord_1685006 prefixEnd_1685006 288405994569979879991935 := by
  unfold tailWord_1685006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682152216689814119860359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40971478489012341972588581 7682152216689814119860359)
  ·
    refine ⟨11523228325034721179790539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7682152216689814119860359 11523228325034721179790539)
    ·
      refine ⟨17284842487552081769685809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11523228325034721179790539 17284842487552081769685809)
      ·
        refine ⟨12963631865664061327264357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17284842487552081769685809 12963631865664061327264357)
        ·
          refine ⟨2430680974812011498862067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12963631865664061327264357 2430680974812011498862067)
          ·
            refine ⟨3646021462218017248293101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430680974812011498862067 3646021462218017248293101)
            ·
              refine ⟨1367258048331756468109913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3646021462218017248293101 1367258048331756468109913)
              ·
                refine ⟨1025443536248817351082435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367258048331756468109913 1025443536248817351082435)
                ·
                  refine ⟨1538165304373226026623653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025443536248817351082435 1538165304373226026623653)
                  ·
                    refine ⟨288405994569979879991935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1538165304373226026623653 288405994569979879991935)
                    ·
                      rfl

theorem cell23_1685006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_1685006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685006 prefixEnd_1685006 := by exact prefixLift 1685006
  have htrace : WordTrace (prefixWord ++ tailWord_1685006) baseStart_1685006 baseEnd_1685006 := by
    simpa [prefixWord, tailWord_1685006, baseEnd_1685006] using wordTrace_append hprefix tailTrace_1685006
  have hstable : (prefixWord ++ tailWord_1685006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685006).length < 2 ^ (prefixWord ++ tailWord_1685006).sum := by decide
  have hdescent : baseEnd_1685006 < baseStart_1685006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685018 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1685018 : Nat := 118140960795 + 1685018 * 2 ^ 59
def prefixEnd_1685018 : Nat := 4983230072969 + 3 ^ 40 * 1685018 * 2
def baseEnd_1685018 : Nat := 865224145477793593025749

theorem tailTrace_1685018 : CollatzResearch.WordTrace tailWord_1685018 prefixEnd_1685018 865224145477793593025749 := by
  unfold tailWord_1685018
  simp only [CollatzResearch.WordTrace]
  refine ⟨15364413852368759752079927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40971770272983359338879805 15364413852368759752079927)
  ·
    refine ⟨23046620778553139628119891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15364413852368759752079927 23046620778553139628119891)
    ·
      refine ⟨34569931167829709442179837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23046620778553139628119891 34569931167829709442179837)
      ·
        refine ⟨12963724187936141040817439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34569931167829709442179837 12963724187936141040817439)
        ·
          refine ⟨19445586281904211561226159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12963724187936141040817439 19445586281904211561226159)
          ·
            refine ⟨29168379422856317341839239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19445586281904211561226159 29168379422856317341839239)
            ·
              refine ⟨43752569134284476012758859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29168379422856317341839239 43752569134284476012758859)
              ·
                refine ⟨65628853701426714019138289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43752569134284476012758859 65628853701426714019138289)
                ·
                  refine ⟨49221640276070035514353717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65628853701426714019138289 49221640276070035514353717)
                  ·
                    refine ⟨4614528775881565829470661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49221640276070035514353717 4614528775881565829470661)
                    ·
                      refine ⟨865224145477793593025749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4614528775881565829470661 865224145477793593025749)
                      ·
                        rfl

theorem cell23_1685018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1685018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685018 prefixEnd_1685018 := by exact prefixLift 1685018
  have htrace : WordTrace (prefixWord ++ tailWord_1685018) baseStart_1685018 baseEnd_1685018 := by
    simpa [prefixWord, tailWord_1685018, baseEnd_1685018] using wordTrace_append hprefix tailTrace_1685018
  have hstable : (prefixWord ++ tailWord_1685018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685018).length < 2 ^ (prefixWord ++ tailWord_1685018).sum := by decide
  have hdescent : baseEnd_1685018 < baseStart_1685018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685032 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1685032 : Nat := 118140960795 + 1685032 * 2 ^ 59
def prefixEnd_1685032 : Nat := 4983230072969 + 3 ^ 40 * 1685032 * 2
def baseEnd_1685032 : Nat := 288410444735652179416895

theorem tailTrace_1685032 : CollatzResearch.WordTrace tailWord_1685032 prefixEnd_1685032 288410444735652179416895 := by
  unfold tailWord_1685032
  simp only [CollatzResearch.WordTrace]
  refine ⟨30729083015712159699664675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40972110687616212932886233 30729083015712159699664675)
  ·
    refine ⟨46093624523568239549497013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30729083015712159699664675 46093624523568239549497013)
    ·
      refine ⟨4321277299084522457765345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46093624523568239549497013 4321277299084522457765345)
      ·
        refine ⟨3240957974313391843324009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4321277299084522457765345 3240957974313391843324009)
        ·
          refine ⟨2430718480735043882493007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3240957974313391843324009 2430718480735043882493007)
          ·
            refine ⟨3646077721102565823739511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430718480735043882493007 3646077721102565823739511)
            ·
              refine ⟨5469116581653848735609267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646077721102565823739511 5469116581653848735609267)
              ·
                refine ⟨8203674872480773103413901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469116581653848735609267 8203674872480773103413901)
                ·
                  refine ⟨3076378077180289913780213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8203674872480773103413901 3076378077180289913780213)
                  ·
                    refine ⟨288410444735652179416895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3076378077180289913780213 288410444735652179416895)
                    ·
                      rfl

theorem cell23_1685032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1685032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685032 prefixEnd_1685032 := by exact prefixLift 1685032
  have htrace : WordTrace (prefixWord ++ tailWord_1685032) baseStart_1685032 baseEnd_1685032 := by
    simpa [prefixWord, tailWord_1685032, baseEnd_1685032] using wordTrace_append hprefix tailTrace_1685032
  have hstable : (prefixWord ++ tailWord_1685032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685032).length < 2 ^ (prefixWord ++ tailWord_1685032).sum := by decide
  have hdescent : baseEnd_1685032 < baseStart_1685032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685045 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_1685045 : Nat := 118140960795 + 1685045 * 2 ^ 59
def prefixEnd_1685045 : Nat := 4983230072969 + 3 ^ 40 * 1685045 * 2
def baseEnd_1685045 : Nat := 288412669818488329129375

theorem tailTrace_1685045 : CollatzResearch.WordTrace tailWord_1685045 prefixEnd_1685045 288412669818488329129375 := by
  unfold tailWord_1685045
  simp only [CollatzResearch.WordTrace]
  refine ⟨61458640180377222619552589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40972426786918148413035059 61458640180377222619552589)
  ·
    refine ⟨23046990067641458482332221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61458640180377222619552589 23046990067641458482332221)
    ·
      refine ⟨8642621275365546930874583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23046990067641458482332221 8642621275365546930874583)
      ·
        refine ⟨12963931913048320396311875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8642621275365546930874583 12963931913048320396311875)
        ·
          refine ⟨19445897869572480594467813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12963931913048320396311875 19445897869572480594467813)
          ·
            refine ⟨3646105850544840111462715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19445897869572480594467813 3646105850544840111462715)
            ·
              refine ⟨5469158775817260167194073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646105850544840111462715 5469158775817260167194073)
              ·
                refine ⟨4101869081862945125395555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5469158775817260167194073 4101869081862945125395555)
                ·
                  refine ⟨6152803622794417688093333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101869081862945125395555 6152803622794417688093333)
                  ·
                    refine ⟨288412669818488329129375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6152803622794417688093333 288412669818488329129375)
                    ·
                      rfl

theorem cell23_1685045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_1685045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685045 prefixEnd_1685045 := by exact prefixLift 1685045
  have htrace : WordTrace (prefixWord ++ tailWord_1685045) baseStart_1685045 baseEnd_1685045 := by
    simpa [prefixWord, tailWord_1685045, baseEnd_1685045] using wordTrace_append hprefix tailTrace_1685045
  have hstable : (prefixWord ++ tailWord_1685045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685045).length < 2 ^ (prefixWord ++ tailWord_1685045).sum := by decide
  have hdescent : baseEnd_1685045 < baseStart_1685045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685055 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 5]
def baseStart_1685055 : Nat := 118140960795 + 1685055 * 2 ^ 59
def prefixEnd_1685055 : Nat := 4983230072969 + 3 ^ 40 * 1685055 * 2
def baseEnd_1685055 : Nat := 865243144262009948263079

theorem tailTrace_1685055 : CollatzResearch.WordTrace tailWord_1685055 prefixEnd_1685055 865243144262009948263079 := by
  unfold tailWord_1685055
  simp only [CollatzResearch.WordTrace]
  refine ⟨61459004910340994327416619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40972669940227329551611079 61459004910340994327416619)
  ·
    refine ⟨92188507365511491491124929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61459004910340994327416619 92188507365511491491124929)
    ·
      refine ⟨69141380524133618618343697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92188507365511491491124929 69141380524133618618343697)
      ·
        refine ⟨51856035393100213963757773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69141380524133618618343697 51856035393100213963757773)
        ·
          refine ⟨19446013272412580236409165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51856035393100213963757773 19446013272412580236409165)
          ·
            refine ⟨7292254977154717588653437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19446013272412580236409165 7292254977154717588653437)
            ·
              refine ⟨2734595616433019095745039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7292254977154717588653437 2734595616433019095745039)
              ·
                refine ⟨4101893424649528643617559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734595616433019095745039 4101893424649528643617559)
                ·
                  refine ⟨6152840136974292965426339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101893424649528643617559 6152840136974292965426339)
                  ·
                    refine ⟨9229260205461439448139509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6152840136974292965426339 9229260205461439448139509)
                    ·
                      refine ⟨865243144262009948263079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9229260205461439448139509 865243144262009948263079)
                      ·
                        rfl

theorem cell23_1685055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_1685055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685055 prefixEnd_1685055 := by exact prefixLift 1685055
  have htrace : WordTrace (prefixWord ++ tailWord_1685055) baseStart_1685055 baseEnd_1685055 := by
    simpa [prefixWord, tailWord_1685055, baseEnd_1685055] using wordTrace_append hprefix tailTrace_1685055
  have hstable : (prefixWord ++ tailWord_1685055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685055).length < 2 ^ (prefixWord ++ tailWord_1685055).sum := by decide
  have hdescent : baseEnd_1685055 < baseStart_1685055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685063 : List Nat := [1, 1, 4, 1, 5, 2, 2, 2, 1, 1, 3]
def baseStart_1685063 : Nat := 118140960795 + 1685063 * 2 ^ 59
def prefixEnd_1685063 : Nat := 4983230072969 + 3 ^ 40 * 1685063 * 2
def baseEnd_1685063 : Nat := 865247252107245916963043

theorem tailTrace_1685063 : CollatzResearch.WordTrace tailWord_1685063 prefixEnd_1685063 865247252107245916963043 := by
  unfold tailWord_1685063
  simp only [CollatzResearch.WordTrace]
  refine ⟨61459296694312011693707843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40972864462874674462471895 61459296694312011693707843)
  ·
    refine ⟨92188945041468017540561765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61459296694312011693707843 92188945041468017540561765)
    ·
      refine ⟨17285427195275253288855331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92188945041468017540561765 17285427195275253288855331)
      ·
        refine ⟨25928140792912879933282997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17285427195275253288855331 25928140792912879933282997)
        ·
          refine ⟨2430763199335582493745281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25928140792912879933282997 2430763199335582493745281)
          ·
            refine ⟨1823072399501686870308961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2430763199335582493745281 1823072399501686870308961)
            ·
              refine ⟨1367304299626265152731721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1823072399501686870308961 1367304299626265152731721)
              ·
                refine ⟨1025478224719698864548791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367304299626265152731721 1025478224719698864548791)
                ·
                  refine ⟨1538217337079548296823187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025478224719698864548791 1538217337079548296823187)
                  ·
                    refine ⟨2307326005619322445234781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1538217337079548296823187 2307326005619322445234781)
                    ·
                      refine ⟨865247252107245916963043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2307326005619322445234781 865247252107245916963043)
                      ·
                        rfl

theorem cell23_1685063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_1685063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685063 prefixEnd_1685063 := by exact prefixLift 1685063
  have htrace : WordTrace (prefixWord ++ tailWord_1685063) baseStart_1685063 baseEnd_1685063 := by
    simpa [prefixWord, tailWord_1685063, baseEnd_1685063] using wordTrace_append hprefix tailTrace_1685063
  have hstable : (prefixWord ++ tailWord_1685063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685063).length < 2 ^ (prefixWord ++ tailWord_1685063).sum := by decide
  have hdescent : baseEnd_1685063 < baseStart_1685063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685088 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 4, 7]
def baseStart_1685088 : Nat := 118140960795 + 1685088 * 2 ^ 59
def prefixEnd_1685088 : Nat := 4983230072969 + 3 ^ 40 * 1685088 * 2
def baseEnd_1685088 : Nat := 288420029707869439716809

theorem tailTrace_1685088 : CollatzResearch.WordTrace tailWord_1685088 prefixEnd_1685088 288420029707869439716809 := by
  unfold tailWord_1685088
  simp only [CollatzResearch.WordTrace]
  refine ⟨30730104259610720481683959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40973472346147627308911945 30730104259610720481683959)
  ·
    refine ⟨46095156389416080722525939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30730104259610720481683959 46095156389416080722525939)
    ·
      refine ⟨69142734584124121083788909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46095156389416080722525939 69142734584124121083788909)
      ·
        refine ⟨25928525469046545406420841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69142734584124121083788909 25928525469046545406420841)
        ·
          refine ⟨19446394101784909054815631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25928525469046545406420841 19446394101784909054815631)
          ·
            refine ⟨29169591152677363582223447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19446394101784909054815631 29169591152677363582223447)
            ·
              refine ⟨43754386729016045373335171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29169591152677363582223447 43754386729016045373335171)
              ·
                refine ⟨65631580093524068060002757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43754386729016045373335171 65631580093524068060002757)
                ·
                  refine ⟨12305921267535762761250517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65631580093524068060002757 12305921267535762761250517)
                  ·
                    refine ⟨288420029707869439716809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12305921267535762761250517 288420029707869439716809)
                    ·
                      rfl

theorem cell23_1685088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_1685088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685088 prefixEnd_1685088 := by exact prefixLift 1685088
  have htrace : WordTrace (prefixWord ++ tailWord_1685088) baseStart_1685088 baseEnd_1685088 := by
    simpa [prefixWord, tailWord_1685088, baseEnd_1685088] using wordTrace_append hprefix tailTrace_1685088
  have hstable : (prefixWord ++ tailWord_1685088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685088).length < 2 ^ (prefixWord ++ tailWord_1685088).sum := by decide
  have hdescent : baseEnd_1685088 < baseStart_1685088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685106 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 1, 2, 3]
def baseStart_1685106 : Nat := 118140960795 + 1685106 * 2 ^ 59
def prefixEnd_1685106 : Nat := 4983230072969 + 3 ^ 40 * 1685106 * 2
def baseEnd_1685106 : Nat := 865269331775389248725345

theorem tailTrace_1685106 : CollatzResearch.WordTrace tailWord_1685106 prefixEnd_1685106 865269331775389248725345 := by
  unfold tailWord_1685106
  simp only [CollatzResearch.WordTrace]
  refine ⟨15365216258289057509380793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40973910022104153358348781 15365216258289057509380793)
  ·
    refine ⟨11523912193716793132035595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15365216258289057509380793 11523912193716793132035595)
    ·
      refine ⟨17285868290575189698053393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11523912193716793132035595 17285868290575189698053393)
      ·
        refine ⟨12964401217931392273540045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17285868290575189698053393 12964401217931392273540045)
        ·
          refine ⟨4861650456724272102577517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12964401217931392273540045 4861650456724272102577517)
          ·
            refine ⟨1823118921271602038466569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4861650456724272102577517 1823118921271602038466569)
            ·
              refine ⟨1367339190953701528849927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1823118921271602038466569 1367339190953701528849927)
              ·
                refine ⟨2051008786430552293274891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367339190953701528849927 2051008786430552293274891)
                ·
                  refine ⟨3076513179645828439912337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051008786430552293274891 3076513179645828439912337)
                  ·
                    refine ⟨2307384884734371329934253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3076513179645828439912337 2307384884734371329934253)
                    ·
                      refine ⟨865269331775389248725345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2307384884734371329934253 865269331775389248725345)
                      ·
                        rfl

theorem cell23_1685106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_1685106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685106 prefixEnd_1685106 := by exact prefixLift 1685106
  have htrace : WordTrace (prefixWord ++ tailWord_1685106) baseStart_1685106 baseEnd_1685106 := by
    simpa [prefixWord, tailWord_1685106, baseEnd_1685106] using wordTrace_append hprefix tailTrace_1685106
  have hstable : (prefixWord ++ tailWord_1685106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685106).length < 2 ^ (prefixWord ++ tailWord_1685106).sum := by decide
  have hdescent : baseEnd_1685106 < baseStart_1685106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685182 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_1685182 : Nat := 118140960795 + 1685182 * 2 ^ 59
def prefixEnd_1685182 : Nat := 4983230072969 + 3 ^ 40 * 1685182 * 2
def baseEnd_1685182 : Nat := 96145372922792327930555

theorem tailTrace_1685182 : CollatzResearch.WordTrace tailWord_1685182 prefixEnd_1685182 96145372922792327930555 := by
  unfold tailWord_1685182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682954622610111877161225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40975757987253930011526533 7682954622610111877161225)
  ·
    refine ⟨5762215966957583907870919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7682954622610111877161225 5762215966957583907870919)
    ·
      refine ⟨8643323950436375861806379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5762215966957583907870919 8643323950436375861806379)
      ·
        refine ⟨12964985925654563792709569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8643323950436375861806379 12964985925654563792709569)
        ·
          refine ⟨9723739444240922844532177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12964985925654563792709569 9723739444240922844532177)
          ·
            refine ⟨7292804583180692133399133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9723739444240922844532177 7292804583180692133399133)
            ·
              refine ⟨2734801718692759550024675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7292804583180692133399133 2734801718692759550024675)
              ·
                refine ⟨4102202578039139325037013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734801718692759550024675 4102202578039139325037013)
                ·
                  refine ⟨96145372922792327930555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4102202578039139325037013 96145372922792327930555)
                  ·
                    rfl

theorem cell23_1685182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_1685182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685182 prefixEnd_1685182 := by exact prefixLift 1685182
  have htrace : WordTrace (prefixWord ++ tailWord_1685182) baseStart_1685182 baseEnd_1685182 := by
    simpa [prefixWord, tailWord_1685182, baseEnd_1685182] using wordTrace_append hprefix tailTrace_1685182
  have hstable : (prefixWord ++ tailWord_1685182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685182).length < 2 ^ (prefixWord ++ tailWord_1685182).sum := by decide
  have hdescent : baseEnd_1685182 < baseStart_1685182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685242 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_1685242 : Nat := 118140960795 + 1685242 * 2 ^ 59
def prefixEnd_1685242 : Nat := 4983230072969 + 3 ^ 40 * 1685242 * 2
def baseEnd_1685242 : Nat := 288446388381466905541573

theorem tailTrace_1685242 : CollatzResearch.WordTrace tailWord_1685242 prefixEnd_1685242 288446388381466905541573 := by
  unfold tailWord_1685242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15366456340165881316118495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40977216907109016842982653 15366456340165881316118495)
  ·
    refine ⟨23049684510248821974177743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15366456340165881316118495 23049684510248821974177743)
    ·
      refine ⟨34574526765373232961266615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23049684510248821974177743 34574526765373232961266615)
      ·
        refine ⟨51861790148059849441899923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34574526765373232961266615 51861790148059849441899923)
        ·
          refine ⟨77792685222089774162849885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51861790148059849441899923 77792685222089774162849885)
          ·
            refine ⟨29172256958283665311068707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77792685222089774162849885 29172256958283665311068707)
            ·
              refine ⟨43758385437425497966603061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29172256958283665311068707 43758385437425497966603061)
              ·
                refine ⟨4102348634758640434369037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43758385437425497966603061 4102348634758640434369037)
                ·
                  refine ⟨1538380738034490162888389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4102348634758640434369037 1538380738034490162888389)
                  ·
                    refine ⟨288446388381466905541573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1538380738034490162888389 288446388381466905541573)
                    ·
                      rfl

theorem cell23_1685242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_1685242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685242 prefixEnd_1685242 := by exact prefixLift 1685242
  have htrace : WordTrace (prefixWord ++ tailWord_1685242) baseStart_1685242 baseEnd_1685242 := by
    simpa [prefixWord, tailWord_1685242, baseEnd_1685242] using wordTrace_append hprefix tailTrace_1685242
  have hstable : (prefixWord ++ tailWord_1685242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685242).length < 2 ^ (prefixWord ++ tailWord_1685242).sum := by decide
  have hdescent : baseEnd_1685242 < baseStart_1685242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685245 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_1685245 : Nat := 118140960795 + 1685245 * 2 ^ 59
def prefixEnd_1685245 : Nat := 4983230072969 + 3 ^ 40 * 1685245 * 2
def baseEnd_1685245 : Nat := 865340705586364204887205

theorem tailTrace_1685245 : CollatzResearch.WordTrace tailWord_1685245 prefixEnd_1685245 865340705586364204887205 := by
  unfold tailWord_1685245
  simp only [CollatzResearch.WordTrace]
  refine ⟨61465934779652656776833189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40977289853101771184555459 61465934779652656776833189)
  ·
    refine ⟨11524862771184873145656223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61465934779652656776833189 11524862771184873145656223)
    ·
      refine ⟨17287294156777309718484335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11524862771184873145656223 17287294156777309718484335)
      ·
        refine ⟨25930941235165964577726503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17287294156777309718484335 25930941235165964577726503)
        ·
          refine ⟨38896411852748946866589755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25930941235165964577726503 38896411852748946866589755)
          ·
            refine ⟨58344617779123420299884633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38896411852748946866589755 58344617779123420299884633)
            ·
              refine ⟨43758463334342565224913475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58344617779123420299884633 43758463334342565224913475)
              ·
                refine ⟨65637695001513847837370213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43758463334342565224913475 65637695001513847837370213)
                ·
                  refine ⟨12307067812783846469506915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65637695001513847837370213 12307067812783846469506915)
                  ·
                    refine ⟨18460601719175769704260373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12307067812783846469506915 18460601719175769704260373)
                    ·
                      refine ⟨865340705586364204887205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18460601719175769704260373 865340705586364204887205)
                      ·
                        rfl

theorem cell23_1685245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_1685245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685245 prefixEnd_1685245 := by exact prefixLift 1685245
  have htrace : WordTrace (prefixWord ++ tailWord_1685245) baseStart_1685245 baseEnd_1685245 := by
    simpa [prefixWord, tailWord_1685245, baseEnd_1685245] using wordTrace_append hprefix tailTrace_1685245
  have hstable : (prefixWord ++ tailWord_1685245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685245).length < 2 ^ (prefixWord ++ tailWord_1685245).sum := by decide
  have hdescent : baseEnd_1685245 < baseStart_1685245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685266 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1685266 : Nat := 118140960795 + 1685266 * 2 ^ 59
def prefixEnd_1685266 : Nat := 4983230072969 + 3 ^ 40 * 1685266 * 2
def baseEnd_1685266 : Nat := 865351488680108622724609

theorem tailTrace_1685266 : CollatzResearch.WordTrace tailWord_1685266 prefixEnd_1685266 865351488680108622724609 := by
  unfold tailWord_1685266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15366675178144144340836913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40977800475051051575565101 15366675178144144340836913)
  ·
    refine ⟨11525006383608108255627685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15366675178144144340836913 11525006383608108255627685)
    ·
      refine ⟨2160938696926520297930191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11525006383608108255627685 2160938696926520297930191)
      ·
        refine ⟨3241408045389780446895287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160938696926520297930191 3241408045389780446895287)
        ·
          refine ⟨4862112068084670670342931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3241408045389780446895287 4862112068084670670342931)
          ·
            refine ⟨7293168102127006005514397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4862112068084670670342931 7293168102127006005514397)
            ·
              refine ⟨2734938038297627252067899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7293168102127006005514397 2734938038297627252067899)
              ·
                refine ⟨4102407057446440878101849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734938038297627252067899 4102407057446440878101849)
                ·
                  refine ⟨3076805293084830658576387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4102407057446440878101849 3076805293084830658576387)
                  ·
                    refine ⟨4615207939627245987864581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3076805293084830658576387 4615207939627245987864581)
                    ·
                      refine ⟨865351488680108622724609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4615207939627245987864581 865351488680108622724609)
                      ·
                        rfl

theorem cell23_1685266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1685266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685266 prefixEnd_1685266 := by exact prefixLift 1685266
  have htrace : WordTrace (prefixWord ++ tailWord_1685266) baseStart_1685266 baseEnd_1685266 := by
    simpa [prefixWord, tailWord_1685266, baseEnd_1685266] using wordTrace_append hprefix tailTrace_1685266
  have hstable : (prefixWord ++ tailWord_1685266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685266).length < 2 ^ (prefixWord ++ tailWord_1685266).sum := by decide
  have hdescent : baseEnd_1685266 < baseStart_1685266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685269 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_1685269 : Nat := 118140960795 + 1685269 * 2 ^ 59
def prefixEnd_1685269 : Nat := 4983230072969 + 3 ^ 40 * 1685269 * 2
def baseEnd_1685269 : Nat := 865353029122072110987095

theorem tailTrace_1685269 : CollatzResearch.WordTrace tailWord_1685269 prefixEnd_1685269 865353029122072110987095 := by
  unfold tailWord_1685269
  simp only [CollatzResearch.WordTrace]
  refine ⟨61466810131565708875706861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40977873421043805917137907 61466810131565708875706861)
  ·
    refine ⟨23050053799337140828390073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61466810131565708875706861 23050053799337140828390073)
    ·
      refine ⟨17287540349502855621292555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23050053799337140828390073 17287540349502855621292555)
      ·
        refine ⟨25931310524254283431938833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17287540349502855621292555 25931310524254283431938833)
        ·
          refine ⟨19448482893190712573954125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25931310524254283431938833 19448482893190712573954125)
          ·
            refine ⟨7293181084946517215232797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19448482893190712573954125 7293181084946517215232797)
            ·
              refine ⟨2734942906854943955712299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7293181084946517215232797 2734942906854943955712299)
              ·
                refine ⟨4102414360282415933568449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734942906854943955712299 4102414360282415933568449)
                ·
                  refine ⟨3076810770211811950176337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4102414360282415933568449 3076810770211811950176337)
                  ·
                    refine ⟨2307608077658858962632253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3076810770211811950176337 2307608077658858962632253)
                    ·
                      refine ⟨865353029122072110987095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2307608077658858962632253 865353029122072110987095)
                      ·
                        rfl

theorem cell23_1685269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_1685269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685269 prefixEnd_1685269 := by exact prefixLift 1685269
  have htrace : WordTrace (prefixWord ++ tailWord_1685269) baseStart_1685269 baseEnd_1685269 := by
    simpa [prefixWord, tailWord_1685269, baseEnd_1685269] using wordTrace_append hprefix tailTrace_1685269
  have hstable : (prefixWord ++ tailWord_1685269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685269).length < 2 ^ (prefixWord ++ tailWord_1685269).sum := by decide
  have hdescent : baseEnd_1685269 < baseStart_1685269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
