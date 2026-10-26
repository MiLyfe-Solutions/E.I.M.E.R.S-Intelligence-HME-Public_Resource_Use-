import V185TrunkScan23Chunk0526

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3115512 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 4, 4]
def baseStart_3115512 : Nat := 118140960795 + 3115512 * 2 ^ 59
def prefixEnd_3115512 : Nat := 4983230072969 + 3 ^ 40 * 3115512 * 2
def baseEnd_3115512 : Nat := 533251713616839926224009

theorem tailTrace_3115512 : CollatzResearch.WordTrace tailWord_3115512 prefixEnd_3115512 533251713616839926224009 := by
  unfold tailWord_3115512
  simp only [CollatzResearch.WordTrace]
  refine ⟨56816028944519792966546395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75754705259359723955395193 56816028944519792966546395)
  ·
    refine ⟨85224043416779689449819593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56816028944519792966546395 85224043416779689449819593)
    ·
      refine ⟨63918032562584767087364695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85224043416779689449819593 63918032562584767087364695)
      ·
        refine ⟨95877048843877150631047043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63918032562584767087364695 95877048843877150631047043)
        ·
          refine ⟨143815573265815725946570565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95877048843877150631047043 143815573265815725946570565)
          ·
            refine ⟨26965419987340448614981981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143815573265815725946570565 26965419987340448614981981)
            ·
              refine ⟨10112032495252668230618243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26965419987340448614981981 10112032495252668230618243)
              ·
                refine ⟨15168048742879002345927365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10112032495252668230618243 15168048742879002345927365)
                ·
                  refine ⟨2844009139289812939861381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15168048742879002345927365 2844009139289812939861381)
                  ·
                    refine ⟨533251713616839926224009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2844009139289812939861381 533251713616839926224009)
                    ·
                      rfl

theorem cell23_3115512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_3115512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115512 prefixEnd_3115512 := by exact prefixLift 3115512
  have htrace : WordTrace (prefixWord ++ tailWord_3115512) baseStart_3115512 baseEnd_3115512 := by
    simpa [prefixWord, tailWord_3115512, baseEnd_3115512] using wordTrace_append hprefix tailTrace_3115512
  have hstable : (prefixWord ++ tailWord_3115512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115512).length < 2 ^ (prefixWord ++ tailWord_3115512).sum := by decide
  have hdescent : baseEnd_3115512 < baseStart_3115512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115532 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3115532 : Nat := 118140960795 + 3115532 * 2 ^ 59
def prefixEnd_3115532 : Nat := 4983230072969 + 3 ^ 40 * 3115532 * 2
def baseEnd_3115532 : Nat := 1599765410463609700421935

theorem tailTrace_3115532 : CollatzResearch.WordTrace tailWord_3115532 prefixEnd_3115532 1599765410463609700421935 := by
  unfold tailWord_3115532
  simp only [CollatzResearch.WordTrace]
  refine ⟨56816393674483564674410425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75755191565978086232547233 56816393674483564674410425)
  ·
    refine ⟨42612295255862673505807819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56816393674483564674410425 42612295255862673505807819)
    ·
      refine ⟨63918442883794010258711729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42612295255862673505807819 63918442883794010258711729)
      ·
        refine ⟨47938832162845507694033797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63918442883794010258711729 47938832162845507694033797)
        ·
          refine ⟨8988531030533532692631337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47938832162845507694033797 8988531030533532692631337)
          ·
            refine ⟨6741398272900149519473503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8988531030533532692631337 6741398272900149519473503)
            ·
              refine ⟨10112097409350224279210255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6741398272900149519473503 10112097409350224279210255)
              ·
                refine ⟨15168146114025336418815383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10112097409350224279210255 15168146114025336418815383)
                ·
                  refine ⟨22752219171038004628223075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15168146114025336418815383 22752219171038004628223075)
                  ·
                    refine ⟨34128328756557006942334613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22752219171038004628223075 34128328756557006942334613)
                    ·
                      refine ⟨1599765410463609700421935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34128328756557006942334613 1599765410463609700421935)
                      ·
                        rfl

theorem cell23_3115532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3115532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115532 prefixEnd_3115532 := by exact prefixLift 3115532
  have htrace : WordTrace (prefixWord ++ tailWord_3115532) baseStart_3115532 baseEnd_3115532 := by
    simpa [prefixWord, tailWord_3115532, baseEnd_3115532] using wordTrace_append hprefix tailTrace_3115532
  have hstable : (prefixWord ++ tailWord_3115532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115532).length < 2 ^ (prefixWord ++ tailWord_3115532).sum := by decide
  have hdescent : baseEnd_3115532 < baseStart_3115532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115533 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3115533 : Nat := 118140960795 + 3115533 * 2 ^ 59
def prefixEnd_3115533 : Nat := 4983230072969 + 3 ^ 40 * 3115533 * 2
def baseEnd_3115533 : Nat := 533255307981421398836477

theorem tailTrace_3115533 : CollatzResearch.WordTrace tailWord_3115533 prefixEnd_3115533 533255307981421398836477 := by
  unfold tailWord_3115533
  simp only [CollatzResearch.WordTrace]
  refine ⟨113632823821963506519607253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75755215881309004346404835 113632823821963506519607253)
  ·
    refine ⟨2663269308327269684053295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 113632823821963506519607253 2663269308327269684053295)
    ·
      refine ⟨3994903962490904526079943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2663269308327269684053295 3994903962490904526079943)
      ·
        refine ⟨5992355943736356789119915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994903962490904526079943 5992355943736356789119915)
        ·
          refine ⟨8988533915604535183679873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5992355943736356789119915 8988533915604535183679873)
          ·
            refine ⟨6741400436703401387759905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8988533915604535183679873 6741400436703401387759905)
            ·
              refine ⟨5056050327527551040819929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6741400436703401387759905 5056050327527551040819929)
              ·
                refine ⟨3792037745645663280614947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056050327527551040819929 3792037745645663280614947)
                ·
                  refine ⟨5688056618468494920922421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792037745645663280614947 5688056618468494920922421)
                  ·
                    refine ⟨533255307981421398836477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5688056618468494920922421 533255307981421398836477)
                    ·
                      rfl

theorem cell23_3115533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3115533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115533 prefixEnd_3115533 := by exact prefixLift 3115533
  have htrace : WordTrace (prefixWord ++ tailWord_3115533) baseStart_3115533 baseEnd_3115533 := by
    simpa [prefixWord, tailWord_3115533, baseEnd_3115533] using wordTrace_append hprefix tailTrace_3115533
  have hstable : (prefixWord ++ tailWord_3115533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115533).length < 2 ^ (prefixWord ++ tailWord_3115533).sum := by decide
  have hdescent : baseEnd_3115533 < baseStart_3115533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115539 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 1, 2, 3]
def baseStart_3115539 : Nat := 118140960795 + 3115539 * 2 ^ 59
def prefixEnd_3115539 : Nat := 4983230072969 + 3 ^ 40 * 3115539 * 2
def baseEnd_3115539 : Nat := 1599769004828191173034403

theorem tailTrace_3115539 : CollatzResearch.WordTrace tailWord_3115539 prefixEnd_3115539 1599769004828191173034403 := by
  unfold tailWord_3115539
  simp only [CollatzResearch.WordTrace]
  refine ⟨113633042659941769544325671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75755361773294513029550447 113633042659941769544325671)
  ·
    refine ⟨170449563989912654316488507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113633042659941769544325671 170449563989912654316488507)
    ·
      refine ⟨255674345984868981474732761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170449563989912654316488507 255674345984868981474732761)
      ·
        refine ⟨191755759488651736106049571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255674345984868981474732761 191755759488651736106049571)
        ·
          refine ⟨287633639232977604159074357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191755759488651736106049571 287633639232977604159074357)
          ·
            refine ⟨26965653678091650389913221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 287633639232977604159074357 26965653678091650389913221)
            ·
              refine ⟨5056060064642184448108729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26965653678091650389913221 5056060064642184448108729)
              ·
                refine ⟨3792045048481638336081547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056060064642184448108729 3792045048481638336081547)
                ·
                  refine ⟨5688067572722457504122321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792045048481638336081547 5688067572722457504122321)
                  ·
                    refine ⟨4266050679541843128091741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5688067572722457504122321 4266050679541843128091741)
                    ·
                      refine ⟨1599769004828191173034403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4266050679541843128091741 1599769004828191173034403)
                      ·
                        rfl

theorem cell23_3115539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 2, 3].length) (baseStart_3115539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115539 prefixEnd_3115539 := by exact prefixLift 3115539
  have htrace : WordTrace (prefixWord ++ tailWord_3115539) baseStart_3115539 baseEnd_3115539 := by
    simpa [prefixWord, tailWord_3115539, baseEnd_3115539] using wordTrace_append hprefix tailTrace_3115539
  have hstable : (prefixWord ++ tailWord_3115539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115539).length < 2 ^ (prefixWord ++ tailWord_3115539).sum := by decide
  have hdescent : baseEnd_3115539 < baseStart_3115539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115556 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3115556 : Nat := 118140960795 + 3115556 * 2 ^ 59
def prefixEnd_3115556 : Nat := 4983230072969 + 3 ^ 40 * 3115556 * 2
def baseEnd_3115556 : Nat := 1599777733999317606521825

theorem tailTrace_3115556 : CollatzResearch.WordTrace tailWord_3115556 prefixEnd_3115556 1599777733999317606521825 := by
  unfold tailWord_3115556
  simp only [CollatzResearch.WordTrace]
  refine ⟨56816831350440090723847261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75755775133920120965129681 56816831350440090723847261)
  ·
    refine ⟨21306311756415034021442723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56816831350440090723847261 21306311756415034021442723)
    ·
      refine ⟨31959467634622551032164085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21306311756415034021442723 31959467634622551032164085)
      ·
        refine ⟨2996200090745864159265383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31959467634622551032164085 2996200090745864159265383)
        ·
          refine ⟨4494300136118796238898075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996200090745864159265383 4494300136118796238898075)
          ·
            refine ⟨6741450204178194358347113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494300136118796238898075 6741450204178194358347113)
            ·
              refine ⟨5056087653133645768760335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6741450204178194358347113 5056087653133645768760335)
              ·
                refine ⟨7584131479700468653140503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5056087653133645768760335 7584131479700468653140503)
                ·
                  refine ⟨11376197219550702979710755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7584131479700468653140503 11376197219550702979710755)
                  ·
                    refine ⟨17064295829326054469566133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11376197219550702979710755 17064295829326054469566133)
                    ·
                      refine ⟨1599777733999317606521825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17064295829326054469566133 1599777733999317606521825)
                      ·
                        rfl

theorem cell23_3115556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3115556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115556 prefixEnd_3115556 := by exact prefixLift 3115556
  have htrace : WordTrace (prefixWord ++ tailWord_3115556) baseStart_3115556 baseEnd_3115556 := by
    simpa [prefixWord, tailWord_3115556, baseEnd_3115556] using wordTrace_append hprefix tailTrace_3115556
  have hstable : (prefixWord ++ tailWord_3115556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115556).length < 2 ^ (prefixWord ++ tailWord_3115556).sum := by decide
  have hdescent : baseEnd_3115556 < baseStart_3115556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115569 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 4, 1, 3]
def baseStart_3115569 : Nat := 118140960795 + 3115569 * 2 ^ 59
def prefixEnd_3115569 : Nat := 4983230072969 + 3 ^ 40 * 3115569 * 2
def baseEnd_3115569 : Nat := 1599784409247826055659265

theorem tailTrace_3115569 : CollatzResearch.WordTrace tailWord_3115569 prefixEnd_3115569 1599784409247826055659265 := by
  unfold tailWord_3115569
  simp only [CollatzResearch.WordTrace]
  refine ⟨113634136849833084667917761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75756091233222056445278507 113634136849833084667917761)
  ·
    refine ⟨85225602637374813500938321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113634136849833084667917761 85225602637374813500938321)
    ·
      refine ⟨63919201978031110125703741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85225602637374813500938321 63919201978031110125703741)
      ·
        refine ⟨23969700741761666297138903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63919201978031110125703741 23969700741761666297138903)
        ·
          refine ⟨35954551112642499445708355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23969700741761666297138903 35954551112642499445708355)
          ·
            refine ⟨53931826668963749168562533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35954551112642499445708355 53931826668963749168562533)
            ·
              refine ⟨10112217500430702969105475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53931826668963749168562533 10112217500430702969105475)
              ·
                refine ⟨15168326250646054453658213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10112217500430702969105475 15168326250646054453658213)
                ·
                  refine ⟨2844061171996135210060915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15168326250646054453658213 2844061171996135210060915)
                  ·
                    refine ⟨4266091757994202815091373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2844061171996135210060915 4266091757994202815091373)
                    ·
                      refine ⟨1599784409247826055659265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4266091757994202815091373 1599784409247826055659265)
                      ·
                        rfl

theorem cell23_3115569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_3115569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115569 prefixEnd_3115569 := by exact prefixLift 3115569
  have htrace : WordTrace (prefixWord ++ tailWord_3115569) baseStart_3115569 baseEnd_3115569 := by
    simpa [prefixWord, tailWord_3115569, baseEnd_3115569] using wordTrace_append hprefix tailTrace_3115569
  have hstable : (prefixWord ++ tailWord_3115569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115569).length < 2 ^ (prefixWord ++ tailWord_3115569).sum := by decide
  have hdescent : baseEnd_3115569 < baseStart_3115569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115590 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3115590 : Nat := 118140960795 + 3115590 * 2 ^ 59
def prefixEnd_3115590 : Nat := 4983230072969 + 3 ^ 40 * 3115590 * 2
def baseEnd_3115590 : Nat := 1599795192341570473496669

theorem tailTrace_3115590 : CollatzResearch.WordTrace tailWord_3115590 prefixEnd_3115590 1599795192341570473496669 := by
  unfold tailWord_3115590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3551090711961156414201007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75756601855171336836288149 3551090711961156414201007)
  ·
    refine ⟨5326636067941734621301511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3551090711961156414201007 5326636067941734621301511)
    ·
      refine ⟨7989954101912601931952267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5326636067941734621301511 7989954101912601931952267)
      ·
        refine ⟨11984931152868902897928401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7989954101912601931952267 11984931152868902897928401)
        ·
          refine ⟨8988698364651677173446301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11984931152868902897928401 8988698364651677173446301)
          ·
            refine ⟨3370761886744378940042363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8988698364651677173446301 3370761886744378940042363)
            ·
              refine ⟨5056142830116568410063545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370761886744378940042363 5056142830116568410063545)
              ·
                refine ⟨3792107122587426307547659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056142830116568410063545 3792107122587426307547659)
                ·
                  refine ⟨5688160683881139461321489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792107122587426307547659 5688160683881139461321489)
                  ·
                    refine ⟨4266120512910854595991117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5688160683881139461321489 4266120512910854595991117)
                    ·
                      refine ⟨1599795192341570473496669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4266120512910854595991117 1599795192341570473496669)
                      ·
                        rfl

theorem cell23_3115590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3115590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115590 prefixEnd_3115590 := by exact prefixLift 3115590
  have htrace : WordTrace (prefixWord ++ tailWord_3115590) baseStart_3115590 baseEnd_3115590 := by
    simpa [prefixWord, tailWord_3115590, baseEnd_3115590] using wordTrace_append hprefix tailTrace_3115590
  have hstable : (prefixWord ++ tailWord_3115590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115590).length < 2 ^ (prefixWord ++ tailWord_3115590).sum := by decide
  have hdescent : baseEnd_3115590 < baseStart_3115590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115629 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3115629 : Nat := 118140960795 + 3115629 * 2 ^ 59
def prefixEnd_3115629 : Nat := 4983230072969 + 3 ^ 40 * 3115629 * 2
def baseEnd_3115629 : Nat := 1599815218087095820908989

theorem tailTrace_3115629 : CollatzResearch.WordTrace tailWord_3115629 prefixEnd_3115629 1599815218087095820908989 := by
  unfold tailWord_3115629
  simp only [CollatzResearch.WordTrace]
  refine ⟨113636325229615714915101941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75757550153077143276734627 113636325229615714915101941)
  ·
    refine ⟨10653405490276473273290807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113636325229615714915101941 10653405490276473273290807)
    ·
      refine ⟨15980108235414709909936211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10653405490276473273290807 15980108235414709909936211)
      ·
        refine ⟨23970162353122064864904317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15980108235414709909936211 23970162353122064864904317)
        ·
          refine ⟨8988810882420774324339119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23970162353122064864904317 8988810882420774324339119)
          ·
            refine ⟨13483216323631161486508679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8988810882420774324339119 13483216323631161486508679)
            ·
              refine ⟨20224824485446742229763019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13483216323631161486508679 20224824485446742229763019)
              ·
                refine ⟨30337236728170113344644529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20224824485446742229763019 30337236728170113344644529)
                ·
                  refine ⟨22752927546127585008483397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30337236728170113344644529 22752927546127585008483397)
                  ·
                    refine ⟨4266173914898922189090637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22752927546127585008483397 4266173914898922189090637)
                    ·
                      refine ⟨1599815218087095820908989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4266173914898922189090637 1599815218087095820908989)
                      ·
                        rfl

theorem cell23_3115629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3115629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115629 prefixEnd_3115629 := by exact prefixLift 3115629
  have htrace : WordTrace (prefixWord ++ tailWord_3115629) baseStart_3115629 baseEnd_3115629 := by
    simpa [prefixWord, tailWord_3115629, baseEnd_3115629] using wordTrace_append hprefix tailTrace_3115629
  have hstable : (prefixWord ++ tailWord_3115629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115629).length < 2 ^ (prefixWord ++ tailWord_3115629).sum := by decide
  have hdescent : baseEnd_3115629 < baseStart_3115629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115666 : List Nat := [3, 2, 3, 1, 2, 1, 1, 5, 5]
def baseStart_3115666 : Nat := 118140960795 + 3115666 * 2 ^ 59
def prefixEnd_3115666 : Nat := 4983230072969 + 3 ^ 40 * 3115666 * 2
def baseEnd_3115666 : Nat := 177759357430145797349591

theorem tailTrace_3115666 : CollatzResearch.WordTrace tailWord_3115666 prefixEnd_3115666 177759357430145797349591 := by
  unfold tailWord_3115666
  simp only [CollatzResearch.WordTrace]
  refine ⟨28409418682620417558549713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75758449820321113489465901 28409418682620417558549713)
  ·
    refine ⟨21307064011965313168912285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28409418682620417558549713 21307064011965313168912285)
    ·
      refine ⟨7990149004486992438342107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21307064011965313168912285 7990149004486992438342107)
      ·
        refine ⟨11985223506730488657513161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7990149004486992438342107 11985223506730488657513161)
        ·
          refine ⟨8988917630047866493134871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11985223506730488657513161 8988917630047866493134871)
          ·
            refine ⟨13483376445071799739702307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8988917630047866493134871 13483376445071799739702307)
            ·
              refine ⟨20225064667607699609553461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13483376445071799739702307 20225064667607699609553461)
              ·
                refine ⟨1896099812588221838395637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20225064667607699609553461 1896099812588221838395637)
                ·
                  refine ⟨177759357430145797349591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1896099812588221838395637 177759357430145797349591)
                  ·
                    rfl

theorem cell23_3115666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_3115666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115666 prefixEnd_3115666 := by exact prefixLift 3115666
  have htrace : WordTrace (prefixWord ++ tailWord_3115666) baseStart_3115666 baseEnd_3115666 := by
    simpa [prefixWord, tailWord_3115666, baseEnd_3115666] using wordTrace_append hprefix tailTrace_3115666
  have hstable : (prefixWord ++ tailWord_3115666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115666).length < 2 ^ (prefixWord ++ tailWord_3115666).sum := by decide
  have hdescent : baseEnd_3115666 < baseStart_3115666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115733 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3115733 : Nat := 118140960795 + 3115733 * 2 ^ 59
def prefixEnd_3115733 : Nat := 4983230072969 + 3 ^ 40 * 3115733 * 2
def baseEnd_3115733 : Nat := 1599868620075163414008511

theorem tailTrace_3115733 : CollatzResearch.WordTrace tailWord_3115733 prefixEnd_3115733 1599868620075163414008511 := by
  unfold tailWord_3115733
  simp only [CollatzResearch.WordTrace]
  refine ⟨113640118421238940676887853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75760078947492627117925235 113640118421238940676887853)
  ·
    refine ⟨42615044407964602753832945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113640118421238940676887853 42615044407964602753832945)
    ·
      refine ⟨31961283305973452065374709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42615044407964602753832945 31961283305973452065374709)
      ·
        refine ⟨2996370309935011131128879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31961283305973452065374709 2996370309935011131128879)
        ·
          refine ⟨4494555464902516696693319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996370309935011131128879 4494555464902516696693319)
          ·
            refine ⟨6741833197353775045039979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494555464902516696693319 6741833197353775045039979)
            ·
              refine ⟨10112749796030662567559969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6741833197353775045039979 10112749796030662567559969)
              ·
                refine ⟨7584562347022996925669977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10112749796030662567559969 7584562347022996925669977)
                ·
                  refine ⟨5688421760267247694252483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7584562347022996925669977 5688421760267247694252483)
                  ·
                    refine ⟨8532632640400871541378725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5688421760267247694252483 8532632640400871541378725)
                    ·
                      refine ⟨1599868620075163414008511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8532632640400871541378725 1599868620075163414008511)
                      ·
                        rfl

theorem cell23_3115733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3115733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115733 prefixEnd_3115733 := by exact prefixLift 3115733
  have htrace : WordTrace (prefixWord ++ tailWord_3115733) baseStart_3115733 baseEnd_3115733 := by
    simpa [prefixWord, tailWord_3115733, baseEnd_3115733] using wordTrace_append hprefix tailTrace_3115733
  have hstable : (prefixWord ++ tailWord_3115733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115733).length < 2 ^ (prefixWord ++ tailWord_3115733).sum := by decide
  have hdescent : baseEnd_3115733 < baseStart_3115733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115736 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 2, 2, 3]
def baseStart_3115736 : Nat := 118140960795 + 3115736 * 2 ^ 59
def prefixEnd_3115736 : Nat := 4983230072969 + 3 ^ 40 * 3115736 * 2
def baseEnd_3115736 : Nat := 1599870160517126902270997

theorem tailTrace_3115736 : CollatzResearch.WordTrace tailWord_3115736 prefixEnd_3115736 1599870160517126902270997 := by
  unfold tailWord_3115736
  simp only [CollatzResearch.WordTrace]
  refine ⟨56820113920114036094623531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75760151893485381459498041 56820113920114036094623531)
  ·
    refine ⟨85230170880171054141935297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56820113920114036094623531 85230170880171054141935297)
    ·
      refine ⟨63922628160128290606451473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85230170880171054141935297 63922628160128290606451473)
      ·
        refine ⟨47941971120096217954838605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63922628160128290606451473 47941971120096217954838605)
        ·
          refine ⟨17978239170036081733064477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47941971120096217954838605 17978239170036081733064477)
          ·
            refine ⟨6741839688763530649899179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17978239170036081733064477 6741839688763530649899179)
            ·
              refine ⟨10112759533145295974848769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6741839688763530649899179 10112759533145295974848769)
              ·
                refine ⟨7584569649858971981136577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10112759533145295974848769 7584569649858971981136577)
                ·
                  refine ⟨5688427237394228985852433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7584569649858971981136577 5688427237394228985852433)
                  ·
                    refine ⟨4266320428045671739389325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5688427237394228985852433 4266320428045671739389325)
                    ·
                      refine ⟨1599870160517126902270997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4266320428045671739389325 1599870160517126902270997)
                      ·
                        rfl

theorem cell23_3115736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_3115736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115736 prefixEnd_3115736 := by exact prefixLift 3115736
  have htrace : WordTrace (prefixWord ++ tailWord_3115736) baseStart_3115736 baseEnd_3115736 := by
    simpa [prefixWord, tailWord_3115736, baseEnd_3115736] using wordTrace_append hprefix tailTrace_3115736
  have hstable : (prefixWord ++ tailWord_3115736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115736).length < 2 ^ (prefixWord ++ tailWord_3115736).sum := by decide
  have hdescent : baseEnd_3115736 < baseStart_3115736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115794 : List Nat := [3, 2, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3115794 : Nat := 118140960795 + 3115794 * 2 ^ 59
def prefixEnd_3115794 : Nat := 4983230072969 + 3 ^ 40 * 3115794 * 2
def baseEnd_3115794 : Nat := 533299980798362558448577

theorem tailTrace_3115794 : CollatzResearch.WordTrace tailWord_3115794 prefixEnd_3115794 533299980798362558448577 := by
  unfold tailWord_3115794
  simp only [CollatzResearch.WordTrace]
  refine ⟨28410585818504487023714609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75761562182678632063238957 28410585818504487023714609)
  ·
    refine ⟨21307939363878365267785957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28410585818504487023714609 21307939363878365267785957)
    ·
      refine ⟨3995238630727193487709867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21307939363878365267785957 3995238630727193487709867)
      ·
        refine ⟨5992857946090790231564801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3995238630727193487709867 5992857946090790231564801)
        ·
          refine ⟨4494643459568092673673601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5992857946090790231564801 4494643459568092673673601)
          ·
            refine ⟨3370982594676069505255201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4494643459568092673673601 3370982594676069505255201)
            ·
              refine ⟨2528236946007052128941401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3370982594676069505255201 2528236946007052128941401)
              ·
                refine ⟨1896177709505289096706051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528236946007052128941401 1896177709505289096706051)
                ·
                  refine ⟨2844266564257933645059077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896177709505289096706051 2844266564257933645059077)
                  ·
                    refine ⟨533299980798362558448577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2844266564257933645059077 533299980798362558448577)
                    ·
                      rfl

theorem cell23_3115794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3115794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115794 prefixEnd_3115794 := by exact prefixLift 3115794
  have htrace : WordTrace (prefixWord ++ tailWord_3115794) baseStart_3115794 baseEnd_3115794 := by
    simpa [prefixWord, tailWord_3115794, baseEnd_3115794] using wordTrace_append hprefix tailTrace_3115794
  have hstable : (prefixWord ++ tailWord_3115794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115794).length < 2 ^ (prefixWord ++ tailWord_3115794).sum := by decide
  have hdescent : baseEnd_3115794 < baseStart_3115794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115809 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3115809 : Nat := 118140960795 + 3115809 * 2 ^ 59
def prefixEnd_3115809 : Nat := 4983230072969 + 3 ^ 40 * 3115809 * 2
def baseEnd_3115809 : Nat := 1599907644604905116658161

theorem tailTrace_3115809 : CollatzResearch.WordTrace tailWord_3115809 prefixEnd_3115809 1599907644604905116658161 := by
  unfold tailWord_3115809
  simp only [CollatzResearch.WordTrace]
  refine ⟨113642890368963605656654481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75761926912642403771102987 113642890368963605656654481)
  ·
    refine ⟨85232167776722704242490861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113642890368963605656654481 85232167776722704242490861)
    ·
      refine ⟨31962062916271014090934073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85232167776722704242490861 31962062916271014090934073)
      ·
        refine ⟨23971547187203260568200555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31962062916271014090934073 23971547187203260568200555)
        ·
          refine ⟨35957320780804890852300833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23971547187203260568200555 35957320780804890852300833)
          ·
            refine ⟨26967990585603668139225625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35957320780804890852300833 26967990585603668139225625)
            ·
              refine ⟨20225992939202751104419219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26967990585603668139225625 20225992939202751104419219)
              ·
                refine ⟨30338989408804126656628829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20225992939202751104419219 30338989408804126656628829)
                ·
                  refine ⟨11377121028301547496235811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30338989408804126656628829 11377121028301547496235811)
                  ·
                    refine ⟨17065681542452321244353717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11377121028301547496235811 17065681542452321244353717)
                    ·
                      refine ⟨1599907644604905116658161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17065681542452321244353717 1599907644604905116658161)
                      ·
                        rfl

theorem cell23_3115809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3115809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115809 prefixEnd_3115809 := by exact prefixLift 3115809
  have htrace : WordTrace (prefixWord ++ tailWord_3115809) baseStart_3115809 baseEnd_3115809 := by
    simpa [prefixWord, tailWord_3115809, baseEnd_3115809] using wordTrace_append hprefix tailTrace_3115809
  have hstable : (prefixWord ++ tailWord_3115809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115809).length < 2 ^ (prefixWord ++ tailWord_3115809).sum := by decide
  have hdescent : baseEnd_3115809 < baseStart_3115809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115816 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3115816 : Nat := 118140960795 + 3115816 * 2 ^ 59
def prefixEnd_3115816 : Nat := 4983230072969 + 3 ^ 40 * 3115816 * 2
def baseEnd_3115816 : Nat := 533303746323162196423543

theorem tailTrace_3115816 : CollatzResearch.WordTrace tailWord_3115816 prefixEnd_3115816 533303746323162196423543 := by
  unfold tailWord_3115816
  simp only [CollatzResearch.WordTrace]
  refine ⟨56821572839969122926079651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75762097119958830568106201 56821572839969122926079651)
  ·
    refine ⟨85232359259953684389119477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56821572839969122926079651 85232359259953684389119477)
    ·
      refine ⟨7990533680620657911479951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85232359259953684389119477 7990533680620657911479951)
      ·
        refine ⟨11985800520930986867219927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7990533680620657911479951 11985800520930986867219927)
        ·
          refine ⟨17978700781396480300829891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11985800520930986867219927 17978700781396480300829891)
          ·
            refine ⟨26968051172094720451244837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17978700781396480300829891 26968051172094720451244837)
            ·
              refine ⟨5056509594767760084608407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26968051172094720451244837 5056509594767760084608407)
              ·
                refine ⟨7584764392151640126912611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5056509594767760084608407 7584764392151640126912611)
                ·
                  refine ⟨11377146588227460190368917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7584764392151640126912611 11377146588227460190368917)
                  ·
                    refine ⟨533303746323162196423543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11377146588227460190368917 533303746323162196423543)
                    ·
                      rfl

theorem cell23_3115816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3115816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115816 prefixEnd_3115816 := by exact prefixLift 3115816
  have htrace : WordTrace (prefixWord ++ tailWord_3115816) baseStart_3115816 baseEnd_3115816 := by
    simpa [prefixWord, tailWord_3115816, baseEnd_3115816] using wordTrace_append hprefix tailTrace_3115816
  have hstable : (prefixWord ++ tailWord_3115816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115816).length < 2 ^ (prefixWord ++ tailWord_3115816).sum := by decide
  have hdescent : baseEnd_3115816 < baseStart_3115816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115819 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 4]
def baseStart_3115819 : Nat := 118140960795 + 3115819 * 2 ^ 59
def prefixEnd_3115819 : Nat := 4983230072969 + 3 ^ 40 * 3115819 * 2
def baseEnd_3115819 : Nat := 1599912779411450077533115

theorem tailTrace_3115819 : CollatzResearch.WordTrace tailWord_3115819 prefixEnd_3115819 1599912779411450077533115 := by
  unfold tailWord_3115819
  simp only [CollatzResearch.WordTrace]
  refine ⟨113643255098927377364518511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75762170065951584909679007 113643255098927377364518511)
  ·
    refine ⟨170464882648391066046777767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113643255098927377364518511 170464882648391066046777767)
    ·
      refine ⟨255697323972586599070166651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170464882648391066046777767 255697323972586599070166651)
      ·
        refine ⟨383545985958879898605249977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255697323972586599070166651 383545985958879898605249977)
        ·
          refine ⟨287659489469159923953937483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383545985958879898605249977 287659489469159923953937483)
          ·
            refine ⟨431489234203739885930906225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287659489469159923953937483 431489234203739885930906225)
            ·
              refine ⟨323616925652804914448179669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431489234203739885930906225 323616925652804914448179669)
              ·
                refine ⟨7584771694987615182379211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 323616925652804914448179669 7584771694987615182379211)
                ·
                  refine ⟨11377157542481422773568817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7584771694987615182379211 11377157542481422773568817)
                  ·
                    refine ⟨8532868156861067080176613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11377157542481422773568817 8532868156861067080176613)
                    ·
                      refine ⟨1599912779411450077533115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8532868156861067080176613 1599912779411450077533115)
                      ·
                        rfl

theorem cell23_3115819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 4].length) (baseStart_3115819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115819 prefixEnd_3115819 := by exact prefixLift 3115819
  have htrace : WordTrace (prefixWord ++ tailWord_3115819) baseStart_3115819 baseEnd_3115819 := by
    simpa [prefixWord, tailWord_3115819, baseEnd_3115819] using wordTrace_append hprefix tailTrace_3115819
  have hstable : (prefixWord ++ tailWord_3115819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115819).length < 2 ^ (prefixWord ++ tailWord_3115819).sum := by decide
  have hdescent : baseEnd_3115819 < baseStart_3115819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115826 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_3115826 : Nat := 118140960795 + 3115826 * 2 ^ 59
def prefixEnd_3115826 : Nat := 4983230072969 + 3 ^ 40 * 3115826 * 2
def baseEnd_3115826 : Nat := 1599916373776031550145583

theorem tailTrace_3115826 : CollatzResearch.WordTrace tailWord_3115826 prefixEnd_3115826 1599916373776031550145583 := by
  unfold tailWord_3115826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28410877602475504390005833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75762340273268011706682221 28410877602475504390005833)
  ·
    refine ⟨21308158201856628292504375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28410877602475504390005833 21308158201856628292504375)
    ·
      refine ⟨31962237302784942438756563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21308158201856628292504375 31962237302784942438756563)
      ·
        refine ⟨47943355954177413658134845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31962237302784942438756563 47943355954177413658134845)
        ·
          refine ⟨17978758482816530121800567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47943355954177413658134845 17978758482816530121800567)
          ·
            refine ⟨26968137724224795182700851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17978758482816530121800567 26968137724224795182700851)
            ·
              refine ⟨40452206586337192774051277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26968137724224795182700851 40452206586337192774051277)
              ·
                refine ⟨15169577469876447290269229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40452206586337192774051277 15169577469876447290269229)
                ·
                  refine ⟨5688591551203667733850961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15169577469876447290269229 5688591551203667733850961)
                  ·
                    refine ⟨4266443663402750800388221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5688591551203667733850961 4266443663402750800388221)
                    ·
                      refine ⟨1599916373776031550145583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4266443663402750800388221 1599916373776031550145583)
                      ·
                        rfl

theorem cell23_3115826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_3115826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115826 prefixEnd_3115826 := by exact prefixLift 3115826
  have htrace : WordTrace (prefixWord ++ tailWord_3115826) baseStart_3115826 baseEnd_3115826 := by
    simpa [prefixWord, tailWord_3115826, baseEnd_3115826] using wordTrace_append hprefix tailTrace_3115826
  have hstable : (prefixWord ++ tailWord_3115826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115826).length < 2 ^ (prefixWord ++ tailWord_3115826).sum := by decide
  have hdescent : baseEnd_3115826 < baseStart_3115826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115837 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_3115837 : Nat := 118140960795 + 3115837 * 2 ^ 59
def prefixEnd_3115837 : Nat := 4983230072969 + 3 ^ 40 * 3115837 * 2
def baseEnd_3115837 : Nat := 533307340687743669036011

theorem tailTrace_3115837 : CollatzResearch.WordTrace tailWord_3115837 prefixEnd_3115837 533307340687743669036011 := by
  unfold tailWord_3115837
  simp only [CollatzResearch.WordTrace]
  refine ⟨113643911612862166438673765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75762607741908110959115843 113643911612862166438673765)
  ·
    refine ⟨21308233427411656207251331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113643911612862166438673765 21308233427411656207251331)
    ·
      refine ⟨31962350141117484310876997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21308233427411656207251331 31962350141117484310876997)
      ·
        refine ⟨5992940651459528308289437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31962350141117484310876997 5992940651459528308289437)
        ·
          refine ⟨2247352744297323115608539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5992940651459528308289437 2247352744297323115608539)
          ·
            refine ⟨3371029116445984673412809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247352744297323115608539 3371029116445984673412809)
            ·
              refine ⟨2528271837334488505059607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3371029116445984673412809 2528271837334488505059607)
              ·
                refine ⟨3792407756001732757589411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528271837334488505059607 3792407756001732757589411)
                ·
                  refine ⟨5688611634002599136384117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792407756001732757589411 5688611634002599136384117)
                  ·
                    refine ⟨533307340687743669036011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5688611634002599136384117 533307340687743669036011)
                    ·
                      rfl

theorem cell23_3115837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_3115837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115837 prefixEnd_3115837 := by exact prefixLift 3115837
  have htrace : WordTrace (prefixWord ++ tailWord_3115837) baseStart_3115837 baseEnd_3115837 := by
    simpa [prefixWord, tailWord_3115837, baseEnd_3115837] using wordTrace_append hprefix tailTrace_3115837
  have hstable : (prefixWord ++ tailWord_3115837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115837).length < 2 ^ (prefixWord ++ tailWord_3115837).sum := by decide
  have hdescent : baseEnd_3115837 < baseStart_3115837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115883 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 1, 3, 2]
def baseStart_3115883 : Nat := 118140960795 + 3115883 * 2 ^ 59
def prefixEnd_3115883 : Nat := 4983230072969 + 3 ^ 40 * 3115883 * 2
def baseEnd_3115883 : Nat := 1599945642173337827132821

theorem tailTrace_3115883 : CollatzResearch.WordTrace tailWord_3115883 prefixEnd_3115883 1599945642173337827132821 := by
  unfold tailWord_3115883
  simp only [CollatzResearch.WordTrace]
  refine ⟨113645589370695516294848303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75763726247130344196565535 113645589370695516294848303)
  ·
    refine ⟨170468384056043274442272455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113645589370695516294848303 170468384056043274442272455)
    ·
      refine ⟨255702576084064911663408683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170468384056043274442272455 255702576084064911663408683)
      ·
        refine ⟨383553864126097367495113025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255702576084064911663408683 383553864126097367495113025)
        ·
          refine ⟨287665398094573025621334769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383553864126097367495113025 287665398094573025621334769)
          ·
            refine ⟨215749048570929769216001077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287665398094573025621334769 215749048570929769216001077)
            ·
              refine ⟨20226473303524665864000101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215749048570929769216001077 20226473303524665864000101)
              ·
                refine ⟨3792463744410874849500019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20226473303524665864000101 3792463744410874849500019)
                ·
                  refine ⟨5688695616616312274250029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792463744410874849500019 5688695616616312274250029)
                  ·
                    refine ⟨2133260856231117102843761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5688695616616312274250029 2133260856231117102843761)
                    ·
                      refine ⟨1599945642173337827132821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133260856231117102843761 1599945642173337827132821)
                      ·
                        rfl

theorem cell23_3115883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 3, 2].length) (baseStart_3115883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115883 prefixEnd_3115883 := by exact prefixLift 3115883
  have htrace : WordTrace (prefixWord ++ tailWord_3115883) baseStart_3115883 baseEnd_3115883 := by
    simpa [prefixWord, tailWord_3115883, baseEnd_3115883] using wordTrace_append hprefix tailTrace_3115883
  have hstable : (prefixWord ++ tailWord_3115883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115883).length < 2 ^ (prefixWord ++ tailWord_3115883).sum := by decide
  have hdescent : baseEnd_3115883 < baseStart_3115883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115899 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 5]
def baseStart_3115899 : Nat := 118140960795 + 3115899 * 2 ^ 59
def prefixEnd_3115899 : Nat := 4983230072969 + 3 ^ 40 * 3115899 * 2
def baseEnd_3115899 : Nat := 1599953857863809764532747

theorem tailTrace_3115899 : CollatzResearch.WordTrace tailWord_3115899 prefixEnd_3115899 1599953857863809764532747 := by
  unfold tailWord_3115899
  simp only [CollatzResearch.WordTrace]
  refine ⟨113646172938637551027430751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75764115292425034018287167 113646172938637551027430751)
  ·
    refine ⟨170469259407956326541146127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113646172938637551027430751 170469259407956326541146127)
    ·
      refine ⟨255703889111934489811719191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170469259407956326541146127 255703889111934489811719191)
      ·
        refine ⟨383555833667901734717578787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255703889111934489811719191 383555833667901734717578787)
        ·
          refine ⟨575333750501852602076368181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383555833667901734717578787 575333750501852602076368181)
          ·
            refine ⟨53937539109548681444659517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 575333750501852602076368181 53937539109548681444659517)
            ·
              refine ⟨20226577166080755541747319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53937539109548681444659517 20226577166080755541747319)
              ·
                refine ⟨30339865749121133312620979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20226577166080755541747319 30339865749121133312620979)
                ·
                  refine ⟨45509798623681699968931469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30339865749121133312620979 45509798623681699968931469)
                  ·
                    refine ⟨17066174483880637488349301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45509798623681699968931469 17066174483880637488349301)
                    ·
                      refine ⟨1599953857863809764532747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17066174483880637488349301 1599953857863809764532747)
                      ·
                        rfl

theorem cell23_3115899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_3115899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115899 prefixEnd_3115899 := by exact prefixLift 3115899
  have htrace : WordTrace (prefixWord ++ tailWord_3115899) baseStart_3115899 baseEnd_3115899 := by
    simpa [prefixWord, tailWord_3115899, baseEnd_3115899] using wordTrace_append hprefix tailTrace_3115899
  have hstable : (prefixWord ++ tailWord_3115899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115899).length < 2 ^ (prefixWord ++ tailWord_3115899).sum := by decide
  have hdescent : baseEnd_3115899 < baseStart_3115899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115974 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3115974 : Nat := 118140960795 + 3115974 * 2 ^ 59
def prefixEnd_3115974 : Nat := 4983230072969 + 3 ^ 40 * 3115974 * 2
def baseEnd_3115974 : Nat := 533330789637632323698301

theorem tailTrace_3115974 : CollatzResearch.WordTrace tailWord_3115974 prefixEnd_3115974 533330789637632323698301 := by
  unfold tailWord_3115974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3551528387917682463637843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75765938942243892557607317 3551528387917682463637843)
  ·
    refine ⟨5327292581876523695456765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3551528387917682463637843 5327292581876523695456765)
    ·
      refine ⟨1997734718203696385796287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5327292581876523695456765 1997734718203696385796287)
      ·
        refine ⟨2996602077305544578694431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997734718203696385796287 2996602077305544578694431)
        ·
          refine ⟨4494903115958316868041647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996602077305544578694431 4494903115958316868041647)
          ·
            refine ⟨6742354673937475302062471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494903115958316868041647 6742354673937475302062471)
            ·
              refine ⟨10113532010906212953093707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742354673937475302062471 10113532010906212953093707)
              ·
                refine ⟨15170298016359319429640561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10113532010906212953093707 15170298016359319429640561)
                ·
                  refine ⟨11377723512269489572230421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15170298016359319429640561 11377723512269489572230421)
                  ·
                    refine ⟨533330789637632323698301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11377723512269489572230421 533330789637632323698301)
                    ·
                      rfl

theorem cell23_3115974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3115974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115974 prefixEnd_3115974 := by exact prefixLift 3115974
  have htrace : WordTrace (prefixWord ++ tailWord_3115974) baseStart_3115974 baseEnd_3115974 := by
    simpa [prefixWord, tailWord_3115974, baseEnd_3115974] using wordTrace_append hprefix tailTrace_3115974
  have hstable : (prefixWord ++ tailWord_3115974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115974).length < 2 ^ (prefixWord ++ tailWord_3115974).sum := by decide
  have hdescent : baseEnd_3115974 < baseStart_3115974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115981 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3115981 : Nat := 118140960795 + 3115981 * 2 ^ 59
def prefixEnd_3115981 : Nat := 4983230072969 + 3 ^ 40 * 3115981 * 2
def baseEnd_3115981 : Nat := 1599995963277478443707371

theorem tailTrace_3115981 : CollatzResearch.WordTrace tailWord_3115981 prefixEnd_3115981 1599995963277478443707371 := by
  unfold tailWord_3115981
  simp only [CollatzResearch.WordTrace]
  refine ⟨113649163724340479031915797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75766109149560319354610531 113649163724340479031915797)
  ·
    refine ⟨5327304549578459954621053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113649163724340479031915797 5327304549578459954621053)
    ·
      refine ⟨1997739206091922482982895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5327304549578459954621053 1997739206091922482982895)
      ·
        refine ⟨2996608809137883724474343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997739206091922482982895 2996608809137883724474343)
        ·
          refine ⟨4494913213706825586711515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996608809137883724474343 4494913213706825586711515)
          ·
            refine ⟨6742369820560238380067273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494913213706825586711515 6742369820560238380067273)
            ·
              refine ⟨5056777365420178785050455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6742369820560238380067273 5056777365420178785050455)
              ·
                refine ⟨7585166048130268177575683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5056777365420178785050455 7585166048130268177575683)
                ·
                  refine ⟨11377749072195402266363525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7585166048130268177575683 11377749072195402266363525)
                  ·
                    refine ⟨2133327951036637924943161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11377749072195402266363525 2133327951036637924943161)
                    ·
                      refine ⟨1599995963277478443707371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133327951036637924943161 1599995963277478443707371)
                      ·
                        rfl

theorem cell23_3115981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3115981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3115981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3115981 prefixEnd_3115981 := by exact prefixLift 3115981
  have htrace : WordTrace (prefixWord ++ tailWord_3115981) baseStart_3115981 baseEnd_3115981 := by
    simpa [prefixWord, tailWord_3115981, baseEnd_3115981] using wordTrace_append hprefix tailTrace_3115981
  have hstable : (prefixWord ++ tailWord_3115981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115981).length < 2 ^ (prefixWord ++ tailWord_3115981).sum := by decide
  have hdescent : baseEnd_3115981 < baseStart_3115981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116003 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 1, 6, 2]
def baseStart_3116003 : Nat := 118140960795 + 3116003 * 2 ^ 59
def prefixEnd_3116003 : Nat := 4983230072969 + 3 ^ 40 * 3116003 * 2
def baseEnd_3116003 : Nat := 1600007259851877357632269

theorem tailTrace_3116003 : CollatzResearch.WordTrace tailWord_3116003 prefixEnd_3116003 1600007259851877357632269 := by
  unfold tailWord_3116003
  simp only [CollatzResearch.WordTrace]
  refine ⟨113649966130260776789216663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75766644086840517859477775 113649966130260776789216663)
  ·
    refine ⟨170474949195391165183824995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113649966130260776789216663 170474949195391165183824995)
    ·
      refine ⟨255712423793086747775737493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170474949195391165183824995 255712423793086747775737493)
      ·
        refine ⟨11986519865300941301987695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255712423793086747775737493 11986519865300941301987695)
        ·
          refine ⟨17979779797951411952981543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11986519865300941301987695 17979779797951411952981543)
          ·
            refine ⟨26969669696927117929472315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17979779797951411952981543 26969669696927117929472315)
            ·
              refine ⟨40454504545390676894208473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26969669696927117929472315 40454504545390676894208473)
              ·
                refine ⟨30340878409043007670656355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40454504545390676894208473 30340878409043007670656355)
                ·
                  refine ⟨45511317613564511505984533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30340878409043007670656355 45511317613564511505984533)
                  ·
                    refine ⟨2133343013135836476843025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45511317613564511505984533 2133343013135836476843025)
                    ·
                      refine ⟨1600007259851877357632269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133343013135836476843025 1600007259851877357632269)
                      ·
                        rfl

theorem cell23_3116003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_3116003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116003 prefixEnd_3116003 := by exact prefixLift 3116003
  have htrace : WordTrace (prefixWord ++ tailWord_3116003) baseStart_3116003 baseEnd_3116003 := by
    simpa [prefixWord, tailWord_3116003, baseEnd_3116003] using wordTrace_append hprefix tailTrace_3116003
  have hstable : (prefixWord ++ tailWord_3116003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116003).length < 2 ^ (prefixWord ++ tailWord_3116003).sum := by decide
  have hdescent : baseEnd_3116003 < baseStart_3116003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116080 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 2, 3, 2]
def baseStart_3116080 : Nat := 118140960795 + 3116080 * 2 ^ 59
def prefixEnd_3116080 : Nat := 4983230072969 + 3 ^ 40 * 3116080 * 2
def baseEnd_3116080 : Nat := 1600046797862273556369415

theorem tailTrace_3116080 : CollatzResearch.WordTrace tailWord_3116080 prefixEnd_3116080 1600046797862273556369415 := by
  unfold tailWord_3116080
  simp only [CollatzResearch.WordTrace]
  refine ⟨56826387275490909469884847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75768516367321212626513129 56826387275490909469884847)
  ·
    refine ⟨85239580913236364204827271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56826387275490909469884847 85239580913236364204827271)
    ·
      refine ⟨127859371369854546307240907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85239580913236364204827271 127859371369854546307240907)
      ·
        refine ⟨191789057054781819460861361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127859371369854546307240907 191789057054781819460861361)
        ·
          refine ⟨143841792791086364595646021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191789057054781819460861361 143841792791086364595646021)
          ·
            refine ⟨26970336148328693361683629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143841792791086364595646021 26970336148328693361683629)
            ·
              refine ⟨10113876055623260010631361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26970336148328693361683629 10113876055623260010631361)
              ·
                refine ⟨7585407041717445007973521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10113876055623260010631361 7585407041717445007973521)
                ·
                  refine ⟨5689055281288083755980141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7585407041717445007973521 5689055281288083755980141)
                  ·
                    refine ⟨2133395730483031408492553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5689055281288083755980141 2133395730483031408492553)
                    ·
                      refine ⟨1600046797862273556369415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133395730483031408492553 1600046797862273556369415)
                      ·
                        rfl

theorem cell23_3116080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 3, 2].length) (baseStart_3116080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116080 prefixEnd_3116080 := by exact prefixLift 3116080
  have htrace : WordTrace (prefixWord ++ tailWord_3116080) baseStart_3116080 baseEnd_3116080 := by
    simpa [prefixWord, tailWord_3116080, baseEnd_3116080] using wordTrace_append hprefix tailTrace_3116080
  have hstable : (prefixWord ++ tailWord_3116080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116080).length < 2 ^ (prefixWord ++ tailWord_3116080).sum := by decide
  have hdescent : baseEnd_3116080 < baseStart_3116080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116143 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 3]
def baseStart_3116143 : Nat := 118140960795 + 3116143 * 2 ^ 59
def prefixEnd_3116143 : Nat := 4983230072969 + 3 ^ 40 * 3116143 * 2
def baseEnd_3116143 : Nat := 1600079147143506809881625

theorem tailTrace_3116143 : CollatzResearch.WordTrace tailWord_3116143 prefixEnd_3116143 1600079147143506809881625 := by
  unfold tailWord_3116143
  simp only [CollatzResearch.WordTrace]
  refine ⟨113655072349753580699313083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75770048233169053799542055 113655072349753580699313083)
  ·
    refine ⟨170482608524630371048969625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113655072349753580699313083 170482608524630371048969625)
    ·
      refine ⟨127861956393472778286727219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170482608524630371048969625 127861956393472778286727219)
      ·
        refine ⟨191792934590209167430090829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127861956393472778286727219 191792934590209167430090829)
        ·
          refine ⟨71922350471328437786284061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191792934590209167430090829 71922350471328437786284061)
          ·
            refine ⟨26970881426748164169856523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71922350471328437786284061 26970881426748164169856523)
            ·
              refine ⟨40456322140122246254784785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26970881426748164169856523 40456322140122246254784785)
              ·
                refine ⟨30342241605091684691088589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40456322140122246254784785 30342241605091684691088589)
                ·
                  refine ⟨11378340601909381759158221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30342241605091684691088589 11378340601909381759158221)
                  ·
                    refine ⟨4266877725716018159684333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11378340601909381759158221 4266877725716018159684333)
                    ·
                      refine ⟨1600079147143506809881625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4266877725716018159684333 1600079147143506809881625)
                      ·
                        rfl

theorem cell23_3116143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 3].length) (baseStart_3116143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116143 prefixEnd_3116143 := by exact prefixLift 3116143
  have htrace : WordTrace (prefixWord ++ tailWord_3116143) baseStart_3116143 baseEnd_3116143 := by
    simpa [prefixWord, tailWord_3116143, baseEnd_3116143] using wordTrace_append hprefix tailTrace_3116143
  have hstable : (prefixWord ++ tailWord_3116143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116143).length < 2 ^ (prefixWord ++ tailWord_3116143).sum := by decide
  have hdescent : baseEnd_3116143 < baseStart_3116143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116144 : List Nat := [2, 1, 1, 1, 5, 1, 3, 4, 1, 2, 2]
def baseStart_3116144 : Nat := 118140960795 + 3116144 * 2 ^ 59
def prefixEnd_3116144 : Nat := 4983230072969 + 3 ^ 40 * 3116144 * 2
def baseEnd_3116144 : Nat := 1600079660624161305969121

theorem tailTrace_3116144 : CollatzResearch.WordTrace tailWord_3116144 prefixEnd_3116144 1600079660624161305969121 := by
  unfold tailWord_3116144
  simp only [CollatzResearch.WordTrace]
  refine ⟨56827554411374978935049743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75770072548499971913399657 56827554411374978935049743)
  ·
    refine ⟨85241331617062468402574615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56827554411374978935049743 85241331617062468402574615)
    ·
      refine ⟨127861997425593702603861923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85241331617062468402574615 127861997425593702603861923)
      ·
        refine ⟨191792996138390553905792885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127861997425593702603861923 191792996138390553905792885)
        ·
          refine ⟨17980593387974114428668083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191792996138390553905792885 17980593387974114428668083)
          ·
            refine ⟨26970890081961171643002125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17980593387974114428668083 26970890081961171643002125)
            ·
              refine ⟨10114083780735439366125797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26970890081961171643002125 10114083780735439366125797)
              ·
                refine ⟨1896390708887894881148587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10114083780735439366125797 1896390708887894881148587)
                ·
                  refine ⟨2844586063331842321722881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896390708887894881148587 2844586063331842321722881)
                  ·
                    refine ⟨2133439547498881741292161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2844586063331842321722881 2133439547498881741292161)
                    ·
                      refine ⟨1600079660624161305969121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133439547498881741292161 1600079660624161305969121)
                      ·
                        rfl

theorem cell23_3116144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 1, 2, 2].length) (baseStart_3116144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116144 prefixEnd_3116144 := by exact prefixLift 3116144
  have htrace : WordTrace (prefixWord ++ tailWord_3116144) baseStart_3116144 baseEnd_3116144 := by
    simpa [prefixWord, tailWord_3116144, baseEnd_3116144] using wordTrace_append hprefix tailTrace_3116144
  have hstable : (prefixWord ++ tailWord_3116144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116144).length < 2 ^ (prefixWord ++ tailWord_3116144).sum := by decide
  have hdescent : baseEnd_3116144 < baseStart_3116144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116193 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 4, 6]
def baseStart_3116193 : Nat := 118140960795 + 3116193 * 2 ^ 59
def prefixEnd_3116193 : Nat := 4983230072969 + 3 ^ 40 * 3116193 * 2
def baseEnd_3116193 : Nat := 533368273725410538085465

theorem tailTrace_3116193 : CollatzResearch.WordTrace tailWord_3116193 prefixEnd_3116193 533368273725410538085465 := by
  unfold tailWord_3116193
  simp only [CollatzResearch.WordTrace]
  refine ⟨113656895999572439238633233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75771263999714959492422155 113656895999572439238633233)
  ·
    refine ⟨85242671999679329428974925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113656895999572439238633233 85242671999679329428974925)
    ·
      refine ⟨31966001999879748535865597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85242671999679329428974925 31966001999879748535865597)
      ·
        refine ⟨11987250749954905700949599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31966001999879748535865597 11987250749954905700949599)
        ·
          refine ⟨17980876124932358551424399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11987250749954905700949599 17980876124932358551424399)
          ·
            refine ⟨26971314187398537827136599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17980876124932358551424399 26971314187398537827136599)
            ·
              refine ⟨40456971281097806740704899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26971314187398537827136599 40456971281097806740704899)
              ·
                refine ⟨60685456921646710111057349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40456971281097806740704899 60685456921646710111057349)
                ·
                  refine ⟨11378523172808758145823253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60685456921646710111057349 11378523172808758145823253)
                  ·
                    refine ⟨533368273725410538085465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11378523172808758145823253 533368273725410538085465)
                    ·
                      rfl

theorem cell23_3116193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_3116193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116193 prefixEnd_3116193 := by exact prefixLift 3116193
  have htrace : WordTrace (prefixWord ++ tailWord_3116193) baseStart_3116193 baseEnd_3116193 := by
    simpa [prefixWord, tailWord_3116193, baseEnd_3116193] using wordTrace_append hprefix tailTrace_3116193
  have hstable : (prefixWord ++ tailWord_3116193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116193).length < 2 ^ (prefixWord ++ tailWord_3116193).sum := by decide
  have hdescent : baseEnd_3116193 < baseStart_3116193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116194 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3116194 : Nat := 118140960795 + 3116194 * 2 ^ 59
def prefixEnd_3116194 : Nat := 4983230072969 + 3 ^ 40 * 3116194 * 2
def baseEnd_3116194 : Nat := 1600105334656886110343891

theorem tailTrace_3116194 : CollatzResearch.WordTrace tailWord_3116194 prefixEnd_3116194 1600105334656886110343891 := by
  unfold tailWord_3116194
  simp only [CollatzResearch.WordTrace]
  refine ⟨28414233118142204102354909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75771288315045877606279757 28414233118142204102354909)
  ·
    refine ⟨10655337419303326538383091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28414233118142204102354909 10655337419303326538383091)
    ·
      refine ⟨15983006128954989807574637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10655337419303326538383091 15983006128954989807574637)
      ·
        refine ⟨5993627298358121177840489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15983006128954989807574637 5993627298358121177840489)
        ·
          refine ⟨4495220473768590883380367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5993627298358121177840489 4495220473768590883380367)
          ·
            refine ⟨6742830710652886325070551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495220473768590883380367 6742830710652886325070551)
            ·
              refine ⟨10114246065979329487605827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742830710652886325070551 10114246065979329487605827)
              ·
                refine ⟨15171369098968994231408741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10114246065979329487605827 15171369098968994231408741)
                ·
                  refine ⟨2844631706056686418389139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15171369098968994231408741 2844631706056686418389139)
                  ·
                    refine ⟨4266947559085029627583709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2844631706056686418389139 4266947559085029627583709)
                    ·
                      refine ⟨1600105334656886110343891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4266947559085029627583709 1600105334656886110343891)
                      ·
                        rfl

theorem cell23_3116194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3116194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116194 prefixEnd_3116194 := by exact prefixLift 3116194
  have htrace : WordTrace (prefixWord ++ tailWord_3116194) baseStart_3116194 baseEnd_3116194 := by
    simpa [prefixWord, tailWord_3116194, baseEnd_3116194] using wordTrace_append hprefix tailTrace_3116194
  have hstable : (prefixWord ++ tailWord_3116194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116194).length < 2 ^ (prefixWord ++ tailWord_3116194).sum := by decide
  have hdescent : baseEnd_3116194 < baseStart_3116194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116217 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 1, 4, 2]
def baseStart_3116217 : Nat := 118140960795 + 3116217 * 2 ^ 59
def prefixEnd_3116217 : Nat := 4983230072969 + 3 ^ 40 * 3116217 * 2
def baseEnd_3116217 : Nat := 1600117144711939520356285

theorem tailTrace_3116217 : CollatzResearch.WordTrace tailWord_3116217 prefixEnd_3116217 1600117144711939520356285 := by
  unfold tailWord_3116217
  simp only [CollatzResearch.WordTrace]
  refine ⟨113657771351485491337506905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75771847567656994225004603 113657771351485491337506905)
  ·
    refine ⟨85243328513614118503130179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113657771351485491337506905 85243328513614118503130179)
    ·
      refine ⟨127864992770421177754695269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85243328513614118503130179 127864992770421177754695269)
      ·
        refine ⟨23974686144453970829005363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127864992770421177754695269 23974686144453970829005363)
        ·
          refine ⟨35962029216680956243508045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23974686144453970829005363 35962029216680956243508045)
          ·
            refine ⟨13485760956255358591315517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35962029216680956243508045 13485760956255358591315517)
            ·
              refine ⟨5057160358595759471743319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13485760956255358591315517 5057160358595759471743319)
              ·
                refine ⟨7585740537893639207614979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057160358595759471743319 7585740537893639207614979)
                ·
                  refine ⟨11378610806840458811422469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7585740537893639207614979 11378610806840458811422469)
                  ·
                    refine ⟨2133489526282586027141713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11378610806840458811422469 2133489526282586027141713)
                    ·
                      refine ⟨1600117144711939520356285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133489526282586027141713 1600117144711939520356285)
                      ·
                        rfl

theorem cell23_3116217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_3116217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116217 prefixEnd_3116217 := by exact prefixLift 3116217
  have htrace : WordTrace (prefixWord ++ tailWord_3116217) baseStart_3116217 baseEnd_3116217 := by
    simpa [prefixWord, tailWord_3116217, baseEnd_3116217] using wordTrace_append hprefix tailTrace_3116217
  have hstable : (prefixWord ++ tailWord_3116217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116217).length < 2 ^ (prefixWord ++ tailWord_3116217).sum := by decide
  have hdescent : baseEnd_3116217 < baseStart_3116217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116223 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 7]
def baseStart_3116223 : Nat := 118140960795 + 3116223 * 2 ^ 59
def prefixEnd_3116223 : Nat := 4983230072969 + 3 ^ 40 * 3116223 * 2
def baseEnd_3116223 : Nat := 177791136177318499653473

theorem tailTrace_3116223 : CollatzResearch.WordTrace tailWord_3116223 prefixEnd_3116223 177791136177318499653473 := by
  unfold tailWord_3116223
  simp only [CollatzResearch.WordTrace]
  refine ⟨113657990189463754362225323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75771993459642502908150215 113657990189463754362225323)
  ·
    refine ⟨170486985284195631543337985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113657990189463754362225323 170486985284195631543337985)
    ·
      refine ⟨127865238963146723657503489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170486985284195631543337985 127865238963146723657503489)
      ·
        refine ⟨95898929222360042743127617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127865238963146723657503489 95898929222360042743127617)
        ·
          refine ⟨71924196916770032057345713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95898929222360042743127617 71924196916770032057345713)
          ·
            refine ⟨53943147687577524043009285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71924196916770032057345713 53943147687577524043009285)
            ·
              refine ⟨10114340191420785758064241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53943147687577524043009285 10114340191420785758064241)
              ·
                refine ⟨7585755143565589318548181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10114340191420785758064241 7585755143565589318548181)
                ·
                  refine ⟨177791136177318499653473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7585755143565589318548181 177791136177318499653473)
                  ·
                    rfl

theorem cell23_3116223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 7].length) (baseStart_3116223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116223 prefixEnd_3116223 := by exact prefixLift 3116223
  have htrace : WordTrace (prefixWord ++ tailWord_3116223) baseStart_3116223 baseEnd_3116223 := by
    simpa [prefixWord, tailWord_3116223, baseEnd_3116223] using wordTrace_append hprefix tailTrace_3116223
  have hstable : (prefixWord ++ tailWord_3116223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116223).length < 2 ^ (prefixWord ++ tailWord_3116223).sum := by decide
  have hdescent : baseEnd_3116223 < baseStart_3116223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116400 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_3116400 : Nat := 118140960795 + 3116400 * 2 ^ 59
def prefixEnd_3116400 : Nat := 4983230072969 + 3 ^ 40 * 3116400 * 2
def baseEnd_3116400 : Nat := 1600211111671712304367943

theorem tailTrace_3116400 : CollatzResearch.WordTrace tailWord_3116400 prefixEnd_3116400 1600211111671712304367943 := by
  unfold tailWord_3116400
  simp only [CollatzResearch.WordTrace]
  refine ⟨56832222954911256795709327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75776297273215009060945769 56832222954911256795709327)
  ·
    refine ⟨85248334432366885193563991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56832222954911256795709327 85248334432366885193563991)
    ·
      refine ⟨127872501648550327790345987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85248334432366885193563991 127872501648550327790345987)
      ·
        refine ⟨191808752472825491685518981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127872501648550327790345987 191808752472825491685518981)
        ·
          refine ⟨35964141088654779691034809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191808752472825491685518981 35964141088654779691034809)
          ·
            refine ⟨26973105816491084768276107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35964141088654779691034809 26973105816491084768276107)
            ·
              refine ⟨40459658724736627152414161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26973105816491084768276107 40459658724736627152414161)
              ·
                refine ⟨30344744043552470364310621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40459658724736627152414161 30344744043552470364310621)
                ·
                  refine ⟨11379279016332176386616483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30344744043552470364310621 11379279016332176386616483)
                  ·
                    refine ⟨17068918524498264579924725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11379279016332176386616483 17068918524498264579924725)
                    ·
                      refine ⟨1600211111671712304367943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17068918524498264579924725 1600211111671712304367943)
                      ·
                        rfl

theorem cell23_3116400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_3116400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116400 prefixEnd_3116400 := by exact prefixLift 3116400
  have htrace : WordTrace (prefixWord ++ tailWord_3116400) baseStart_3116400 baseEnd_3116400 := by
    simpa [prefixWord, tailWord_3116400, baseEnd_3116400] using wordTrace_append hprefix tailTrace_3116400
  have hstable : (prefixWord ++ tailWord_3116400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116400).length < 2 ^ (prefixWord ++ tailWord_3116400).sum := by decide
  have hdescent : baseEnd_3116400 < baseStart_3116400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116418 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_3116418 : Nat := 118140960795 + 3116418 * 2 ^ 59
def prefixEnd_3116418 : Nat := 4983230072969 + 3 ^ 40 * 3116418 * 2
def baseEnd_3116418 : Nat := 1600220354323493233942861

theorem tailTrace_3116418 : CollatzResearch.WordTrace tailWord_3116418 prefixEnd_3116418 1600220354323493233942861 := by
  unfold tailWord_3116418
  simp only [CollatzResearch.WordTrace]
  refine ⟨28416275605939325666393477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75776734949171535110382605 28416275605939325666393477)
  ·
    refine ⟨5328051676113623562448777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28416275605939325666393477 5328051676113623562448777)
    ·
      refine ⟨3996038757085217671836583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5328051676113623562448777 3996038757085217671836583)
      ·
        refine ⟨5994058135627826507754875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996038757085217671836583 5994058135627826507754875)
        ·
          refine ⟨8991087203441739761632313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5994058135627826507754875 8991087203441739761632313)
          ·
            refine ⟨6743315402581304821224235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8991087203441739761632313 6743315402581304821224235)
            ·
              refine ⟨10114973103871957231836353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6743315402581304821224235 10114973103871957231836353)
              ·
                refine ⟨7586229827903967923877265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10114973103871957231836353 7586229827903967923877265)
                ·
                  refine ⟨5689672370927975942907949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7586229827903967923877265 5689672370927975942907949)
                  ·
                    refine ⟨2133627139097990978590481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5689672370927975942907949 2133627139097990978590481)
                    ·
                      refine ⟨1600220354323493233942861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133627139097990978590481 1600220354323493233942861)
                      ·
                        rfl

theorem cell23_3116418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_3116418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116418 prefixEnd_3116418 := by exact prefixLift 3116418
  have htrace : WordTrace (prefixWord ++ tailWord_3116418) baseStart_3116418 baseEnd_3116418 := by
    simpa [prefixWord, tailWord_3116418, baseEnd_3116418] using wordTrace_append hprefix tailTrace_3116418
  have hstable : (prefixWord ++ tailWord_3116418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116418).length < 2 ^ (prefixWord ++ tailWord_3116418).sum := by decide
  have hdescent : baseEnd_3116418 < baseStart_3116418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116420 : List Nat := [2, 3, 2, 1, 1, 3, 11]
def baseStart_3116420 : Nat := 118140960795 + 3116420 * 2 ^ 59
def prefixEnd_3116420 : Nat := 4983230072969 + 3 ^ 40 * 3116420 * 2
def baseEnd_3116420 : Nat := 19755819522034595384171

theorem tailTrace_3116420 : CollatzResearch.WordTrace tailWord_3116420 prefixEnd_3116420 19755819522034595384171 := by
  unfold tailWord_3116420
  simp only [CollatzResearch.WordTrace]
  refine ⟨56832587684875028503573357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75776783579833371338097809 56832587684875028503573357)
  ·
    refine ⟨21312220381828135688840009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56832587684875028503573357 21312220381828135688840009)
    ·
      refine ⟨15984165286371101766630007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21312220381828135688840009 15984165286371101766630007)
      ·
        refine ⟨23976247929556652649945011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15984165286371101766630007 23976247929556652649945011)
        ·
          refine ⟨35964371894334978974917517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23976247929556652649945011 35964371894334978974917517)
          ·
            refine ⟨13486639460375617115594069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35964371894334978974917517 13486639460375617115594069)
            ·
              refine ⟨19755819522034595384171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13486639460375617115594069 19755819522034595384171)
              ·
                rfl

theorem cell23_3116420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 11].length) (baseStart_3116420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116420 prefixEnd_3116420 := by exact prefixLift 3116420
  have htrace : WordTrace (prefixWord ++ tailWord_3116420) baseStart_3116420 baseEnd_3116420 := by
    simpa [prefixWord, tailWord_3116420, baseEnd_3116420] using wordTrace_append hprefix tailTrace_3116420
  have hstable : (prefixWord ++ tailWord_3116420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116420).length < 2 ^ (prefixWord ++ tailWord_3116420).sum := by decide
  have hdescent : baseEnd_3116420 < baseStart_3116420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116441 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 2, 4]
def baseStart_3116441 : Nat := 118140960795 + 3116441 * 2 ^ 59
def prefixEnd_3116441 : Nat := 4983230072969 + 3 ^ 40 * 3116441 * 2
def baseEnd_3116441 : Nat := 533410721459515547985085

theorem tailTrace_3116441 : CollatzResearch.WordTrace tailWord_3116441 prefixEnd_3116441 533410721459515547985085 := by
  unfold tailWord_3116441
  simp only [CollatzResearch.WordTrace]
  refine ⟨113665941302673977593661177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75777294201782651729107451 113665941302673977593661177)
  ·
    refine ⟨85249455977005483195245883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113665941302673977593661177 85249455977005483195245883)
    ·
      refine ⟨127874183965508224792868825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85249455977005483195245883 127874183965508224792868825)
      ·
        refine ⟨95905637974131168594651619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127874183965508224792868825 95905637974131168594651619)
        ·
          refine ⟨143858456961196752891977429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95905637974131168594651619 143858456961196752891977429)
          ·
            refine ⟨3371682585028048895905721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 143858456961196752891977429 3371682585028048895905721)
            ·
              refine ⟨2528761938771036671929291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3371682585028048895905721 2528761938771036671929291)
              ·
                refine ⟨3793142908156555007893937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528761938771036671929291 3793142908156555007893937)
                ·
                  refine ⟨2844857181117416255920453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3793142908156555007893937 2844857181117416255920453)
                  ·
                    refine ⟨533410721459515547985085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2844857181117416255920453 533410721459515547985085)
                    ·
                      rfl

theorem cell23_3116441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 2, 4].length) (baseStart_3116441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116441 prefixEnd_3116441 := by exact prefixLift 3116441
  have htrace : WordTrace (prefixWord ++ tailWord_3116441) baseStart_3116441 baseEnd_3116441 := by
    simpa [prefixWord, tailWord_3116441, baseEnd_3116441] using wordTrace_append hprefix tailTrace_3116441
  have hstable : (prefixWord ++ tailWord_3116441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116441).length < 2 ^ (prefixWord ++ tailWord_3116441).sum := by decide
  have hdescent : baseEnd_3116441 < baseStart_3116441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116460 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_3116460 : Nat := 118140960795 + 3116460 * 2 ^ 59
def prefixEnd_3116460 : Nat := 4983230072969 + 3 ^ 40 * 3116460 * 2
def baseEnd_3116460 : Nat := 1600241920510982069617667

theorem tailTrace_3116460 : CollatzResearch.WordTrace tailWord_3116460 prefixEnd_3116460 1600241920510982069617667 := by
  unfold tailWord_3116460
  simp only [CollatzResearch.WordTrace]
  refine ⟨56833317144802571919301417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75777756193070095892401889 56833317144802571919301417)
  ·
    refine ⟨42624987858601928939476063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56833317144802571919301417 42624987858601928939476063)
    ·
      refine ⟨63937481787902893409214095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42624987858601928939476063 63937481787902893409214095)
      ·
        refine ⟨95906222681854340113821143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63937481787902893409214095 95906222681854340113821143)
        ·
          refine ⟨143859334022781510170731715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95906222681854340113821143 143859334022781510170731715)
          ·
            refine ⟨215789001034172265256097573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143859334022781510170731715 215789001034172265256097573)
            ·
              refine ⟨40460437693907299735518295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215789001034172265256097573 40460437693907299735518295)
              ·
                refine ⟨60690656540860949603277443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40460437693907299735518295 60690656540860949603277443)
                ·
                  refine ⟨91035984811291424404916165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60690656540860949603277443 91035984811291424404916165)
                  ·
                    refine ⟨17069247152117142075921781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91035984811291424404916165 17069247152117142075921781)
                    ·
                      refine ⟨1600241920510982069617667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17069247152117142075921781 1600241920510982069617667)
                      ·
                        rfl

theorem cell23_3116460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_3116460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116460 prefixEnd_3116460 := by exact prefixLift 3116460
  have htrace : WordTrace (prefixWord ++ tailWord_3116460) baseStart_3116460 baseEnd_3116460 := by
    simpa [prefixWord, tailWord_3116460, baseEnd_3116460] using wordTrace_append hprefix tailTrace_3116460
  have hstable : (prefixWord ++ tailWord_3116460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116460).length < 2 ^ (prefixWord ++ tailWord_3116460).sum := by decide
  have hdescent : baseEnd_3116460 < baseStart_3116460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116504 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 1, 4, 2]
def baseStart_3116504 : Nat := 118140960795 + 3116504 * 2 ^ 59
def prefixEnd_3116504 : Nat := 4983230072969 + 3 ^ 40 * 3116504 * 2
def baseEnd_3116504 : Nat := 1600264513659779897467465

theorem tailTrace_3116504 : CollatzResearch.WordTrace tailWord_3116504 prefixEnd_3116504 1600264513659779897467465 := by
  unfold tailWord_3116504
  simp only [CollatzResearch.WordTrace]
  refine ⟨56834119550722869676602283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75778826067630492902136377 56834119550722869676602283)
  ·
    refine ⟨85251179326084304514903425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56834119550722869676602283 85251179326084304514903425)
    ·
      refine ⟨63938384494563228386177569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85251179326084304514903425 63938384494563228386177569)
      ·
        refine ⟨47953788370922421289633177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63938384494563228386177569 47953788370922421289633177)
        ·
          refine ⟨35965341278191815967224883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47953788370922421289633177 35965341278191815967224883)
          ·
            refine ⟨53948011917287723950837325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35965341278191815967224883 53948011917287723950837325)
            ·
              refine ⟨20230504468982896481563997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53948011917287723950837325 20230504468982896481563997)
              ·
                refine ⟨7586439175868586180586499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20230504468982896481563997 7586439175868586180586499)
                ·
                  refine ⟨11379658763802879270879749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7586439175868586180586499 11379658763802879270879749)
                  ·
                    refine ⟨2133686018213039863289953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11379658763802879270879749 2133686018213039863289953)
                    ·
                      refine ⟨1600264513659779897467465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133686018213039863289953 1600264513659779897467465)
                      ·
                        rfl

theorem cell23_3116504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_3116504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116504 prefixEnd_3116504 := by exact prefixLift 3116504
  have htrace : WordTrace (prefixWord ++ tailWord_3116504) baseStart_3116504 baseEnd_3116504 := by
    simpa [prefixWord, tailWord_3116504, baseEnd_3116504] using wordTrace_append hprefix tailTrace_3116504
  have hstable : (prefixWord ++ tailWord_3116504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116504).length < 2 ^ (prefixWord ++ tailWord_3116504).sum := by decide
  have hdescent : baseEnd_3116504 < baseStart_3116504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116534 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3116534 : Nat := 118140960795 + 3116534 * 2 ^ 59
def prefixEnd_3116534 : Nat := 4983230072969 + 3 ^ 40 * 3116534 * 2
def baseEnd_3116534 : Nat := 1600279918079414780092327

theorem tailTrace_3116534 : CollatzResearch.WordTrace tailWord_3116534 prefixEnd_3116534 1600279918079414780092327 := by
  unfold tailWord_3116534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7104333330708565904799791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75779555527558036317864437 7104333330708565904799791)
  ·
    refine ⟨10656499996062848857199687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7104333330708565904799791 10656499996062848857199687)
    ·
      refine ⟨15984749994094273285799531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10656499996062848857199687 15984749994094273285799531)
      ·
        refine ⟨23977124991141409928699297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15984749994094273285799531 23977124991141409928699297)
        ·
          refine ⟨17982843743356057446524473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23977124991141409928699297 17982843743356057446524473)
          ·
            refine ⟨13487132807517043084893355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17982843743356057446524473 13487132807517043084893355)
            ·
              refine ⟨20230699211275564627340033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13487132807517043084893355 20230699211275564627340033)
              ·
                refine ⟨15173024408456673470505025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20230699211275564627340033 15173024408456673470505025)
                ·
                  refine ⟨11379768306342505102878769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15173024408456673470505025 11379768306342505102878769)
                  ·
                    refine ⟨8534826229756878827159077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11379768306342505102878769 8534826229756878827159077)
                    ·
                      refine ⟨1600279918079414780092327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8534826229756878827159077 1600279918079414780092327)
                      ·
                        rfl

theorem cell23_3116534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3116534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116534 prefixEnd_3116534 := by exact prefixLift 3116534
  have htrace : WordTrace (prefixWord ++ tailWord_3116534) baseStart_3116534 baseEnd_3116534 := by
    simpa [prefixWord, tailWord_3116534, baseEnd_3116534] using wordTrace_append hprefix tailTrace_3116534
  have hstable : (prefixWord ++ tailWord_3116534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116534).length < 2 ^ (prefixWord ++ tailWord_3116534).sum := by decide
  have hdescent : baseEnd_3116534 < baseStart_3116534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116554 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_3116554 : Nat := 118140960795 + 3116554 * 2 ^ 59
def prefixEnd_3116554 : Nat := 4983230072969 + 3 ^ 40 * 3116554 * 2
def baseEnd_3116554 : Nat := 1600290187692504701842235

theorem tailTrace_3116554 : CollatzResearch.WordTrace tailWord_3116554 prefixEnd_3116554 1600290187692504701842235 := by
  unfold tailWord_3116554
  simp only [CollatzResearch.WordTrace]
  refine ⟨28417515687816149473131179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75780041834176398595016477 28417515687816149473131179)
  ·
    refine ⟨42626273531724224209696769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28417515687816149473131179 42626273531724224209696769)
    ·
      refine ⟨31969705148793168157272577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42626273531724224209696769 31969705148793168157272577)
      ·
        refine ⟨23977278861594876117954433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31969705148793168157272577 23977278861594876117954433)
        ·
          refine ⟨17982959146196157088465825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23977278861594876117954433 17982959146196157088465825)
          ·
            refine ⟨13487219359647117816349369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17982959146196157088465825 13487219359647117816349369)
            ·
              refine ⟨10115414519735338362262027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13487219359647117816349369 10115414519735338362262027)
              ·
                refine ⟨15173121779603007543393041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10115414519735338362262027 15173121779603007543393041)
                ·
                  refine ⟨11379841334702255657544781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15173121779603007543393041 11379841334702255657544781)
                  ·
                    refine ⟨4267440500513345871579293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11379841334702255657544781 4267440500513345871579293)
                    ·
                      refine ⟨1600290187692504701842235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4267440500513345871579293 1600290187692504701842235)
                      ·
                        rfl

theorem cell23_3116554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_3116554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116554 prefixEnd_3116554 := by exact prefixLift 3116554
  have htrace : WordTrace (prefixWord ++ tailWord_3116554) baseStart_3116554 baseEnd_3116554 := by
    simpa [prefixWord, tailWord_3116554, baseEnd_3116554] using wordTrace_append hprefix tailTrace_3116554
  have hstable : (prefixWord ++ tailWord_3116554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116554).length < 2 ^ (prefixWord ++ tailWord_3116554).sum := by decide
  have hdescent : baseEnd_3116554 < baseStart_3116554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116555 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 2, 2, 2]
def baseStart_3116555 : Nat := 118140960795 + 3116555 * 2 ^ 59
def prefixEnd_3116555 : Nat := 4983230072969 + 3 ^ 40 * 3116555 * 2
def baseEnd_3116555 : Nat := 1600290701173159197929731

theorem tailTrace_3116555 : CollatzResearch.WordTrace tailWord_3116555 prefixEnd_3116555 1600290701173159197929731 := by
  unfold tailWord_3116555
  simp only [CollatzResearch.WordTrace]
  refine ⟨113670099224260975063311119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75780066149507316708874079 113670099224260975063311119)
  ·
    refine ⟨170505148836391462594966679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113670099224260975063311119 170505148836391462594966679)
    ·
      refine ⟨255757723254587193892450019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170505148836391462594966679 255757723254587193892450019)
      ·
        refine ⟨383636584881880790838675029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255757723254587193892450019 383636584881880790838675029)
        ·
          refine ⟨4495741229084540517640723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 383636584881880790838675029 4495741229084540517640723)
          ·
            refine ⟨6743611843626810776461085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495741229084540517640723 6743611843626810776461085)
            ·
              refine ⟨2528854441360054041172907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6743611843626810776461085 2528854441360054041172907)
              ·
                refine ⟨3793281662040081061759361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528854441360054041172907 3793281662040081061759361)
                ·
                  refine ⟨2844961246530060796319521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3793281662040081061759361 2844961246530060796319521)
                  ·
                    refine ⟨2133720934897545597239641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2844961246530060796319521 2133720934897545597239641)
                    ·
                      refine ⟨1600290701173159197929731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133720934897545597239641 1600290701173159197929731)
                      ·
                        rfl

theorem cell23_3116555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 2, 2, 2].length) (baseStart_3116555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116555 prefixEnd_3116555 := by exact prefixLift 3116555
  have htrace : WordTrace (prefixWord ++ tailWord_3116555) baseStart_3116555 baseEnd_3116555 := by
    simpa [prefixWord, tailWord_3116555, baseEnd_3116555] using wordTrace_append hprefix tailTrace_3116555
  have hstable : (prefixWord ++ tailWord_3116555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116555).length < 2 ^ (prefixWord ++ tailWord_3116555).sum := by decide
  have hdescent : baseEnd_3116555 < baseStart_3116555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116631 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 3]
def baseStart_3116631 : Nat := 118140960795 + 3116631 * 2 ^ 59
def prefixEnd_3116631 : Nat := 4983230072969 + 3 ^ 40 * 3116631 * 2
def baseEnd_3116631 : Nat := 1600329725702900900579381

theorem tailTrace_3116631 : CollatzResearch.WordTrace tailWord_3116631 prefixEnd_3116631 1600329725702900900579381 := by
  unfold tailWord_3116631
  simp only [CollatzResearch.WordTrace]
  refine ⟨113672871171985640043077747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75781914114657093362051831 113672871171985640043077747)
  ·
    refine ⟨170509306757978460064616621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113672871171985640043077747 170509306757978460064616621)
    ·
      refine ⟨63940990034241922524231233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170509306757978460064616621 63940990034241922524231233)
      ·
        refine ⟨47955742525681441893173425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63940990034241922524231233 47955742525681441893173425)
        ·
          refine ⟨35966806894261081419880069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47955742525681441893173425 35966806894261081419880069)
          ·
            refine ⟨6743776292673952766227513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35966806894261081419880069 6743776292673952766227513)
            ·
              refine ⟨5057832219505464574670635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6743776292673952766227513 5057832219505464574670635)
              ·
                refine ⟨7586748329258196862005953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057832219505464574670635 7586748329258196862005953)
                ·
                  refine ⟨5690061246943647646504465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7586748329258196862005953 5690061246943647646504465)
                  ·
                    refine ⟨4267545935207735734878349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5690061246943647646504465 4267545935207735734878349)
                    ·
                      refine ⟨1600329725702900900579381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4267545935207735734878349 1600329725702900900579381)
                      ·
                        rfl

theorem cell23_3116631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_3116631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116631 prefixEnd_3116631 := by exact prefixLift 3116631
  have htrace : WordTrace (prefixWord ++ tailWord_3116631) baseStart_3116631 baseEnd_3116631 := by
    simpa [prefixWord, tailWord_3116631, baseEnd_3116631] using wordTrace_append hprefix tailTrace_3116631
  have hstable : (prefixWord ++ tailWord_3116631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116631).length < 2 ^ (prefixWord ++ tailWord_3116631).sum := by decide
  have hdescent : baseEnd_3116631 < baseStart_3116631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116657 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_3116657 : Nat := 118140960795 + 3116657 * 2 ^ 59
def prefixEnd_3116657 : Nat := 4983230072969 + 3 ^ 40 * 3116657 * 2
def baseEnd_3116657 : Nat := 1600343076199917798854261

theorem tailTrace_3116657 : CollatzResearch.WordTrace tailWord_3116657 prefixEnd_3116657 1600343076199917798854261 := by
  unfold tailWord_3116657
  simp only [CollatzResearch.WordTrace]
  refine ⟨113673819469891446483524225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75782546313260964322349483 113673819469891446483524225)
  ·
    refine ⟨85255364602418584862643169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113673819469891446483524225 85255364602418584862643169)
    ·
      refine ⟨63941523451813938646982377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85255364602418584862643169 63941523451813938646982377)
      ·
        refine ⟨47956142588860453985236783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63941523451813938646982377 47956142588860453985236783)
        ·
          refine ⟨71934213883290680977855175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47956142588860453985236783 71934213883290680977855175)
          ·
            refine ⟨107901320824936021466782763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71934213883290680977855175 107901320824936021466782763)
            ·
              refine ⟨161851981237404032200174145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107901320824936021466782763 161851981237404032200174145)
              ·
                refine ⟨121388985928053024150130609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161851981237404032200174145 121388985928053024150130609)
                ·
                  refine ⟨91041739446039768112597957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121388985928053024150130609 91041739446039768112597957)
                  ·
                    refine ⟨17070326146132456521112117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91041739446039768112597957 17070326146132456521112117)
                    ·
                      refine ⟨1600343076199917798854261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17070326146132456521112117 1600343076199917798854261)
                      ·
                        rfl

theorem cell23_3116657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_3116657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116657 prefixEnd_3116657 := by exact prefixLift 3116657
  have htrace : WordTrace (prefixWord ++ tailWord_3116657) baseStart_3116657 baseEnd_3116657 := by
    simpa [prefixWord, tailWord_3116657, baseEnd_3116657] using wordTrace_append hprefix tailTrace_3116657
  have hstable : (prefixWord ++ tailWord_3116657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116657).length < 2 ^ (prefixWord ++ tailWord_3116657).sum := by decide
  have hdescent : baseEnd_3116657 < baseStart_3116657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116684 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3116684 : Nat := 118140960795 + 3116684 * 2 ^ 59
def prefixEnd_3116684 : Nat := 4983230072969 + 3 ^ 40 * 3116684 * 2
def baseEnd_3116684 : Nat := 1600356940177589193216637

theorem tailTrace_3116684 : CollatzResearch.WordTrace tailWord_3116684 prefixEnd_3116684 1600356940177589193216637 := by
  unfold tailWord_3116684
  simp only [CollatzResearch.WordTrace]
  refine ⟨56837402120396815047378553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75783202827195753396504737 56837402120396815047378553)
  ·
    refine ⟨42628051590297611285533915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56837402120396815047378553 42628051590297611285533915)
    ·
      refine ⟨63942077385446416928300873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42628051590297611285533915 63942077385446416928300873)
      ·
        refine ⟨47956558039084812696225655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63942077385446416928300873 47956558039084812696225655)
        ·
          refine ⟨71934837058627219044338483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47956558039084812696225655 71934837058627219044338483)
          ·
            refine ⟨107902255587940828566507725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71934837058627219044338483 107902255587940828566507725)
            ·
              refine ⟨40463345845477810712440397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107902255587940828566507725 40463345845477810712440397)
              ·
                refine ⟨15173754692054179017165149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40463345845477810712440397 15173754692054179017165149)
                ·
                  refine ⟨5690158009520317131436931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15173754692054179017165149 5690158009520317131436931)
                  ·
                    refine ⟨8535237014280475697155397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5690158009520317131436931 8535237014280475697155397)
                    ·
                      refine ⟨1600356940177589193216637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8535237014280475697155397 1600356940177589193216637)
                      ·
                        rfl

theorem cell23_3116684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3116684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116684 prefixEnd_3116684 := by exact prefixLift 3116684
  have htrace : WordTrace (prefixWord ++ tailWord_3116684) baseStart_3116684 baseEnd_3116684 := by
    simpa [prefixWord, tailWord_3116684, baseEnd_3116684] using wordTrace_append hprefix tailTrace_3116684
  have hstable : (prefixWord ++ tailWord_3116684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116684).length < 2 ^ (prefixWord ++ tailWord_3116684).sum := by decide
  have hdescent : baseEnd_3116684 < baseStart_3116684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116687 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_3116687 : Nat := 118140960795 + 3116687 * 2 ^ 59
def prefixEnd_3116687 : Nat := 4983230072969 + 3 ^ 40 * 3116687 * 2
def baseEnd_3116687 : Nat := 1600358480619552681479123

theorem tailTrace_3116687 : CollatzResearch.WordTrace tailWord_3116687 prefixEnd_3116687 1600358480619552681479123 := by
  unfold tailWord_3116687
  simp only [CollatzResearch.WordTrace]
  refine ⟨113674913659782761607116315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75783275773188507738077543 113674913659782761607116315)
  ·
    refine ⟨170512370489674142410674473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113674913659782761607116315 170512370489674142410674473)
    ·
      refine ⟨127884277867255606808005855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170512370489674142410674473 127884277867255606808005855)
      ·
        refine ⟨191826416800883410212008783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127884277867255606808005855 191826416800883410212008783)
        ·
          refine ⟨287739625201325115318013175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191826416800883410212008783 287739625201325115318013175)
          ·
            refine ⟨431609437801987672977019763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287739625201325115318013175 431609437801987672977019763)
            ·
              refine ⟨647414156702981509465529645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431609437801987672977019763 647414156702981509465529645)
              ·
                refine ⟨242780308763618066049573617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 647414156702981509465529645 242780308763618066049573617)
                ·
                  refine ⟨182085231572713549537180213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242780308763618066049573617 182085231572713549537180213)
                  ·
                    refine ⟨17070490459941895269110645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 182085231572713549537180213 17070490459941895269110645)
                    ·
                      refine ⟨1600358480619552681479123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17070490459941895269110645 1600358480619552681479123)
                      ·
                        rfl

theorem cell23_3116687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_3116687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116687 prefixEnd_3116687 := by exact prefixLift 3116687
  have htrace : WordTrace (prefixWord ++ tailWord_3116687) baseStart_3116687 baseEnd_3116687 := by
    simpa [prefixWord, tailWord_3116687, baseEnd_3116687] using wordTrace_append hprefix tailTrace_3116687
  have hstable : (prefixWord ++ tailWord_3116687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116687).length < 2 ^ (prefixWord ++ tailWord_3116687).sum := by decide
  have hdescent : baseEnd_3116687 < baseStart_3116687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116695 : List Nat := [1, 1, 3, 3, 2, 3, 2, 3, 1, 1, 3]
def baseStart_3116695 : Nat := 118140960795 + 3116695 * 2 ^ 59
def prefixEnd_3116695 : Nat := 4983230072969 + 3 ^ 40 * 3116695 * 2
def baseEnd_3116695 : Nat := 1600362588464788650179087

theorem tailTrace_3116695 : CollatzResearch.WordTrace tailWord_3116695 prefixEnd_3116695 1600362588464788650179087 := by
  unfold tailWord_3116695
  simp only [CollatzResearch.WordTrace]
  refine ⟨113675205443753778973407539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75783470295835852648938359 113675205443753778973407539)
  ·
    refine ⟨170512808165630668460111309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113675205443753778973407539 170512808165630668460111309)
    ·
      refine ⟨63942303062111500672541741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170512808165630668460111309 63942303062111500672541741)
      ·
        refine ⟨23978363648291812752203153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63942303062111500672541741 23978363648291812752203153)
        ·
          refine ⟨17983772736218859564152365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23978363648291812752203153 17983772736218859564152365)
          ·
            refine ⟨6743914776082072336557137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17983772736218859564152365 6743914776082072336557137)
            ·
              refine ⟨5057936082061554252417853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6743914776082072336557137 5057936082061554252417853)
              ·
                refine ⟨1896726030773082844656695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5057936082061554252417853 1896726030773082844656695)
                ·
                  refine ⟨2845089046159624266985043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896726030773082844656695 2845089046159624266985043)
                  ·
                    refine ⟨4267633569239436400477565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2845089046159624266985043 4267633569239436400477565)
                    ·
                      refine ⟨1600362588464788650179087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4267633569239436400477565 1600362588464788650179087)
                      ·
                        rfl

theorem cell23_3116695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_3116695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116695 prefixEnd_3116695 := by exact prefixLift 3116695
  have htrace : WordTrace (prefixWord ++ tailWord_3116695) baseStart_3116695 baseEnd_3116695 := by
    simpa [prefixWord, tailWord_3116695, baseEnd_3116695] using wordTrace_append hprefix tailTrace_3116695
  have hstable : (prefixWord ++ tailWord_3116695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116695).length < 2 ^ (prefixWord ++ tailWord_3116695).sum := by decide
  have hdescent : baseEnd_3116695 < baseStart_3116695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116707 : List Nat := [1, 1, 1, 4, 1, 1, 14]
def baseStart_3116707 : Nat := 118140960795 + 3116707 * 2 ^ 59
def prefixEnd_3116707 : Nat := 4983230072969 + 3 ^ 40 * 3116707 * 2
def baseEnd_3116707 : Nat := 19757638891761019792951

theorem tailTrace_3116707 : CollatzResearch.WordTrace tailWord_3116707 prefixEnd_3116707 19757638891761019792951 := by
  unfold tailWord_3116707
  simp only [CollatzResearch.WordTrace]
  refine ⟨113675643119710305022844375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75783762079806870015229583 113675643119710305022844375)
  ·
    refine ⟨170513464679565457534266563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113675643119710305022844375 170513464679565457534266563)
    ·
      refine ⟨255770197019348186301399845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170513464679565457534266563 255770197019348186301399845)
      ·
        refine ⟨47956911941127784931512471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255770197019348186301399845 47956911941127784931512471)
        ·
          refine ⟨71935367911691677397268707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47956911941127784931512471 71935367911691677397268707)
          ·
            refine ⟨107903051867537516095903061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71935367911691677397268707 107903051867537516095903061)
            ·
              refine ⟨19757638891761019792951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 107903051867537516095903061 19757638891761019792951)
              ·
                rfl

theorem cell23_3116707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 14].length) (baseStart_3116707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116707 prefixEnd_3116707 := by exact prefixLift 3116707
  have htrace : WordTrace (prefixWord ++ tailWord_3116707) baseStart_3116707 baseEnd_3116707 := by
    simpa [prefixWord, tailWord_3116707, baseEnd_3116707] using wordTrace_append hprefix tailTrace_3116707
  have hstable : (prefixWord ++ tailWord_3116707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116707).length < 2 ^ (prefixWord ++ tailWord_3116707).sum := by decide
  have hdescent : baseEnd_3116707 < baseStart_3116707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116769 : List Nat := [1, 2, 3, 1, 5, 1, 3, 2, 1, 2, 2]
def baseStart_3116769 : Nat := 118140960795 + 3116769 * 2 ^ 59
def prefixEnd_3116769 : Nat := 4983230072969 + 3 ^ 40 * 3116769 * 2
def baseEnd_3116769 : Nat := 1600400586033221360653747

theorem tailTrace_3116769 : CollatzResearch.WordTrace tailWord_3116769 prefixEnd_3116769 1600400586033221360653747 := by
  unfold tailWord_3116769
  simp only [CollatzResearch.WordTrace]
  refine ⟨113677904445485689611601361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75785269630323793074400907 113677904445485689611601361)
  ·
    refine ⟨85258428334114267208701021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113677904445485689611601361 85258428334114267208701021)
    ·
      refine ⟨31971910625292850203262883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85258428334114267208701021 31971910625292850203262883)
      ·
        refine ⟨47957865937939275304894325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31971910625292850203262883 47957865937939275304894325)
        ·
          refine ⟨4496049931681807059833843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47957865937939275304894325 4496049931681807059833843)
          ·
            refine ⟨6744074897522710589750765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496049931681807059833843 6744074897522710589750765)
            ·
              refine ⟨2529028086571016471156537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6744074897522710589750765 2529028086571016471156537)
              ·
                refine ⟨1896771064928262353367403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529028086571016471156537 1896771064928262353367403)
                ·
                  refine ⟨2845156597392393530051105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896771064928262353367403 2845156597392393530051105)
                  ·
                    refine ⟨2133867448044295147538329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2845156597392393530051105 2133867448044295147538329)
                    ·
                      refine ⟨1600400586033221360653747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133867448044295147538329 1600400586033221360653747)
                      ·
                        rfl

theorem cell23_3116769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_3116769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116769 prefixEnd_3116769 := by exact prefixLift 3116769
  have htrace : WordTrace (prefixWord ++ tailWord_3116769) baseStart_3116769 baseEnd_3116769 := by
    simpa [prefixWord, tailWord_3116769, baseEnd_3116769] using wordTrace_append hprefix tailTrace_3116769
  have hstable : (prefixWord ++ tailWord_3116769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116769).length < 2 ^ (prefixWord ++ tailWord_3116769).sum := by decide
  have hdescent : baseEnd_3116769 < baseStart_3116769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116785 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 2, 1, 3]
def baseStart_3116785 : Nat := 118140960795 + 3116785 * 2 ^ 59
def prefixEnd_3116785 : Nat := 4983230072969 + 3 ^ 40 * 3116785 * 2
def baseEnd_3116785 : Nat := 1600408801723693298053673

theorem tailTrace_3116785 : CollatzResearch.WordTrace tailWord_3116785 prefixEnd_3116785 1600408801723693298053673 := by
  unfold tailWord_3116785
  simp only [CollatzResearch.WordTrace]
  refine ⟨113678488013427724344183809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75785658675618482896122539 113678488013427724344183809)
  ·
    refine ⟨85258866010070793258137857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113678488013427724344183809 85258866010070793258137857)
    ·
      refine ⟨63944149507553094943603393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85258866010070793258137857 63944149507553094943603393)
      ·
        refine ⟨47958112130664821207702545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63944149507553094943603393 47958112130664821207702545)
        ·
          refine ⟨35968584097998615905776909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47958112130664821207702545 35968584097998615905776909)
          ·
            refine ⟨13488219036749480964666341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35968584097998615905776909 13488219036749480964666341)
            ·
              refine ⟨2529041069390527680874939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13488219036749480964666341 2529041069390527680874939)
              ·
                refine ⟨3793561604085791521312409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529041069390527680874939 3793561604085791521312409)
                ·
                  refine ⟨2845171203064343640984307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3793561604085791521312409 2845171203064343640984307)
                  ·
                    refine ⟨4267756804596515461476461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2845171203064343640984307 4267756804596515461476461)
                    ·
                      refine ⟨1600408801723693298053673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4267756804596515461476461 1600408801723693298053673)
                      ·
                        rfl

theorem cell23_3116785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_3116785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116785 prefixEnd_3116785 := by exact prefixLift 3116785
  have htrace : WordTrace (prefixWord ++ tailWord_3116785) baseStart_3116785 baseEnd_3116785 := by
    simpa [prefixWord, tailWord_3116785, baseEnd_3116785] using wordTrace_append hprefix tailTrace_3116785
  have hstable : (prefixWord ++ tailWord_3116785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116785).length < 2 ^ (prefixWord ++ tailWord_3116785).sum := by decide
  have hdescent : baseEnd_3116785 < baseStart_3116785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116806 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3116806 : Nat := 118140960795 + 3116806 * 2 ^ 59
def prefixEnd_3116806 : Nat := 4983230072969 + 3 ^ 40 * 3116806 * 2
def baseEnd_3116806 : Nat := 1600419584817437715891077

theorem tailTrace_3116806 : CollatzResearch.WordTrace tailWord_3116806 prefixEnd_3116806 1600419584817437715891077 := by
  unfold tailWord_3116806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552476685823488904084321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75786169297567763287132181 3552476685823488904084321)
  ·
    refine ⟨2664357514367616678063241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3552476685823488904084321 2664357514367616678063241)
    ·
      refine ⟨1998268135775712508547431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2664357514367616678063241 1998268135775712508547431)
      ·
        refine ⟨2997402203663568762821147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998268135775712508547431 2997402203663568762821147)
        ·
          refine ⟨4496103305495353144231721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2997402203663568762821147 4496103305495353144231721)
          ·
            refine ⟨3372077479121514858173791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4496103305495353144231721 3372077479121514858173791)
            ·
              refine ⟨5058116218682272287260687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372077479121514858173791 5058116218682272287260687)
              ·
                refine ⟨7587174328023408430891031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5058116218682272287260687 7587174328023408430891031)
                ·
                  refine ⟨11380761492035112646336547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7587174328023408430891031 11380761492035112646336547)
                  ·
                    refine ⟨17071142238052668969504821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11380761492035112646336547 17071142238052668969504821)
                    ·
                      refine ⟨1600419584817437715891077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17071142238052668969504821 1600419584817437715891077)
                      ·
                        rfl

theorem cell23_3116806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3116806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116806 prefixEnd_3116806 := by exact prefixLift 3116806
  have htrace : WordTrace (prefixWord ++ tailWord_3116806) baseStart_3116806 baseEnd_3116806 := by
    simpa [prefixWord, tailWord_3116806, baseEnd_3116806] using wordTrace_append hprefix tailTrace_3116806
  have hstable : (prefixWord ++ tailWord_3116806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116806).length < 2 ^ (prefixWord ++ tailWord_3116806).sum := by decide
  have hdescent : baseEnd_3116806 < baseStart_3116806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116808 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 1, 4, 2]
def baseStart_3116808 : Nat := 118140960795 + 3116808 * 2 ^ 59
def prefixEnd_3116808 : Nat := 4983230072969 + 3 ^ 40 * 3116808 * 2
def baseEnd_3116808 : Nat := 1600420611778746708066067

theorem tailTrace_3116808 : CollatzResearch.WordTrace tailWord_3116808 prefixEnd_3116808 1600420611778746708066067 := by
  unfold tailWord_3116808
  simp only [CollatzResearch.WordTrace]
  refine ⟨56839663446172199636135539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75786217928229599514847385 56839663446172199636135539)
  ·
    refine ⟨85259495169258299454203309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56839663446172199636135539 85259495169258299454203309)
    ·
      refine ⟨31972310688471862295326241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85259495169258299454203309 31972310688471862295326241)
      ·
        refine ⟨23979233016353896721494681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31972310688471862295326241 23979233016353896721494681)
        ·
          refine ⟨17984424762265422541121011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23979233016353896721494681 17984424762265422541121011)
          ·
            refine ⟨26976637143398133811681517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17984424762265422541121011 26976637143398133811681517)
            ·
              refine ⟨10116238928774300179380569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26976637143398133811681517 10116238928774300179380569)
              ·
                refine ⟨7587179196580725134535427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10116238928774300179380569 7587179196580725134535427)
                ·
                  refine ⟨11380768794871087701803141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7587179196580725134535427 11380768794871087701803141)
                  ·
                    refine ⟨2133894149038328944088089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11380768794871087701803141 2133894149038328944088089)
                    ·
                      refine ⟨1600420611778746708066067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133894149038328944088089 1600420611778746708066067)
                      ·
                        rfl

theorem cell23_3116808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_3116808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116808 prefixEnd_3116808 := by exact prefixLift 3116808
  have htrace : WordTrace (prefixWord ++ tailWord_3116808) baseStart_3116808 baseEnd_3116808 := by
    simpa [prefixWord, tailWord_3116808, baseEnd_3116808] using wordTrace_append hprefix tailTrace_3116808
  have hstable : (prefixWord ++ tailWord_3116808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116808).length < 2 ^ (prefixWord ++ tailWord_3116808).sum := by decide
  have hdescent : baseEnd_3116808 < baseStart_3116808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116820 : List Nat := [2, 4, 4, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_3116820 : Nat := 118140960795 + 3116820 * 2 ^ 59
def prefixEnd_3116820 : Nat := 4983230072969 + 3 ^ 40 * 3116820 * 2
def baseEnd_3116820 : Nat := 1600426773546600661116013

theorem tailTrace_3116820 : CollatzResearch.WordTrace tailWord_3116820 prefixEnd_3116820 1600426773546600661116013 := by
  unfold tailWord_3116820
  simp only [CollatzResearch.WordTrace]
  refine ⟨56839882284150462660853957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75786509712200616881138609 56839882284150462660853957)
  ·
    refine ⟨10657477928278211748910117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56839882284150462660853957 10657477928278211748910117)
    ·
      refine ⟨1998277111552164702920647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10657477928278211748910117 1998277111552164702920647)
      ·
        refine ⟨2997415667328247054380971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998277111552164702920647 2997415667328247054380971)
        ·
          refine ⟨4496123500992370581571457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2997415667328247054380971 4496123500992370581571457)
          ·
            refine ⟨3372092625744277936178593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4496123500992370581571457 3372092625744277936178593)
            ·
              refine ⟨2529069469308208452133945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372092625744277936178593 2529069469308208452133945)
              ·
                refine ⟨1896802101981156339100459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529069469308208452133945 1896802101981156339100459)
                ·
                  refine ⟨2845203152971734508650689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896802101981156339100459 2845203152971734508650689)
                  ·
                    refine ⟨2133902364728800881488017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2845203152971734508650689 2133902364728800881488017)
                    ·
                      refine ⟨1600426773546600661116013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2133902364728800881488017 1600426773546600661116013)
                      ·
                        rfl

theorem cell23_3116820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_3116820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116820 prefixEnd_3116820 := by exact prefixLift 3116820
  have htrace : WordTrace (prefixWord ++ tailWord_3116820) baseStart_3116820 baseEnd_3116820 := by
    simpa [prefixWord, tailWord_3116820, baseEnd_3116820] using wordTrace_append hprefix tailTrace_3116820
  have hstable : (prefixWord ++ tailWord_3116820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116820).length < 2 ^ (prefixWord ++ tailWord_3116820).sum := by decide
  have hdescent : baseEnd_3116820 < baseStart_3116820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116824 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3116824 : Nat := 118140960795 + 3116824 * 2 ^ 59
def prefixEnd_3116824 : Nat := 4983230072969 + 3 ^ 40 * 3116824 * 2
def baseEnd_3116824 : Nat := 1600428827469218645465993

theorem tailTrace_3116824 : CollatzResearch.WordTrace tailWord_3116824 prefixEnd_3116824 1600428827469218645465993 := by
  unfold tailWord_3116824
  simp only [CollatzResearch.WordTrace]
  refine ⟨56839955230143217002426763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75786606973524289336569017 56839955230143217002426763)
  ·
    refine ⟨85259932845214825503640145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56839955230143217002426763 85259932845214825503640145)
    ·
      refine ⟨63944949633911119127730109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85259932845214825503640145 63944949633911119127730109)
      ·
        refine ⟨23979356112716669672898791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63944949633911119127730109 23979356112716669672898791)
        ·
          refine ⟨35969034169075004509348187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23979356112716669672898791 35969034169075004509348187)
          ·
            refine ⟨53953551253612506764022281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35969034169075004509348187 53953551253612506764022281)
            ·
              refine ⟨40465163440209380073016711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53953551253612506764022281 40465163440209380073016711)
              ·
                refine ⟨60697745160314070109525067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40465163440209380073016711 60697745160314070109525067)
                ·
                  refine ⟨91046617740471105164287601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60697745160314070109525067 91046617740471105164287601)
                  ·
                    refine ⟨68284963305353328873215701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91046617740471105164287601 68284963305353328873215701)
                    ·
                      refine ⟨1600428827469218645465993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68284963305353328873215701 1600428827469218645465993)
                      ·
                        rfl

theorem cell23_3116824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3116824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116824 prefixEnd_3116824 := by exact prefixLift 3116824
  have htrace : WordTrace (prefixWord ++ tailWord_3116824) baseStart_3116824 baseEnd_3116824 := by
    simpa [prefixWord, tailWord_3116824, baseEnd_3116824] using wordTrace_append hprefix tailTrace_3116824
  have hstable : (prefixWord ++ tailWord_3116824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116824).length < 2 ^ (prefixWord ++ tailWord_3116824).sum := by decide
  have hdescent : baseEnd_3116824 < baseStart_3116824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116898 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3116898 : Nat := 118140960795 + 3116898 * 2 ^ 59
def prefixEnd_3116898 : Nat := 4983230072969 + 3 ^ 40 * 3116898 * 2
def baseEnd_3116898 : Nat := 1600466825037651355940653

theorem tailTrace_3116898 : CollatzResearch.WordTrace tailWord_3116898 prefixEnd_3116898 1600466825037651355940653 := by
  unfold tailWord_3116898
  simp only [CollatzResearch.WordTrace]
  refine ⟨28420652365504586160761837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75788406308012229762031565 28420652365504586160761837)
  ·
    refine ⟨10657744637064219810285689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28420652365504586160761837 10657744637064219810285689)
    ·
      refine ⟨7993308477798164857714267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10657744637064219810285689 7993308477798164857714267)
      ·
        refine ⟨11989962716697247286571401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7993308477798164857714267 11989962716697247286571401)
        ·
          refine ⟨8992472037522935464928551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11989962716697247286571401 8992472037522935464928551)
          ·
            refine ⟨13488708056284403197392827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8992472037522935464928551 13488708056284403197392827)
            ·
              refine ⟨20233062084426604796089241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13488708056284403197392827 20233062084426604796089241)
              ·
                refine ⟨15174796563319953597066931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20233062084426604796089241 15174796563319953597066931)
                ·
                  refine ⟨22762194844979930395600397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15174796563319953597066931 22762194844979930395600397)
                  ·
                    refine ⟨8535823066867473898350149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22762194844979930395600397 8535823066867473898350149)
                    ·
                      refine ⟨1600466825037651355940653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8535823066867473898350149 1600466825037651355940653)
                      ·
                        rfl

theorem cell23_3116898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3116898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116898 prefixEnd_3116898 := by exact prefixLift 3116898
  have htrace : WordTrace (prefixWord ++ tailWord_3116898) baseStart_3116898 baseEnd_3116898 := by
    simpa [prefixWord, tailWord_3116898, baseEnd_3116898] using wordTrace_append hprefix tailTrace_3116898
  have hstable : (prefixWord ++ tailWord_3116898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116898).length < 2 ^ (prefixWord ++ tailWord_3116898).sum := by decide
  have hdescent : baseEnd_3116898 < baseStart_3116898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116908 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_3116908 : Nat := 118140960795 + 3116908 * 2 ^ 59
def prefixEnd_3116908 : Nat := 4983230072969 + 3 ^ 40 * 3116908 * 2
def baseEnd_3116908 : Nat := 533490653281398772271869

theorem tailTrace_3116908 : CollatzResearch.WordTrace tailWord_3116908 prefixEnd_3116908 533490653281398772271869 := by
  unfold tailWord_3116908
  simp only [CollatzResearch.WordTrace]
  refine ⟨56841487095991058175455689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75788649461321410900607585 56841487095991058175455689)
  ·
    refine ⟨42631115321993293631591767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56841487095991058175455689 42631115321993293631591767)
    ·
      refine ⟨63946672982989940447387651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42631115321993293631591767 63946672982989940447387651)
      ·
        refine ⟨95920009474484910671081477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63946672982989940447387651 95920009474484910671081477)
        ·
          refine ⟨17985001776465920750827777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95920009474484910671081477 17985001776465920750827777)
          ·
            refine ⟨13488751332349440563120833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17985001776465920750827777 13488751332349440563120833)
            ·
              refine ⟨10116563499262080422340625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13488751332349440563120833 10116563499262080422340625)
              ·
                refine ⟨7587422624446560316755469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10116563499262080422340625 7587422624446560316755469)
                ·
                  refine ⟨2845283484167460118783301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7587422624446560316755469 2845283484167460118783301)
                  ·
                    refine ⟨533490653281398772271869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2845283484167460118783301 533490653281398772271869)
                    ·
                      rfl

theorem cell23_3116908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_3116908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116908 prefixEnd_3116908 := by exact prefixLift 3116908
  have htrace : WordTrace (prefixWord ++ tailWord_3116908) baseStart_3116908 baseEnd_3116908 := by
    simpa [prefixWord, tailWord_3116908, baseEnd_3116908] using wordTrace_append hprefix tailTrace_3116908
  have hstable : (prefixWord ++ tailWord_3116908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116908).length < 2 ^ (prefixWord ++ tailWord_3116908).sum := by decide
  have hdescent : baseEnd_3116908 < baseStart_3116908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116935 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_3116935 : Nat := 118140960795 + 3116935 * 2 ^ 59
def prefixEnd_3116935 : Nat := 4983230072969 + 3 ^ 40 * 3116935 * 2
def baseEnd_3116935 : Nat := 1600485823821867711177983

theorem tailTrace_3116935 : CollatzResearch.WordTrace tailWord_3116935 prefixEnd_3116935 1600485823821867711177983 := by
  unfold tailWord_3116935
  simp only [CollatzResearch.WordTrace]
  refine ⟨113683958962884299962144259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75789305975256199974762839 113683958962884299962144259)
  ·
    refine ⟨170525938444326449943216389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113683958962884299962144259 170525938444326449943216389)
    ·
      refine ⟨31973613458311209364353073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170525938444326449943216389 31973613458311209364353073)
      ·
        refine ⟨23980210093733407023264805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31973613458311209364353073 23980210093733407023264805)
        ·
          refine ⟨4496289392575013816862151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23980210093733407023264805 4496289392575013816862151)
          ·
            refine ⟨6744434088862520725293227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496289392575013816862151 6744434088862520725293227)
            ·
              refine ⟨10116651133293781087939841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6744434088862520725293227 10116651133293781087939841)
              ·
                refine ⟨7587488349970335815954881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10116651133293781087939841 7587488349970335815954881)
                ·
                  refine ⟨5690616262477751861966161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7587488349970335815954881 5690616262477751861966161)
                  ·
                    refine ⟨4267962196858313896474621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5690616262477751861966161 4267962196858313896474621)
                    ·
                      refine ⟨1600485823821867711177983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4267962196858313896474621 1600485823821867711177983)
                      ·
                        rfl

theorem cell23_3116935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_3116935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116935 prefixEnd_3116935 := by exact prefixLift 3116935
  have htrace : WordTrace (prefixWord ++ tailWord_3116935) baseStart_3116935 baseEnd_3116935 := by
    simpa [prefixWord, tailWord_3116935, baseEnd_3116935] using wordTrace_append hprefix tailTrace_3116935
  have hstable : (prefixWord ++ tailWord_3116935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116935).length < 2 ^ (prefixWord ++ tailWord_3116935).sum := by decide
  have hdescent : baseEnd_3116935 < baseStart_3116935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116975 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 2, 3, 2]
def baseStart_3116975 : Nat := 118140960795 + 3116975 * 2 ^ 59
def prefixEnd_3116975 : Nat := 4983230072969 + 3 ^ 40 * 3116975 * 2
def baseEnd_3116975 : Nat := 1600506363048047554677799

theorem tailTrace_3116975 : CollatzResearch.WordTrace tailWord_3116975 prefixEnd_3116975 1600506363048047554677799 := by
  unfold tailWord_3116975
  simp only [CollatzResearch.WordTrace]
  refine ⟨113685417882739386793600379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75790278588492924529066919 113685417882739386793600379)
  ·
    refine ⟨170528126824109080190400569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113685417882739386793600379 170528126824109080190400569)
    ·
      refine ⟨127896095118081810142800427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170528126824109080190400569 127896095118081810142800427)
      ·
        refine ⟨191844142677122715214200641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127896095118081810142800427 191844142677122715214200641)
        ·
          refine ⟨143883107007842036410650481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191844142677122715214200641 143883107007842036410650481)
          ·
            refine ⟨107912330255881527307987861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143883107007842036410650481 107912330255881527307987861)
            ·
              refine ⟨5058390480744446592561931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107912330255881527307987861 5058390480744446592561931)
              ·
                refine ⟨7587585721116669888842897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5058390480744446592561931 7587585721116669888842897)
                ·
                  refine ⟨5690689290837502416632173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7587585721116669888842897 5690689290837502416632173)
                  ·
                    refine ⟨2134008484064063406237065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5690689290837502416632173 2134008484064063406237065)
                    ·
                      refine ⟨1600506363048047554677799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134008484064063406237065 1600506363048047554677799)
                      ·
                        rfl

theorem cell23_3116975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 3, 2].length) (baseStart_3116975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116975 prefixEnd_3116975 := by exact prefixLift 3116975
  have htrace : WordTrace (prefixWord ++ tailWord_3116975) baseStart_3116975 baseEnd_3116975 := by
    simpa [prefixWord, tailWord_3116975, baseEnd_3116975] using wordTrace_append hprefix tailTrace_3116975
  have hstable : (prefixWord ++ tailWord_3116975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116975).length < 2 ^ (prefixWord ++ tailWord_3116975).sum := by decide
  have hdescent : baseEnd_3116975 < baseStart_3116975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116985 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 1, 5]
def baseStart_3116985 : Nat := 118140960795 + 3116985 * 2 ^ 59
def prefixEnd_3116985 : Nat := 4983230072969 + 3 ^ 40 * 3116985 * 2
def baseEnd_3116985 : Nat := 533503832618197505184251

theorem tailTrace_3116985 : CollatzResearch.WordTrace tailWord_3116985 prefixEnd_3116985 533503832618197505184251 := by
  unfold tailWord_3116985
  simp only [CollatzResearch.WordTrace]
  refine ⟨113685782612703158501464409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75790521741802105667642939 113685782612703158501464409)
  ·
    refine ⟨85264336959527368876098307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113685782612703158501464409 85264336959527368876098307)
    ·
      refine ⟨127896505439291053314147461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85264336959527368876098307 127896505439291053314147461)
      ·
        refine ⟨23980594769867072496402649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127896505439291053314147461 23980594769867072496402649)
        ·
          refine ⟨17985446077400304372301987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23980594769867072496402649 17985446077400304372301987)
          ·
            refine ⟨26978169116100456558452981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17985446077400304372301987 26978169116100456558452981)
            ·
              refine ⟨2529203354634417802354967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26978169116100456558452981 2529203354634417802354967)
              ·
                refine ⟨3793805031951626703532451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529203354634417802354967 3793805031951626703532451)
                ·
                  refine ⟨5690707547927440055298677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3793805031951626703532451 5690707547927440055298677)
                  ·
                    refine ⟨533503832618197505184251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5690707547927440055298677 533503832618197505184251)
                    ·
                      rfl

theorem cell23_3116985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 5].length) (baseStart_3116985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3116985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3116985 prefixEnd_3116985 := by exact prefixLift 3116985
  have htrace : WordTrace (prefixWord ++ tailWord_3116985) baseStart_3116985 baseEnd_3116985 := by
    simpa [prefixWord, tailWord_3116985, baseEnd_3116985] using wordTrace_append hprefix tailTrace_3116985
  have hstable : (prefixWord ++ tailWord_3116985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116985).length < 2 ^ (prefixWord ++ tailWord_3116985).sum := by decide
  have hdescent : baseEnd_3116985 < baseStart_3116985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117008 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 3]
def baseStart_3117008 : Nat := 118140960795 + 3117008 * 2 ^ 59
def prefixEnd_3117008 : Nat := 4983230072969 + 3 ^ 40 * 3117008 * 2
def baseEnd_3117008 : Nat := 1600523307909645925565147

theorem tailTrace_3117008 : CollatzResearch.WordTrace tailWord_3117008 prefixEnd_3117008 1600523307909645925565147 := by
  unfold tailWord_3117008
  simp only [CollatzResearch.WordTrace]
  refine ⟨56843310745809916714775839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75791080994413222286367785 56843310745809916714775839)
  ·
    refine ⟨85264966118714875072163759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56843310745809916714775839 85264966118714875072163759)
    ·
      refine ⟨127897449178072312608245639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85264966118714875072163759 127897449178072312608245639)
      ·
        refine ⟨191846173767108468912368459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127897449178072312608245639 191846173767108468912368459)
        ·
          refine ⟨287769260650662703368552689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191846173767108468912368459 287769260650662703368552689)
          ·
            refine ⟨215826945487997027526414517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287769260650662703368552689 215826945487997027526414517)
            ·
              refine ⟨20233776139499721330601361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215826945487997027526414517 20233776139499721330601361)
              ·
                refine ⟨15175332104624790997951021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20233776139499721330601361 15175332104624790997951021)
                ·
                  refine ⟨5690749539234296624231633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15175332104624790997951021 5690749539234296624231633)
                  ·
                    refine ⟨4268062154425722468173725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5690749539234296624231633 4268062154425722468173725)
                    ·
                      refine ⟨1600523307909645925565147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4268062154425722468173725 1600523307909645925565147)
                      ·
                        rfl

theorem cell23_3117008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 3].length) (baseStart_3117008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117008 prefixEnd_3117008 := by exact prefixLift 3117008
  have htrace : WordTrace (prefixWord ++ tailWord_3117008) baseStart_3117008 baseEnd_3117008 := by
    simpa [prefixWord, tailWord_3117008, baseEnd_3117008] using wordTrace_append hprefix tailTrace_3117008
  have hstable : (prefixWord ++ tailWord_3117008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117008).length < 2 ^ (prefixWord ++ tailWord_3117008).sum := by decide
  have hdescent : baseEnd_3117008 < baseStart_3117008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117026 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3117026 : Nat := 118140960795 + 3117026 * 2 ^ 59
def prefixEnd_3117026 : Nat := 4983230072969 + 3 ^ 40 * 3117026 * 2
def baseEnd_3117026 : Nat := 1600532550561426855140065

theorem tailTrace_3117026 : CollatzResearch.WordTrace tailWord_3117026 prefixEnd_3117026 1600532550561426855140065 := by
  unfold tailWord_3117026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28421819501388655625926733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75791518670369748335804621 28421819501388655625926733)
  ·
    refine ⟨10658182313020745859722525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28421819501388655625926733 10658182313020745859722525)
    ·
      refine ⟨3996818367382779697395947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10658182313020745859722525 3996818367382779697395947)
      ·
        refine ⟨5995227551074169546093921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996818367382779697395947 5995227551074169546093921)
        ·
          refine ⟨4496420663305627159570441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5995227551074169546093921 4496420663305627159570441)
          ·
            refine ⟨3372315497479220369677831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4496420663305627159570441 3372315497479220369677831)
            ·
              refine ⟨5058473246218830554516747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372315497479220369677831 5058473246218830554516747)
              ·
                refine ⟨7587709869328245831775121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5058473246218830554516747 7587709869328245831775121)
                ·
                  refine ⟨5690782401996184373831341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7587709869328245831775121 5690782401996184373831341)
                  ·
                    refine ⟨2134043400748569140186753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5690782401996184373831341 2134043400748569140186753)
                    ·
                      refine ⟨1600532550561426855140065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134043400748569140186753 1600532550561426855140065)
                      ·
                        rfl

theorem cell23_3117026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3117026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117026 prefixEnd_3117026 := by exact prefixLift 3117026
  have htrace : WordTrace (prefixWord ++ tailWord_3117026) baseStart_3117026 baseEnd_3117026 := by
    simpa [prefixWord, tailWord_3117026, baseEnd_3117026] using wordTrace_append hprefix tailTrace_3117026
  have hstable : (prefixWord ++ tailWord_3117026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117026).length < 2 ^ (prefixWord ++ tailWord_3117026).sum := by decide
  have hdescent : baseEnd_3117026 < baseStart_3117026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117028 : List Nat := [2, 3, 1, 1, 1, 1, 7, 7]
def baseStart_3117028 : Nat := 118140960795 + 3117028 * 2 ^ 59
def prefixEnd_3117028 : Nat := 4983230072969 + 3 ^ 40 * 3117028 * 2
def baseEnd_3117028 : Nat := 59279021389730957307965

theorem tailTrace_3117028 : CollatzResearch.WordTrace tailWord_3117028 prefixEnd_3117028 59279021389730957307965 := by
  unfold tailWord_3117028
  simp only [CollatzResearch.WordTrace]
  refine ⟨56843675475773688422639869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75791567301031584563519825 56843675475773688422639869)
  ·
    refine ⟨21316378303415133158489951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56843675475773688422639869 21316378303415133158489951)
    ·
      refine ⟨31974567455122699737734927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21316378303415133158489951 31974567455122699737734927)
      ·
        refine ⟨47961851182684049606602391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31974567455122699737734927 47961851182684049606602391)
        ·
          refine ⟨71942776774026074409903587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47961851182684049606602391 71942776774026074409903587)
          ·
            refine ⟨107914165161039111614855381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71942776774026074409903587 107914165161039111614855381)
            ·
              refine ⟨2529238245961854178473173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 107914165161039111614855381 2529238245961854178473173)
              ·
                refine ⟨59279021389730957307965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2529238245961854178473173 59279021389730957307965)
                ·
                  rfl

theorem cell23_3117028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 7].length) (baseStart_3117028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117028 prefixEnd_3117028 := by exact prefixLift 3117028
  have htrace : WordTrace (prefixWord ++ tailWord_3117028) baseStart_3117028 baseEnd_3117028 := by
    simpa [prefixWord, tailWord_3117028, baseEnd_3117028] using wordTrace_append hprefix tailTrace_3117028
  have hstable : (prefixWord ++ tailWord_3117028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117028).length < 2 ^ (prefixWord ++ tailWord_3117028).sum := by decide
  have hdescent : baseEnd_3117028 < baseStart_3117028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117039 : List Nat := [1, 1, 2, 1, 4, 2, 4, 3, 1, 2, 2]
def baseStart_3117039 : Nat := 118140960795 + 3117039 * 2 ^ 59
def prefixEnd_3117039 : Nat := 4983230072969 + 3 ^ 40 * 3117039 * 2
def baseEnd_3117039 : Nat := 1600539225809935304277505

theorem tailTrace_3117039 : CollatzResearch.WordTrace tailWord_3117039 prefixEnd_3117039 1600539225809935304277505 := by
  unfold tailWord_3117039
  simp only [CollatzResearch.WordTrace]
  refine ⟨113687752154507525723930171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75791834769671683815953447 113687752154507525723930171)
  ·
    refine ⟨170531628231761288585895257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113687752154507525723930171 170531628231761288585895257)
    ·
      refine ⟨127898721173820966439421443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170531628231761288585895257 127898721173820966439421443)
      ·
        refine ⟨191848081760731449659132165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127898721173820966439421443 191848081760731449659132165)
        ·
          refine ⟨35971515330137146811087281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191848081760731449659132165 35971515330137146811087281)
          ·
            refine ⟨26978636497602860108315461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35971515330137146811087281 26978636497602860108315461)
            ·
              refine ⟨5058494343300536270309149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26978636497602860108315461 5058494343300536270309149)
              ·
                refine ⟨1896935378737701101365931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5058494343300536270309149 1896935378737701101365931)
                ·
                  refine ⟨2845403068106551652048897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896935378737701101365931 2845403068106551652048897)
                  ·
                    refine ⟨2134052301079913739036673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2845403068106551652048897 2134052301079913739036673)
                    ·
                      refine ⟨1600539225809935304277505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134052301079913739036673 1600539225809935304277505)
                      ·
                        rfl

theorem cell23_3117039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 1, 2, 2].length) (baseStart_3117039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117039 prefixEnd_3117039 := by exact prefixLift 3117039
  have htrace : WordTrace (prefixWord ++ tailWord_3117039) baseStart_3117039 baseEnd_3117039 := by
    simpa [prefixWord, tailWord_3117039, baseEnd_3117039] using wordTrace_append hprefix tailTrace_3117039
  have hstable : (prefixWord ++ tailWord_3117039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117039).length < 2 ^ (prefixWord ++ tailWord_3117039).sum := by decide
  have hdescent : baseEnd_3117039 < baseStart_3117039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117069 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3117069 : Nat := 118140960795 + 3117069 * 2 ^ 59
def prefixEnd_3117069 : Nat := 4983230072969 + 3 ^ 40 * 3117069 * 2
def baseEnd_3117069 : Nat := 1600554630229570186902367

theorem tailTrace_3117069 : CollatzResearch.WordTrace tailWord_3117069 prefixEnd_3117069 1600554630229570186902367 := by
  unfold tailWord_3117069
  simp only [CollatzResearch.WordTrace]
  refine ⟨113688846344398840847522261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75792564229599227231681507 113688846344398840847522261)
  ·
    refine ⟨2664582336196847832363803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 113688846344398840847522261 2664582336196847832363803)
    ·
      refine ⟨3996873504295271748545705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2664582336196847832363803 3996873504295271748545705)
      ·
        refine ⟨2997655128221453811409279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3996873504295271748545705 2997655128221453811409279)
        ·
          refine ⟨4496482692332180717113919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2997655128221453811409279 4496482692332180717113919)
          ·
            refine ⟨6744724038498271075670879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496482692332180717113919 6744724038498271075670879)
            ·
              refine ⟨10117086057747406613506319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6744724038498271075670879 10117086057747406613506319)
              ·
                refine ⟨15175629086621109920259479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10117086057747406613506319 15175629086621109920259479)
                ·
                  refine ⟨22763443629931664880389219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15175629086621109920259479 22763443629931664880389219)
                  ·
                    refine ⟨34145165444897497320583829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22763443629931664880389219 34145165444897497320583829)
                    ·
                      refine ⟨1600554630229570186902367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34145165444897497320583829 1600554630229570186902367)
                      ·
                        rfl

theorem cell23_3117069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3117069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117069 prefixEnd_3117069 := by exact prefixLift 3117069
  have htrace : WordTrace (prefixWord ++ tailWord_3117069) baseStart_3117069 baseEnd_3117069 := by
    simpa [prefixWord, tailWord_3117069, baseEnd_3117069] using wordTrace_append hprefix tailTrace_3117069
  have hstable : (prefixWord ++ tailWord_3117069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117069).length < 2 ^ (prefixWord ++ tailWord_3117069).sum := by decide
  have hdescent : baseEnd_3117069 < baseStart_3117069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117076 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3117076 : Nat := 118140960795 + 3117076 * 2 ^ 59
def prefixEnd_3117076 : Nat := 4983230072969 + 3 ^ 40 * 3117076 * 2
def baseEnd_3117076 : Nat := 1600558224594151659514835

theorem tailTrace_3117076 : CollatzResearch.WordTrace tailWord_3117076 prefixEnd_3117076 1600558224594151659514835 := by
  unfold tailWord_3117076
  simp only [CollatzResearch.WordTrace]
  refine ⟨56844550827686740521513541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75792734436915654028684721 56844550827686740521513541)
  ·
    refine ⟨10658353280191263847783789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56844550827686740521513541 10658353280191263847783789)
    ·
      refine ⟨3996882480071723942918921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10658353280191263847783789 3996882480071723942918921)
      ·
        refine ⟨2997661860053792957189191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3996882480071723942918921 2997661860053792957189191)
        ·
          refine ⟨4496492790080689435783787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2997661860053792957189191 4496492790080689435783787)
          ·
            refine ⟨6744739185121034153675681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496492790080689435783787 6744739185121034153675681)
            ·
              refine ⟨5058554388840775615256761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6744739185121034153675681 5058554388840775615256761)
              ·
                refine ⟨3793915791630581711442571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5058554388840775615256761 3793915791630581711442571)
                ·
                  refine ⟨5690873687445872567163857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3793915791630581711442571 5690873687445872567163857)
                  ·
                    refine ⟨4268155265584404425372893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5690873687445872567163857 4268155265584404425372893)
                    ·
                      refine ⟨1600558224594151659514835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4268155265584404425372893 1600558224594151659514835)
                      ·
                        rfl

theorem cell23_3117076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3117076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117076 prefixEnd_3117076 := by exact prefixLift 3117076
  have htrace : WordTrace (prefixWord ++ tailWord_3117076) baseStart_3117076 baseEnd_3117076 := by
    simpa [prefixWord, tailWord_3117076, baseEnd_3117076] using wordTrace_append hprefix tailTrace_3117076
  have hstable : (prefixWord ++ tailWord_3117076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117076).length < 2 ^ (prefixWord ++ tailWord_3117076).sum := by decide
  have hdescent : baseEnd_3117076 < baseStart_3117076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117082 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2]
def baseStart_3117082 : Nat := 118140960795 + 3117082 * 2 ^ 59
def prefixEnd_3117082 : Nat := 4983230072969 + 3 ^ 40 * 3117082 * 2
def baseEnd_3117082 : Nat := 1600561305478078636039807

theorem tailTrace_3117082 : CollatzResearch.WordTrace tailWord_3117082 prefixEnd_3117082 1600561305478078636039807 := by
  unfold tailWord_3117082
  simp only [CollatzResearch.WordTrace]
  refine ⟨28422330123337936016936375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75792880328901162711830333 28422330123337936016936375)
  ·
    refine ⟨42633495185006904025404563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28422330123337936016936375 42633495185006904025404563)
    ·
      refine ⟨63950242777510356038106845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42633495185006904025404563 63950242777510356038106845)
      ·
        refine ⟨23981341041566383514290067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63950242777510356038106845 23981341041566383514290067)
        ·
          refine ⟨35972011562349575271435101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23981341041566383514290067 35972011562349575271435101)
          ·
            refine ⟨13489504335881090726788163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35972011562349575271435101 13489504335881090726788163)
            ·
              refine ⟨20234256503821636090182245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13489504335881090726788163 20234256503821636090182245)
              ·
                refine ⟨3793923094466556766909171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20234256503821636090182245 3793923094466556766909171)
                ·
                  refine ⟨5690884641699835150363757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3793923094466556766909171 5690884641699835150363757)
                  ·
                    refine ⟨2134081740637438181386409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5690884641699835150363757 2134081740637438181386409)
                    ·
                      refine ⟨1600561305478078636039807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134081740637438181386409 1600561305478078636039807)
                      ·
                        rfl

theorem cell23_3117082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_3117082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117082 prefixEnd_3117082 := by exact prefixLift 3117082
  have htrace : WordTrace (prefixWord ++ tailWord_3117082) baseStart_3117082 baseEnd_3117082 := by
    simpa [prefixWord, tailWord_3117082, baseEnd_3117082] using wordTrace_append hprefix tailTrace_3117082
  have hstable : (prefixWord ++ tailWord_3117082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117082).length < 2 ^ (prefixWord ++ tailWord_3117082).sum := by decide
  have hdescent : baseEnd_3117082 < baseStart_3117082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117150 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_3117150 : Nat := 118140960795 + 3117150 * 2 ^ 59
def prefixEnd_3117150 : Nat := 4983230072969 + 3 ^ 40 * 3117150 * 2
def baseEnd_3117150 : Nat := 1600596222162584369989495

theorem tailTrace_3117150 : CollatzResearch.WordTrace tailWord_3117150 prefixEnd_3117150 1600596222162584369989495 := by
  unfold tailWord_3117150
  simp only [CollatzResearch.WordTrace]
  refine ⟨14211475082138173960152613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75794533771403594454147269 14211475082138173960152613)
  ·
    refine ⟨2664651577900907617528615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14211475082138173960152613 2664651577900907617528615)
    ·
      refine ⟨3996977366851361426292923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2664651577900907617528615 3996977366851361426292923)
      ·
        refine ⟨5995466050277042139439385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996977366851361426292923 5995466050277042139439385)
        ·
          refine ⟨4496599537707781604579539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5995466050277042139439385 4496599537707781604579539)
          ·
            refine ⟨6744899306561672406869309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496599537707781604579539 6744899306561672406869309)
            ·
              refine ⟨2529337239960627152575991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6744899306561672406869309 2529337239960627152575991)
              ·
                refine ⟨3794005859940940728863987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529337239960627152575991 3794005859940940728863987)
                ·
                  refine ⟨5691008789911411093295981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794005859940940728863987 5691008789911411093295981)
                  ·
                    refine ⟨2134128296216779159985993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5691008789911411093295981 2134128296216779159985993)
                    ·
                      refine ⟨1600596222162584369989495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134128296216779159985993 1600596222162584369989495)
                      ·
                        rfl

theorem cell23_3117150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_3117150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117150 prefixEnd_3117150 := by exact prefixLift 3117150
  have htrace : WordTrace (prefixWord ++ tailWord_3117150) baseStart_3117150 baseEnd_3117150 := by
    simpa [prefixWord, tailWord_3117150, baseEnd_3117150] using wordTrace_append hprefix tailTrace_3117150
  have hstable : (prefixWord ++ tailWord_3117150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117150).length < 2 ^ (prefixWord ++ tailWord_3117150).sum := by decide
  have hdescent : baseEnd_3117150 < baseStart_3117150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117165 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_3117165 : Nat := 118140960795 + 3117165 * 2 ^ 59
def prefixEnd_3117165 : Nat := 4983230072969 + 3 ^ 40 * 3117165 * 2
def baseEnd_3117165 : Nat := 533534641457467270433975

theorem tailTrace_3117165 : CollatzResearch.WordTrace tailWord_3117165 prefixEnd_3117165 533534641457467270433975 := by
  unfold tailWord_3117165
  simp only [CollatzResearch.WordTrace]
  refine ⟨113692347752051049243016949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75794898501367366162011299 113692347752051049243016949)
  ·
    refine ⟨10658657601754785866532839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113692347752051049243016949 10658657601754785866532839)
    ·
      refine ⟨15987986402632178799799259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10658657601754785866532839 15987986402632178799799259)
      ·
        refine ⟨23981979603948268199698889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15987986402632178799799259 23981979603948268199698889)
        ·
          refine ⟨17986484702961201149774167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23981979603948268199698889 17986484702961201149774167)
          ·
            refine ⟨26979727054441801724661251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17986484702961201149774167 26979727054441801724661251)
            ·
              refine ⟨40469590581662702586991877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26979727054441801724661251 40469590581662702586991877)
              ·
                refine ⟨7588048234061756735060977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40469590581662702586991877 7588048234061756735060977)
                ·
                  refine ⟨5691036175546317551295733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7588048234061756735060977 5691036175546317551295733)
                  ·
                    refine ⟨533534641457467270433975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5691036175546317551295733 533534641457467270433975)
                    ·
                      rfl

theorem cell23_3117165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_3117165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117165 prefixEnd_3117165 := by exact prefixLift 3117165
  have htrace : WordTrace (prefixWord ++ tailWord_3117165) baseStart_3117165 baseEnd_3117165 := by
    simpa [prefixWord, tailWord_3117165, baseEnd_3117165] using wordTrace_append hprefix tailTrace_3117165
  have hstable : (prefixWord ++ tailWord_3117165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117165).length < 2 ^ (prefixWord ++ tailWord_3117165).sum := by decide
  have hdescent : baseEnd_3117165 < baseStart_3117165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117202 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_3117202 : Nat := 118140960795 + 3117202 * 2 ^ 59
def prefixEnd_3117202 : Nat := 4983230072969 + 3 ^ 40 * 3117202 * 2
def baseEnd_3117202 : Nat := 1600622923156618166539255

theorem tailTrace_3117202 : CollatzResearch.WordTrace tailWord_3117202 prefixEnd_3117202 1600622923156618166539255 := by
  unfold tailWord_3117202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28423424313229251140528465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75795798168611336374742573 28423424313229251140528465)
  ·
    refine ⟨21317568234921938355396349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28423424313229251140528465 21317568234921938355396349)
    ·
      refine ⟨7994088088095726883273631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21317568234921938355396349 7994088088095726883273631)
      ·
        refine ⟨11991132132143590324910447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7994088088095726883273631 11991132132143590324910447)
        ·
          refine ⟨17986698198215385487365671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11991132132143590324910447 17986698198215385487365671)
          ·
            refine ⟨26980047297323078231048507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17986698198215385487365671 26980047297323078231048507)
            ·
              refine ⟨40470070945984617346572761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26980047297323078231048507 40470070945984617346572761)
              ·
                refine ⟨30352553209488463009929571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40470070945984617346572761 30352553209488463009929571)
                ·
                  refine ⟨45528829814232694514894357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30352553209488463009929571 45528829814232694514894357)
                  ·
                    refine ⟨2134163897542157555385673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45528829814232694514894357 2134163897542157555385673)
                    ·
                      refine ⟨1600622923156618166539255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134163897542157555385673 1600622923156618166539255)
                      ·
                        rfl

theorem cell23_3117202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_3117202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117202 prefixEnd_3117202 := by exact prefixLift 3117202
  have htrace : WordTrace (prefixWord ++ tailWord_3117202) baseStart_3117202 baseEnd_3117202 := by
    simpa [prefixWord, tailWord_3117202, baseEnd_3117202] using wordTrace_append hprefix tailTrace_3117202
  have hstable : (prefixWord ++ tailWord_3117202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117202).length < 2 ^ (prefixWord ++ tailWord_3117202).sum := by decide
  have hdescent : baseEnd_3117202 < baseStart_3117202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117205 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_3117205 : Nat := 118140960795 + 3117205 * 2 ^ 59
def prefixEnd_3117205 : Nat := 4983230072969 + 3 ^ 40 * 3117205 * 2
def baseEnd_3117205 : Nat := 1600624463598581654801741

theorem tailTrace_3117205 : CollatzResearch.WordTrace tailWord_3117205 prefixEnd_3117205 1600624463598581654801741 := by
  unfold tailWord_3117205
  simp only [CollatzResearch.WordTrace]
  refine ⟨113693806671906136074473069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75795871114604090716315379 113693806671906136074473069)
  ·
    refine ⟨42635177501964801027927401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113693806671906136074473069 42635177501964801027927401)
    ·
      refine ⟨31976383126473600770945551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42635177501964801027927401 31976383126473600770945551)
      ·
        refine ⟨47964574689710401156418327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31976383126473600770945551 47964574689710401156418327)
        ·
          refine ⟨71946862034565601734627491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47964574689710401156418327 71946862034565601734627491)
          ·
            refine ⟨107920293051848402601941237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71946862034565601734627491 107920293051848402601941237)
            ·
              refine ⟨10117527473610787743931991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107920293051848402601941237 10117527473610787743931991)
              ·
                refine ⟨15176291210416181615897987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10117527473610787743931991 15176291210416181615897987)
                ·
                  refine ⟨22764436815624272423846981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15176291210416181615897987 22764436815624272423846981)
                  ·
                    refine ⟨4268331902929551079471309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22764436815624272423846981 4268331902929551079471309)
                    ·
                      refine ⟨1600624463598581654801741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4268331902929551079471309 1600624463598581654801741)
                      ·
                        rfl

theorem cell23_3117205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_3117205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117205 prefixEnd_3117205 := by exact prefixLift 3117205
  have htrace : WordTrace (prefixWord ++ tailWord_3117205) baseStart_3117205 baseEnd_3117205 := by
    simpa [prefixWord, tailWord_3117205, baseEnd_3117205] using wordTrace_append hprefix tailTrace_3117205
  have hstable : (prefixWord ++ tailWord_3117205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117205).length < 2 ^ (prefixWord ++ tailWord_3117205).sum := by decide
  have hdescent : baseEnd_3117205 < baseStart_3117205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117215 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3117215 : Nat := 118140960795 + 3117215 * 2 ^ 59
def prefixEnd_3117215 : Nat := 4983230072969 + 3 ^ 40 * 3117215 * 2
def baseEnd_3117215 : Nat := 1600629598405126615676695

theorem tailTrace_3117215 : CollatzResearch.WordTrace tailWord_3117215 prefixEnd_3117215 1600629598405126615676695 := by
  unfold tailWord_3117215
  simp only [CollatzResearch.WordTrace]
  refine ⟨113694171401869907782337099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75796114267913271854891399 113694171401869907782337099)
  ·
    refine ⟨170541257102804861673505649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113694171401869907782337099 170541257102804861673505649)
    ·
      refine ⟨127905942827103646255129237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170541257102804861673505649 127905942827103646255129237)
      ·
        refine ⟨5995591070020483418209183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127905942827103646255129237 5995591070020483418209183)
        ·
          refine ⟨8993386605030725127313775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995591070020483418209183 8993386605030725127313775)
          ·
            refine ⟨13490079907546087690970663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8993386605030725127313775 13490079907546087690970663)
            ·
              refine ⟨20235119861319131536455995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13490079907546087690970663 20235119861319131536455995)
              ·
                refine ⟨30352679791978697304683993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20235119861319131536455995 30352679791978697304683993)
                ·
                  refine ⟨22764509843984022978512995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30352679791978697304683993 22764509843984022978512995)
                  ·
                    refine ⟨34146764765976034467769493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22764509843984022978512995 34146764765976034467769493)
                    ·
                      refine ⟨1600629598405126615676695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34146764765976034467769493 1600629598405126615676695)
                      ·
                        rfl

theorem cell23_3117215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3117215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117215 prefixEnd_3117215 := by exact prefixLift 3117215
  have htrace : WordTrace (prefixWord ++ tailWord_3117215) baseStart_3117215 baseEnd_3117215 := by
    simpa [prefixWord, tailWord_3117215, baseEnd_3117215] using wordTrace_append hprefix tailTrace_3117215
  have hstable : (prefixWord ++ tailWord_3117215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117215).length < 2 ^ (prefixWord ++ tailWord_3117215).sum := by decide
  have hdescent : baseEnd_3117215 < baseStart_3117215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117229 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3117229 : Nat := 118140960795 + 3117229 * 2 ^ 59
def prefixEnd_3117229 : Nat := 4983230072969 + 3 ^ 40 * 3117229 * 2
def baseEnd_3117229 : Nat := 533545595711429853633877

theorem tailTrace_3117229 : CollatzResearch.WordTrace tailWord_3117229 prefixEnd_3117229 533545595711429853633877 := by
  unfold tailWord_3117229
  simp only [CollatzResearch.WordTrace]
  refine ⟨113694682023819188173346741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75796454682546125448897827 113694682023819188173346741)
  ·
    refine ⟨10658876439733048891251257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113694682023819188173346741 10658876439733048891251257)
    ·
      refine ⟨7994157329799786668438443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10658876439733048891251257 7994157329799786668438443)
      ·
        refine ⟨11991235994699680002657665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7994157329799786668438443 11991235994699680002657665)
        ·
          refine ⟨8993426996024760001993249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11991235994699680002657665 8993426996024760001993249)
          ·
            refine ⟨6745070247018570001494937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8993426996024760001993249 6745070247018570001494937)
            ·
              refine ⟨5058802685263927501121203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6745070247018570001494937 5058802685263927501121203)
              ·
                refine ⟨7588204027895891251681805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5058802685263927501121203 7588204027895891251681805)
                ·
                  refine ⟨2845576510460959219380677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7588204027895891251681805 2845576510460959219380677)
                  ·
                    refine ⟨533545595711429853633877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2845576510460959219380677 533545595711429853633877)
                    ·
                      rfl

theorem cell23_3117229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3117229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117229 prefixEnd_3117229 := by exact prefixLift 3117229
  have htrace : WordTrace (prefixWord ++ tailWord_3117229) baseStart_3117229 baseEnd_3117229 := by
    simpa [prefixWord, tailWord_3117229, baseEnd_3117229] using wordTrace_append hprefix tailTrace_3117229
  have hstable : (prefixWord ++ tailWord_3117229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117229).length < 2 ^ (prefixWord ++ tailWord_3117229).sum := by decide
  have hdescent : baseEnd_3117229 < baseStart_3117229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117272 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 1, 5]
def baseStart_3117272 : Nat := 118140960795 + 3117272 * 2 ^ 59
def prefixEnd_3117272 : Nat := 4983230072969 + 3 ^ 40 * 3117272 * 2
def baseEnd_3117272 : Nat := 533552955600810964221311

theorem tailTrace_3117272 : CollatzResearch.WordTrace tailWord_3117272 prefixEnd_3117272 533552955600810964221311 := by
  unfold tailWord_3117272
  simp only [CollatzResearch.WordTrace]
  refine ⟨56848125181331703258581035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75797500241775604344774713 56848125181331703258581035)
  ·
    refine ⟨85272187771997554887871553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56848125181331703258581035 85272187771997554887871553)
    ·
      refine ⟨63954140828998166165903665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85272187771997554887871553 63954140828998166165903665)
      ·
        refine ⟨47965605621748624624427749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63954140828998166165903665 47965605621748624624427749)
        ·
          refine ⟨8993551054077867117080203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47965605621748624624427749 8993551054077867117080203)
          ·
            refine ⟨13490326581116800675620305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8993551054077867117080203 13490326581116800675620305)
            ·
              refine ⟨10117744935837600506715229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13490326581116800675620305 10117744935837600506715229)
              ·
                refine ⟨3794154350939100190018211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10117744935837600506715229 3794154350939100190018211)
                ·
                  refine ⟨5691231526408650285027317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794154350939100190018211 5691231526408650285027317)
                  ·
                    refine ⟨533552955600810964221311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5691231526408650285027317 533552955600810964221311)
                    ·
                      rfl

theorem cell23_3117272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_3117272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117272 prefixEnd_3117272 := by exact prefixLift 3117272
  have htrace : WordTrace (prefixWord ++ tailWord_3117272) baseStart_3117272 baseEnd_3117272 := by
    simpa [prefixWord, tailWord_3117272, baseEnd_3117272] using wordTrace_append hprefix tailTrace_3117272
  have hstable : (prefixWord ++ tailWord_3117272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117272).length < 2 ^ (prefixWord ++ tailWord_3117272).sum := by decide
  have hdescent : baseEnd_3117272 < baseStart_3117272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117309 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 3, 2, 2]
def baseStart_3117309 : Nat := 118140960795 + 3117309 * 2 ^ 59
def prefixEnd_3117309 : Nat := 4983230072969 + 3 ^ 40 * 3117309 * 2
def baseEnd_3117309 : Nat := 1600677865586649247901263

theorem tailTrace_3117309 : CollatzResearch.WordTrace tailWord_3117309 prefixEnd_3117309 1600677865586649247901263 := by
  unfold tailWord_3117309
  simp only [CollatzResearch.WordTrace]
  refine ⟨113697599863529361836258981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75798399909019574557505987 113697599863529361836258981)
  ·
    refine ⟨21318299974411755344298559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113697599863529361836258981 21318299974411755344298559)
    ·
      refine ⟨31977449961617633016447839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21318299974411755344298559 31977449961617633016447839)
      ·
        refine ⟨47966174942426449524671759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31977449961617633016447839 47966174942426449524671759)
        ·
          refine ⟨71949262413639674287007639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47966174942426449524671759 71949262413639674287007639)
          ·
            refine ⟨107923893620459511430511459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71949262413639674287007639 107923893620459511430511459)
            ·
              refine ⟨161885840430689267145767189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107923893620459511430511459 161885840430689267145767189)
              ·
                refine ⟨7588398770188559397457837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161885840430689267145767189 7588398770188559397457837)
                ·
                  refine ⟨2845649538820709774046689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7588398770188559397457837 2845649538820709774046689)
                  ·
                    refine ⟨2134237154115532330535017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2845649538820709774046689 2134237154115532330535017)
                    ·
                      refine ⟨1600677865586649247901263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134237154115532330535017 1600677865586649247901263)
                      ·
                        rfl

theorem cell23_3117309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_3117309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117309 prefixEnd_3117309 := by exact prefixLift 3117309
  have htrace : WordTrace (prefixWord ++ tailWord_3117309) baseStart_3117309 baseEnd_3117309 := by
    simpa [prefixWord, tailWord_3117309, baseEnd_3117309] using wordTrace_append hprefix tailTrace_3117309
  have hstable : (prefixWord ++ tailWord_3117309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117309).length < 2 ^ (prefixWord ++ tailWord_3117309).sum := by decide
  have hdescent : baseEnd_3117309 < baseStart_3117309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117319 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 1, 6]
def baseStart_3117319 : Nat := 118140960795 + 3117319 * 2 ^ 59
def prefixEnd_3117319 : Nat := 4983230072969 + 3 ^ 40 * 3117319 * 2
def baseEnd_3117319 : Nat := 533561000131064736258739

theorem tailTrace_3117319 : CollatzResearch.WordTrace tailWord_3117319 prefixEnd_3117319 533561000131064736258739 := by
  unfold tailWord_3117319
  simp only [CollatzResearch.WordTrace]
  refine ⟨113697964593493133544123011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75798643062328755696082007 113697964593493133544123011)
  ·
    refine ⟨170546946890239700316184517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113697964593493133544123011 170546946890239700316184517)
    ·
      refine ⟨31977552541919943809284597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170546946890239700316184517 31977552541919943809284597)
      ·
        refine ⟨2997895550804994732120431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31977552541919943809284597 2997895550804994732120431)
        ·
          refine ⟨4496843326207492098180647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2997895550804994732120431 4496843326207492098180647)
          ·
            refine ⟨6745264989311238147270971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496843326207492098180647 6745264989311238147270971)
            ·
              refine ⟨10117897483966857220906457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6745264989311238147270971 10117897483966857220906457)
              ·
                refine ⟨7588423112975142915679843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10117897483966857220906457 7588423112975142915679843)
                ·
                  refine ⟨11382634669462714373519765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7588423112975142915679843 11382634669462714373519765)
                  ·
                    refine ⟨533561000131064736258739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11382634669462714373519765 533561000131064736258739)
                    ·
                      rfl

theorem cell23_3117319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_3117319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117319 prefixEnd_3117319 := by exact prefixLift 3117319
  have htrace : WordTrace (prefixWord ++ tailWord_3117319) baseStart_3117319 baseEnd_3117319 := by
    simpa [prefixWord, tailWord_3117319, baseEnd_3117319] using wordTrace_append hprefix tailTrace_3117319
  have hstable : (prefixWord ++ tailWord_3117319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117319).length < 2 ^ (prefixWord ++ tailWord_3117319).sum := by decide
  have hdescent : baseEnd_3117319 < baseStart_3117319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117343 : List Nat := [1, 1, 2, 4, 3, 2, 1, 4, 1, 2, 2]
def baseStart_3117343 : Nat := 118140960795 + 3117343 * 2 ^ 59
def prefixEnd_3117343 : Nat := 4983230072969 + 3 ^ 40 * 3117343 * 2
def baseEnd_3117343 : Nat := 1600695323928902114876107

theorem tailTrace_3117343 : CollatzResearch.WordTrace tailWord_3117343 prefixEnd_3117343 1600695323928902114876107 := by
  unfold tailWord_3117343
  simp only [CollatzResearch.WordTrace]
  refine ⟨113698839945406185642996683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75799226630270790428664455 113698839945406185642996683)
  ·
    refine ⟨170548259918109278464495025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113698839945406185642996683 170548259918109278464495025)
    ·
      refine ⟨127911194938581958848371269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170548259918109278464495025 127911194938581958848371269)
      ·
        refine ⟨23983349050984117284069613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127911194938581958848371269 23983349050984117284069613)
        ·
          refine ⟨8993755894119043981526105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23983349050984117284069613 8993755894119043981526105)
          ·
            refine ⟨6745316920589282986144579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8993755894119043981526105 6745316920589282986144579)
            ·
              refine ⟨10117975380883924479216869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6745316920589282986144579 10117975380883924479216869)
              ·
                refine ⟨1897120383915735839853163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10117975380883924479216869 1897120383915735839853163)
                ·
                  refine ⟨2845680575873603759779745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897120383915735839853163 2845680575873603759779745)
                  ·
                    refine ⟨2134260431905202819834809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2845680575873603759779745 2134260431905202819834809)
                    ·
                      refine ⟨1600695323928902114876107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134260431905202819834809 1600695323928902114876107)
                      ·
                        rfl

theorem cell23_3117343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_3117343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117343 prefixEnd_3117343 := by exact prefixLift 3117343
  have htrace : WordTrace (prefixWord ++ tailWord_3117343) baseStart_3117343 baseEnd_3117343 := by
    simpa [prefixWord, tailWord_3117343, baseEnd_3117343] using wordTrace_append hprefix tailTrace_3117343
  have hstable : (prefixWord ++ tailWord_3117343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117343).length < 2 ^ (prefixWord ++ tailWord_3117343).sum := by decide
  have hdescent : baseEnd_3117343 < baseStart_3117343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117345 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 2, 7]
def baseStart_3117345 : Nat := 118140960795 + 3117345 * 2 ^ 59
def prefixEnd_3117345 : Nat := 4983230072969 + 3 ^ 40 * 3117345 * 2
def baseEnd_3117345 : Nat := 533565450296737035683699

theorem tailTrace_3117345 : CollatzResearch.WordTrace tailWord_3117345 prefixEnd_3117345 533565450296737035683699 := by
  unfold tailWord_3117345
  simp only [CollatzResearch.WordTrace]
  refine ⟨113698912891398939984569489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75799275260932626656379659 113698912891398939984569489)
  ·
    refine ⟨85274184668549204988427117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113698912891398939984569489 85274184668549204988427117)
    ·
      refine ⟨31977819250705951870660169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85274184668549204988427117 31977819250705951870660169)
      ·
        refine ⟨23983364438029463902995127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31977819250705951870660169 23983364438029463902995127)
        ·
          refine ⟨35975046657044195854492691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23983364438029463902995127 35975046657044195854492691)
          ·
            refine ⟨53962569985566293781739037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35975046657044195854492691 53962569985566293781739037)
            ·
              refine ⟨20235963744587360168152139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53962569985566293781739037 20235963744587360168152139)
              ·
                refine ⟨30353945616881040252228209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20235963744587360168152139 30353945616881040252228209)
                ·
                  refine ⟨22765459212660780189171157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30353945616881040252228209 22765459212660780189171157)
                  ·
                    refine ⟨533565450296737035683699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22765459212660780189171157 533565450296737035683699)
                    ·
                      rfl

theorem cell23_3117345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_3117345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117345 prefixEnd_3117345 := by exact prefixLift 3117345
  have htrace : WordTrace (prefixWord ++ tailWord_3117345) baseStart_3117345 baseEnd_3117345 := by
    simpa [prefixWord, tailWord_3117345, baseEnd_3117345] using wordTrace_append hprefix tailTrace_3117345
  have hstable : (prefixWord ++ tailWord_3117345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117345).length < 2 ^ (prefixWord ++ tailWord_3117345).sum := by decide
  have hdescent : baseEnd_3117345 < baseStart_3117345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117349 : List Nat := [1, 3, 1, 2, 6, 1, 1, 8]
def baseStart_3117349 : Nat := 118140960795 + 3117349 * 2 ^ 59
def prefixEnd_3117349 : Nat := 4983230072969 + 3 ^ 40 * 3117349 * 2
def baseEnd_3117349 : Nat := 59285126104178855237077

theorem tailTrace_3117349 : CollatzResearch.WordTrace tailWord_3117349 prefixEnd_3117349 59285126104178855237077 := by
  unfold tailWord_3117349
  simp only [CollatzResearch.WordTrace]
  refine ⟨113699058783384448667715101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75799372522256299111810067 113699058783384448667715101)
  ·
    refine ⟨42637147043769168250393163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113699058783384448667715101 42637147043769168250393163)
    ·
      refine ⟨63955720565653752375589745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42637147043769168250393163 63955720565653752375589745)
      ·
        refine ⟨47966790424240314281692309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63955720565653752375589745 47966790424240314281692309)
        ·
          refine ⟨2248443301136264731954327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47966790424240314281692309 2248443301136264731954327)
          ·
            refine ⟨3372664951704397097931491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248443301136264731954327 3372664951704397097931491)
            ·
              refine ⟨5058997427556595646897237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372664951704397097931491 5058997427556595646897237)
              ·
                refine ⟨59285126104178855237077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5058997427556595646897237 59285126104178855237077)
                ·
                  rfl

theorem cell23_3117349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 8].length) (baseStart_3117349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117349 prefixEnd_3117349 := by exact prefixLift 3117349
  have htrace : WordTrace (prefixWord ++ tailWord_3117349) baseStart_3117349 baseEnd_3117349 := by
    simpa [prefixWord, tailWord_3117349, baseEnd_3117349] using wordTrace_append hprefix tailTrace_3117349
  have hstable : (prefixWord ++ tailWord_3117349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117349).length < 2 ^ (prefixWord ++ tailWord_3117349).sum := by decide
  have hdescent : baseEnd_3117349 < baseStart_3117349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117359 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 2, 1, 3]
def baseStart_3117359 : Nat := 118140960795 + 3117359 * 2 ^ 59
def prefixEnd_3117359 : Nat := 4983230072969 + 3 ^ 40 * 3117359 * 2
def baseEnd_3117359 : Nat := 1600703539619374052276033

theorem tailTrace_3117359 : CollatzResearch.WordTrace tailWord_3117359 prefixEnd_3117359 1600703539619374052276033 := by
  unfold tailWord_3117359
  simp only [CollatzResearch.WordTrace]
  refine ⟨113699423513348220375579131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75799615675565480250386087 113699423513348220375579131)
  ·
    refine ⟨170549135270022330563368697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113699423513348220375579131 170549135270022330563368697)
    ·
      refine ⟨127911851452516747922526523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170549135270022330563368697 127911851452516747922526523)
      ·
        refine ⟨191867777178775121883789785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127911851452516747922526523 191867777178775121883789785)
        ·
          refine ⟨143900832884081341412842339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191867777178775121883789785 143900832884081341412842339)
          ·
            refine ⟨215851249326122012119263509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143900832884081341412842339 215851249326122012119263509)
            ·
              refine ⟨10118027312161969318090477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 215851249326122012119263509 10118027312161969318090477)
              ·
                refine ⟨3794260242060738494283929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10118027312161969318090477 3794260242060738494283929)
                ·
                  refine ⟨2845695181545553870712947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3794260242060738494283929 2845695181545553870712947)
                  ·
                    refine ⟨4268542772318330806069421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2845695181545553870712947 4268542772318330806069421)
                    ·
                      refine ⟨1600703539619374052276033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4268542772318330806069421 1600703539619374052276033)
                      ·
                        rfl

theorem cell23_3117359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 1, 3].length) (baseStart_3117359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117359 prefixEnd_3117359 := by exact prefixLift 3117359
  have htrace : WordTrace (prefixWord ++ tailWord_3117359) baseStart_3117359 baseEnd_3117359 := by
    simpa [prefixWord, tailWord_3117359, baseEnd_3117359] using wordTrace_append hprefix tailTrace_3117359
  have hstable : (prefixWord ++ tailWord_3117359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117359).length < 2 ^ (prefixWord ++ tailWord_3117359).sum := by decide
  have hdescent : baseEnd_3117359 < baseStart_3117359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117375 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 1, 8]
def baseStart_3117375 : Nat := 118140960795 + 3117375 * 2 ^ 59
def prefixEnd_3117375 : Nat := 4983230072969 + 3 ^ 40 * 3117375 * 2
def baseEnd_3117375 : Nat := 533570585103281996558653

theorem tailTrace_3117375 : CollatzResearch.WordTrace tailWord_3117375 prefixEnd_3117375 533570585103281996558653 := by
  unfold tailWord_3117375
  simp only [CollatzResearch.WordTrace]
  refine ⟨113700007081290255108161579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75800004720860170072107719 113700007081290255108161579)
  ·
    refine ⟨170550010621935382662242369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113700007081290255108161579 170550010621935382662242369)
    ·
      refine ⟨127912507966451536996681777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170550010621935382662242369 127912507966451536996681777)
      ·
        refine ⟨95934380974838652747511333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127912507966451536996681777 95934380974838652747511333)
        ·
          refine ⟨17987696432782247390158375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95934380974838652747511333 17987696432782247390158375)
          ·
            refine ⟨26981544649173371085237563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17987696432782247390158375 26981544649173371085237563)
            ·
              refine ⟨40472316973760056627856345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26981544649173371085237563 40472316973760056627856345)
              ·
                refine ⟨30354237730320042470892259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40472316973760056627856345 30354237730320042470892259)
                ·
                  refine ⟨45531356595480063706338389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30354237730320042470892259 45531356595480063706338389)
                  ·
                    refine ⟨533570585103281996558653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45531356595480063706338389 533570585103281996558653)
                    ·
                      rfl

theorem cell23_3117375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_3117375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117375 prefixEnd_3117375 := by exact prefixLift 3117375
  have htrace : WordTrace (prefixWord ++ tailWord_3117375) baseStart_3117375 baseEnd_3117375 := by
    simpa [prefixWord, tailWord_3117375, baseEnd_3117375] using wordTrace_append hprefix tailTrace_3117375
  have hstable : (prefixWord ++ tailWord_3117375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117375).length < 2 ^ (prefixWord ++ tailWord_3117375).sum := by decide
  have hdescent : baseEnd_3117375 < baseStart_3117375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117380 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_3117380 : Nat := 118140960795 + 3117380 * 2 ^ 59
def prefixEnd_3117380 : Nat := 4983230072969 + 3 ^ 40 * 3117380 * 2
def baseEnd_3117380 : Nat := 1600714322713118470113437

theorem tailTrace_3117380 : CollatzResearch.WordTrace tailWord_3117380 prefixEnd_3117380 1600714322713118470113437 := by
  unfold tailWord_3117380
  simp only [CollatzResearch.WordTrace]
  refine ⟨56850094723136070481046797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75800126297514760641395729 56850094723136070481046797)
  ·
    refine ⟨21318785521176026430392549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56850094723136070481046797 21318785521176026430392549)
    ·
      refine ⟨3997272285220504955698603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21318785521176026430392549 3997272285220504955698603)
      ·
        refine ⟨5995908427830757433547905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997272285220504955698603 5995908427830757433547905)
        ·
          refine ⟨4496931320873068075160929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5995908427830757433547905 4496931320873068075160929)
          ·
            refine ⟨3372698490654801056370697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4496931320873068075160929 3372698490654801056370697)
            ·
              refine ⟨2529523867991100792278023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372698490654801056370697 2529523867991100792278023)
              ·
                refine ⟨3794285801986651188417035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529523867991100792278023 3794285801986651188417035)
                ·
                  refine ⟨5691428702979976782625553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794285801986651188417035 5691428702979976782625553)
                  ·
                    refine ⟨4268571527234982586969165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5691428702979976782625553 4268571527234982586969165)
                    ·
                      refine ⟨1600714322713118470113437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4268571527234982586969165 1600714322713118470113437)
                      ·
                        rfl

theorem cell23_3117380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_3117380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117380 prefixEnd_3117380 := by exact prefixLift 3117380
  have htrace : WordTrace (prefixWord ++ tailWord_3117380) baseStart_3117380 baseEnd_3117380 := by
    simpa [prefixWord, tailWord_3117380, baseEnd_3117380] using wordTrace_append hprefix tailTrace_3117380
  have hstable : (prefixWord ++ tailWord_3117380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117380).length < 2 ^ (prefixWord ++ tailWord_3117380).sum := by decide
  have hdescent : baseEnd_3117380 < baseStart_3117380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117385 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_3117385 : Nat := 118140960795 + 3117385 * 2 ^ 59
def prefixEnd_3117385 : Nat := 4983230072969 + 3 ^ 40 * 3117385 * 2
def baseEnd_3117385 : Nat := 1600716890116390950550913

theorem tailTrace_3117385 : CollatzResearch.WordTrace tailWord_3117385 prefixEnd_3117385 1600716890116390950550913 := by
  unfold tailWord_3117385
  simp only [CollatzResearch.WordTrace]
  refine ⟨113700371811254026816025609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75800247874169351210683739 113700371811254026816025609)
  ·
    refine ⟨85275278858440520112019207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113700371811254026816025609 85275278858440520112019207)
    ·
      refine ⟨127912918287660780168028811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85275278858440520112019207 127912918287660780168028811)
      ·
        refine ⟨191869377431491170252043217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127912918287660780168028811 191869377431491170252043217)
        ·
          refine ⟨143902033073618377689032413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191869377431491170252043217 143902033073618377689032413)
          ·
            refine ⟨53963262402606891633387155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143902033073618377689032413 53963262402606891633387155)
            ·
              refine ⟨80944893603910337450080733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53963262402606891633387155 80944893603910337450080733)
              ·
                refine ⟨30354335101466376543780275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80944893603910337450080733 30354335101466376543780275)
                ·
                  refine ⟨45531502652199564815670413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30354335101466376543780275 45531502652199564815670413)
                  ·
                    refine ⟨17074313494574836805876405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45531502652199564815670413 17074313494574836805876405)
                    ·
                      refine ⟨1600716890116390950550913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17074313494574836805876405 1600716890116390950550913)
                      ·
                        rfl

theorem cell23_3117385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_3117385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117385 prefixEnd_3117385 := by exact prefixLift 3117385
  have htrace : WordTrace (prefixWord ++ tailWord_3117385) baseStart_3117385 baseEnd_3117385 := by
    simpa [prefixWord, tailWord_3117385, baseEnd_3117385] using wordTrace_append hprefix tailTrace_3117385
  have hstable : (prefixWord ++ tailWord_3117385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117385).length < 2 ^ (prefixWord ++ tailWord_3117385).sum := by decide
  have hdescent : baseEnd_3117385 < baseStart_3117385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117412 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_3117412 : Nat := 118140960795 + 3117412 * 2 ^ 59
def prefixEnd_3117412 : Nat := 4983230072969 + 3 ^ 40 * 3117412 * 2
def baseEnd_3117412 : Nat := 1600730754094062344913289

theorem tailTrace_3117412 : CollatzResearch.WordTrace tailWord_3117412 prefixEnd_3117412 1600730754094062344913289 := by
  unfold tailWord_3117412
  simp only [CollatzResearch.WordTrace]
  refine ⟨56850678291078105213629245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75800904388104140284838993 56850678291078105213629245)
  ·
    refine ⟨21319004359154289455110967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56850678291078105213629245 21319004359154289455110967)
    ·
      refine ⟨31978506538731434182666451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21319004359154289455110967 31978506538731434182666451)
      ·
        refine ⟨47967759808097151273999677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31978506538731434182666451 47967759808097151273999677)
        ·
          refine ⟨17987909928036431727749879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47967759808097151273999677 17987909928036431727749879)
          ·
            refine ⟨26981864892054647591624819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17987909928036431727749879 26981864892054647591624819)
            ·
              refine ⟨40472797338081971387437229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26981864892054647591624819 40472797338081971387437229)
              ·
                refine ⟨15177299001780739270288961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40472797338081971387437229 15177299001780739270288961)
                ·
                  refine ⟨11382974251335554452716721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15177299001780739270288961 11382974251335554452716721)
                  ·
                    refine ⟨8537230688501665839537541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11382974251335554452716721 8537230688501665839537541)
                    ·
                      refine ⟨1600730754094062344913289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8537230688501665839537541 1600730754094062344913289)
                      ·
                        rfl

theorem cell23_3117412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_3117412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117412 prefixEnd_3117412 := by exact prefixLift 3117412
  have htrace : WordTrace (prefixWord ++ tailWord_3117412) baseStart_3117412 baseEnd_3117412 := by
    simpa [prefixWord, tailWord_3117412, baseEnd_3117412] using wordTrace_append hprefix tailTrace_3117412
  have hstable : (prefixWord ++ tailWord_3117412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117412).length < 2 ^ (prefixWord ++ tailWord_3117412).sum := by decide
  have hdescent : baseEnd_3117412 < baseStart_3117412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117416 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_3117416 : Nat := 118140960795 + 3117416 * 2 ^ 59
def prefixEnd_3117416 : Nat := 4983230072969 + 3 ^ 40 * 3117416 * 2
def baseEnd_3117416 : Nat := 1600732808016680329263271

theorem tailTrace_3117416 : CollatzResearch.WordTrace tailWord_3117416 prefixEnd_3117416 1600732808016680329263271 := by
  unfold tailWord_3117416
  simp only [CollatzResearch.WordTrace]
  refine ⟨56850751237070859555202051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75801001649427812740269401 56850751237070859555202051)
  ·
    refine ⟨85276126855606289332803077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56850751237070859555202051 85276126855606289332803077)
    ·
      refine ⟨15989273785426179249900577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85276126855606289332803077 15989273785426179249900577)
      ·
        refine ⟨11991955339069634437425433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15989273785426179249900577 11991955339069634437425433)
        ·
          refine ⟨8993966504302225828069075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11991955339069634437425433 8993966504302225828069075)
          ·
            refine ⟨13490949756453338742103613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8993966504302225828069075 13490949756453338742103613)
            ·
              refine ⟨5059106158670002028288855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13490949756453338742103613 5059106158670002028288855)
              ·
                refine ⟨7588659238005003042433283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059106158670002028288855 7588659238005003042433283)
                ·
                  refine ⟨11382988857007504563649925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7588659238005003042433283 11382988857007504563649925)
                  ·
                    refine ⟨2134310410688907105684361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11382988857007504563649925 2134310410688907105684361)
                    ·
                      refine ⟨1600732808016680329263271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134310410688907105684361 1600732808016680329263271)
                      ·
                        rfl

theorem cell23_3117416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_3117416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117416 prefixEnd_3117416 := by exact prefixLift 3117416
  have htrace : WordTrace (prefixWord ++ tailWord_3117416) baseStart_3117416 baseEnd_3117416 := by
    simpa [prefixWord, tailWord_3117416, baseEnd_3117416] using wordTrace_append hprefix tailTrace_3117416
  have hstable : (prefixWord ++ tailWord_3117416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117416).length < 2 ^ (prefixWord ++ tailWord_3117416).sum := by decide
  have hdescent : baseEnd_3117416 < baseStart_3117416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117452 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_3117452 : Nat := 118140960795 + 3117452 * 2 ^ 59
def prefixEnd_3117452 : Nat := 4983230072969 + 3 ^ 40 * 3117452 * 2
def baseEnd_3117452 : Nat := 533583764440080729471035

theorem tailTrace_3117452 : CollatzResearch.WordTrace tailWord_3117452 prefixEnd_3117452 533583764440080729471035 := by
  unfold tailWord_3117452
  simp only [CollatzResearch.WordTrace]
  refine ⟨56851407751005648629357305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75801877001340864839143073 56851407751005648629357305)
  ·
    refine ⟨42638555813254236472017979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56851407751005648629357305 42638555813254236472017979)
    ·
      refine ⟨63957833719881354708026969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42638555813254236472017979 63957833719881354708026969)
      ·
        refine ⟨47968375289911016031020227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63957833719881354708026969 47968375289911016031020227)
        ·
          refine ⟨71952562934866524046530341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47968375289911016031020227 71952562934866524046530341)
          ·
            refine ⟨13491105550287473258724439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71952562934866524046530341 13491105550287473258724439)
            ·
              refine ⟨20236658325431209888086659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13491105550287473258724439 20236658325431209888086659)
              ·
                refine ⟨30354987488146814832129989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20236658325431209888086659 30354987488146814832129989)
                ·
                  refine ⟨5691560154027527781024373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30354987488146814832129989 5691560154027527781024373)
                  ·
                    refine ⟨533583764440080729471035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5691560154027527781024373 533583764440080729471035)
                    ·
                      rfl

theorem cell23_3117452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_3117452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117452 prefixEnd_3117452 := by exact prefixLift 3117452
  have htrace : WordTrace (prefixWord ++ tailWord_3117452) baseStart_3117452 baseEnd_3117452 := by
    simpa [prefixWord, tailWord_3117452, baseEnd_3117452] using wordTrace_append hprefix tailTrace_3117452
  have hstable : (prefixWord ++ tailWord_3117452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117452).length < 2 ^ (prefixWord ++ tailWord_3117452).sum := by decide
  have hdescent : baseEnd_3117452 < baseStart_3117452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117489 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3117489 : Nat := 118140960795 + 3117489 * 2 ^ 59
def prefixEnd_3117489 : Nat := 4983230072969 + 3 ^ 40 * 3117489 * 2
def baseEnd_3117489 : Nat := 1600770292104458543650435

theorem tailTrace_3117489 : CollatzResearch.WordTrace tailWord_3117489 prefixEnd_3117489 1600770292104458543650435 := by
  unfold tailWord_3117489
  simp only [CollatzResearch.WordTrace]
  refine ⟨113704165002877252577811521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75802776668584835051874347 113704165002877252577811521)
  ·
    refine ⟨85278123752157939433358641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113704165002877252577811521 85278123752157939433358641)
    ·
      refine ⟨63958592814118454575018981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85278123752157939433358641 63958592814118454575018981)
      ·
        refine ⟨11992236152647210232816059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63958592814118454575018981 11992236152647210232816059)
        ·
          refine ⟨17988354228970815349224089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11992236152647210232816059 17988354228970815349224089)
          ·
            refine ⟨13491265671728111511918067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17988354228970815349224089 13491265671728111511918067)
            ·
              refine ⟨20236898507592167267877101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13491265671728111511918067 20236898507592167267877101)
              ·
                refine ⟨7588836940347062725453913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20236898507592167267877101 7588836940347062725453913)
                ·
                  refine ⟨5691627705260297044090435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7588836940347062725453913 5691627705260297044090435)
                  ·
                    refine ⟨8537441557890445566135653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5691627705260297044090435 8537441557890445566135653)
                    ·
                      refine ⟨1600770292104458543650435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8537441557890445566135653 1600770292104458543650435)
                      ·
                        rfl

theorem cell23_3117489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3117489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117489 prefixEnd_3117489 := by exact prefixLift 3117489
  have htrace : WordTrace (prefixWord ++ tailWord_3117489) baseStart_3117489 baseEnd_3117489 := by
    simpa [prefixWord, tailWord_3117489, baseEnd_3117489] using wordTrace_append hprefix tailTrace_3117489
  have hstable : (prefixWord ++ tailWord_3117489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117489).length < 2 ^ (prefixWord ++ tailWord_3117489).sum := by decide
  have hdescent : baseEnd_3117489 < baseStart_3117489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117526 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_3117526 : Nat := 118140960795 + 3117526 * 2 ^ 59
def prefixEnd_3117526 : Nat := 4983230072969 + 3 ^ 40 * 3117526 * 2
def baseEnd_3117526 : Nat := 1600789290888674898887765

theorem tailTrace_3117526 : CollatzResearch.WordTrace tailWord_3117526 prefixEnd_3117526 1600789290888674898887765 := by
  unfold tailWord_3117526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7106594656483950493556777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75803676335828805264605621 7106594656483950493556777)
  ·
    refine ⟨5329945992362962870167583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7106594656483950493556777 5329945992362962870167583)
    ·
      refine ⟨7994918988544444305251375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5329945992362962870167583 7994918988544444305251375)
      ·
        refine ⟨11992378482816666457877063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7994918988544444305251375 11992378482816666457877063)
        ·
          refine ⟨17988567724224999686815595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11992378482816666457877063 17988567724224999686815595)
          ·
            refine ⟨26982851586337499530223393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17988567724224999686815595 26982851586337499530223393)
            ·
              refine ⟨20237138689753124647667545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26982851586337499530223393 20237138689753124647667545)
              ·
                refine ⟨15177854017314843485750659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20237138689753124647667545 15177854017314843485750659)
                ·
                  refine ⟨22766781025972265228625989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15177854017314843485750659 22766781025972265228625989)
                  ·
                    refine ⟨4268771442369799730367373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22766781025972265228625989 4268771442369799730367373)
                    ·
                      refine ⟨1600789290888674898887765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4268771442369799730367373 1600789290888674898887765)
                      ·
                        rfl

theorem cell23_3117526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_3117526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117526 prefixEnd_3117526 := by exact prefixLift 3117526
  have htrace : WordTrace (prefixWord ++ tailWord_3117526) baseStart_3117526 baseEnd_3117526 := by
    simpa [prefixWord, tailWord_3117526, baseEnd_3117526] using wordTrace_append hprefix tailTrace_3117526
  have hstable : (prefixWord ++ tailWord_3117526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117526).length < 2 ^ (prefixWord ++ tailWord_3117526).sum := by decide
  have hdescent : baseEnd_3117526 < baseStart_3117526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117573 : List Nat := [1, 3, 1, 1, 2, 2, 4, 4, 1, 1, 3]
def baseStart_3117573 : Nat := 118140960795 + 3117573 * 2 ^ 59
def prefixEnd_3117573 : Nat := 4983230072969 + 3 ^ 40 * 3117573 * 2
def baseEnd_3117573 : Nat := 1600813424479436215000049

theorem tailTrace_3117573 : CollatzResearch.WordTrace tailWord_3117573 prefixEnd_3117573 1600813424479436215000049 := by
  unfold tailWord_3117573
  simp only [CollatzResearch.WordTrace]
  refine ⟨113707228734572934923869373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75804819156381956615912915 113707228734572934923869373)
  ·
    refine ⟨42640210775464850596451015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113707228734572934923869373 42640210775464850596451015)
    ·
      refine ⟨63960316163197275894676523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42640210775464850596451015 63960316163197275894676523)
      ·
        refine ⟨95940474244795913842014785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63960316163197275894676523 95940474244795913842014785)
        ·
          refine ⟨71955355683596935381511089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95940474244795913842014785 71955355683596935381511089)
          ·
            refine ⟨53966516762697701536133317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71955355683596935381511089 53966516762697701536133317)
            ·
              refine ⟨10118721893005819038024997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53966516762697701536133317 10118721893005819038024997)
              ·
                refine ⟨1897260354938591069629687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10118721893005819038024997 1897260354938591069629687)
                ·
                  refine ⟨2845890532407886604444531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897260354938591069629687 2845890532407886604444531)
                  ·
                    refine ⟨4268835798611829906666797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2845890532407886604444531 4268835798611829906666797)
                    ·
                      refine ⟨1600813424479436215000049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4268835798611829906666797 1600813424479436215000049)
                      ·
                        rfl

theorem cell23_3117573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 1, 1, 3].length) (baseStart_3117573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117573 prefixEnd_3117573 := by exact prefixLift 3117573
  have htrace : WordTrace (prefixWord ++ tailWord_3117573) baseStart_3117573 baseEnd_3117573 := by
    simpa [prefixWord, tailWord_3117573, baseEnd_3117573] using wordTrace_append hprefix tailTrace_3117573
  have hstable : (prefixWord ++ tailWord_3117573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117573).length < 2 ^ (prefixWord ++ tailWord_3117573).sum := by decide
  have hdescent : baseEnd_3117573 < baseStart_3117573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117596 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_3117596 : Nat := 118140960795 + 3117596 * 2 ^ 59
def prefixEnd_3117596 : Nat := 4983230072969 + 3 ^ 40 * 3117596 * 2
def baseEnd_3117596 : Nat := 1600825234534489625012443

theorem tailTrace_3117596 : CollatzResearch.WordTrace tailWord_3117596 prefixEnd_3117596 1600825234534489625012443 := by
  unfold tailWord_3117596
  simp only [CollatzResearch.WordTrace]
  refine ⟨56854033806744804925978321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75805378408993073234637761 56854033806744804925978321)
  ·
    refine ⟨42640525355058603694483741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56854033806744804925978321 42640525355058603694483741)
    ·
      refine ⟨15990197008146976385431403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42640525355058603694483741 15990197008146976385431403)
      ·
        refine ⟨23985295512220464578147105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15990197008146976385431403 23985295512220464578147105)
        ·
          refine ⟨17988971634165348433610329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23985295512220464578147105 17988971634165348433610329)
          ·
            refine ⟨13491728725624011325207747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17988971634165348433610329 13491728725624011325207747)
            ·
              refine ⟨20237593088436016987811621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13491728725624011325207747 20237593088436016987811621)
              ·
                refine ⟨3794548704081753185214679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20237593088436016987811621 3794548704081753185214679)
                ·
                  refine ⟨5691823056122629777822019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794548704081753185214679 5691823056122629777822019)
                  ·
                    refine ⟨8537734584183944666733029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5691823056122629777822019 8537734584183944666733029)
                    ·
                      refine ⟨1600825234534489625012443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8537734584183944666733029 1600825234534489625012443)
                      ·
                        rfl

theorem cell23_3117596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_3117596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117596 prefixEnd_3117596 := by exact prefixLift 3117596
  have htrace : WordTrace (prefixWord ++ tailWord_3117596) baseStart_3117596 baseEnd_3117596 := by
    simpa [prefixWord, tailWord_3117596, baseEnd_3117596] using wordTrace_append hprefix tailTrace_3117596
  have hstable : (prefixWord ++ tailWord_3117596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117596).length < 2 ^ (prefixWord ++ tailWord_3117596).sum := by decide
  have hdescent : baseEnd_3117596 < baseStart_3117596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117616 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 3]
def baseStart_3117616 : Nat := 118140960795 + 3117616 * 2 ^ 59
def prefixEnd_3117616 : Nat := 4983230072969 + 3 ^ 40 * 3117616 * 2
def baseEnd_3117616 : Nat := 1600835504147579546762351

theorem tailTrace_3117616 : CollatzResearch.WordTrace tailWord_3117616 prefixEnd_3117616 1600835504147579546762351 := by
  unfold tailWord_3117616
  simp only [CollatzResearch.WordTrace]
  refine ⟨56854398536708576633842351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75805864715611435511789801 56854398536708576633842351)
  ·
    refine ⟨85281597805062864950763527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56854398536708576633842351 85281597805062864950763527)
    ·
      refine ⟨127922396707594297426145291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85281597805062864950763527 127922396707594297426145291)
      ·
        refine ⟨191883595061391446139217937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127922396707594297426145291 191883595061391446139217937)
        ·
          refine ⟨143912696296043584604413453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191883595061391446139217937 143912696296043584604413453)
          ·
            refine ⟨53967261111016344226655045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143912696296043584604413453 53967261111016344226655045)
            ·
              refine ⟨10118861458315564542497821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53967261111016344226655045 10118861458315564542497821)
              ·
                refine ⟨3794573046868336703436683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10118861458315564542497821 3794573046868336703436683)
                ·
                  refine ⟨5691859570302505055155025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794573046868336703436683 5691859570302505055155025)
                  ·
                    refine ⟨4268894677726878791366269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5691859570302505055155025 4268894677726878791366269)
                    ·
                      refine ⟨1600835504147579546762351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4268894677726878791366269 1600835504147579546762351)
                      ·
                        rfl

theorem cell23_3117616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 3].length) (baseStart_3117616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117616 prefixEnd_3117616 := by exact prefixLift 3117616
  have htrace : WordTrace (prefixWord ++ tailWord_3117616) baseStart_3117616 baseEnd_3117616 := by
    simpa [prefixWord, tailWord_3117616, baseEnd_3117616] using wordTrace_append hprefix tailTrace_3117616
  have hstable : (prefixWord ++ tailWord_3117616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117616).length < 2 ^ (prefixWord ++ tailWord_3117616).sum := by decide
  have hdescent : baseEnd_3117616 < baseStart_3117616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117680 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 2, 1, 3]
def baseStart_3117680 : Nat := 118140960795 + 3117680 * 2 ^ 59
def prefixEnd_3117680 : Nat := 4983230072969 + 3 ^ 40 * 3117680 * 2
def baseEnd_3117680 : Nat := 1600868366909467296362057

theorem tailTrace_3117680 : CollatzResearch.WordTrace tailWord_3117680 prefixEnd_3117680 1600868366909467296362057 := by
  unfold tailWord_3117680
  simp only [CollatzResearch.WordTrace]
  refine ⟨56855565672592646099007247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75807420896790194798676329 56855565672592646099007247)
  ·
    refine ⟨85283348508888969148510871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56855565672592646099007247 85283348508888969148510871)
    ·
      refine ⟨127925022763333453722766307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85283348508888969148510871 127925022763333453722766307)
      ·
        refine ⟨191887534145000180584149461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127925022763333453722766307 191887534145000180584149461)
        ·
          refine ⟨4497364081523441732441003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 191887534145000180584149461 4497364081523441732441003)
          ·
            refine ⟨6746046122285162598661505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497364081523441732441003 6746046122285162598661505)
            ·
              refine ⟨5059534591713871948996129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746046122285162598661505 5059534591713871948996129)
              ·
                refine ⟨3794650943785403961747097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5059534591713871948996129 3794650943785403961747097)
                ·
                  refine ⟨2845988207839052971310323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3794650943785403961747097 2845988207839052971310323)
                  ·
                    refine ⟨4268982311758579456965485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2845988207839052971310323 4268982311758579456965485)
                    ·
                      refine ⟨1600868366909467296362057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4268982311758579456965485 1600868366909467296362057)
                      ·
                        rfl

theorem cell23_3117680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2, 1, 3].length) (baseStart_3117680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117680 prefixEnd_3117680 := by exact prefixLift 3117680
  have htrace : WordTrace (prefixWord ++ tailWord_3117680) baseStart_3117680 baseEnd_3117680 := by
    simpa [prefixWord, tailWord_3117680, baseEnd_3117680] using wordTrace_append hprefix tailTrace_3117680
  have hstable : (prefixWord ++ tailWord_3117680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117680).length < 2 ^ (prefixWord ++ tailWord_3117680).sum := by decide
  have hdescent : baseEnd_3117680 < baseStart_3117680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117699 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 4]
def baseStart_3117699 : Nat := 118140960795 + 3117699 * 2 ^ 59
def prefixEnd_3117699 : Nat := 4983230072969 + 3 ^ 40 * 3117699 * 2
def baseEnd_3117699 : Nat := 1600878123041902722024469

theorem tailTrace_3117699 : CollatzResearch.WordTrace tailWord_3117699 prefixEnd_3117699 1600878123041902722024469 := by
  unfold tailWord_3117699
  simp only [CollatzResearch.WordTrace]
  refine ⟨113711824332116458442956151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75807882888077638961970767 113711824332116458442956151)
  ·
    refine ⟨170567736498174687664434227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113711824332116458442956151 170567736498174687664434227)
    ·
      refine ⟨255851604747262031496651341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170567736498174687664434227 255851604747262031496651341)
      ·
        refine ⟨95944351780223261811244253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255851604747262031496651341 95944351780223261811244253)
        ·
          refine ⟨35979131917583723179216595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95944351780223261811244253 35979131917583723179216595)
          ·
            refine ⟨53968697876375584768824893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35979131917583723179216595 53968697876375584768824893)
            ·
              refine ⟨20238261703640844288309335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53968697876375584768824893 20238261703640844288309335)
              ·
                refine ⟨30357392555461266432464003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20238261703640844288309335 30357392555461266432464003)
                ·
                  refine ⟨45536088833191899648696005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30357392555461266432464003 45536088833191899648696005)
                  ·
                    refine ⟨8538016656223481184130501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45536088833191899648696005 8538016656223481184130501)
                    ·
                      refine ⟨1600878123041902722024469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8538016656223481184130501 1600878123041902722024469)
                      ·
                        rfl

theorem cell23_3117699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_3117699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117699 prefixEnd_3117699 := by exact prefixLift 3117699
  have htrace : WordTrace (prefixWord ++ tailWord_3117699) baseStart_3117699 baseEnd_3117699 := by
    simpa [prefixWord, tailWord_3117699, baseEnd_3117699] using wordTrace_append hprefix tailTrace_3117699
  have hstable : (prefixWord ++ tailWord_3117699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117699).length < 2 ^ (prefixWord ++ tailWord_3117699).sum := by decide
  have hdescent : baseEnd_3117699 < baseStart_3117699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117703 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 1, 4, 2]
def baseStart_3117703 : Nat := 118140960795 + 3117703 * 2 ^ 59
def prefixEnd_3117703 : Nat := 4983230072969 + 3 ^ 40 * 3117703 * 2
def baseEnd_3117703 : Nat := 1600880176964520706374451

theorem tailTrace_3117703 : CollatzResearch.WordTrace tailWord_3117703 prefixEnd_3117703 1600880176964520706374451 := by
  unfold tailWord_3117703
  simp only [CollatzResearch.WordTrace]
  refine ⟨113711970224101967126101763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75807980149401311417401175 113711970224101967126101763)
  ·
    refine ⟨170567955336152950689152645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113711970224101967126101763 170567955336152950689152645)
    ·
      refine ⟨31981491625528678254216121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170567955336152950689152645 31981491625528678254216121)
      ·
        refine ⟨23986118719146508690662091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31981491625528678254216121 23986118719146508690662091)
        ·
          refine ⟨35979178078719763035993137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23986118719146508690662091 35979178078719763035993137)
          ·
            refine ⟨26984383559039822276994853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35979178078719763035993137 26984383559039822276994853)
            ·
              refine ⟨5059571917319966676936535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26984383559039822276994853 5059571917319966676936535)
              ·
                refine ⟨7589357875979950015404803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059571917319966676936535 7589357875979950015404803)
                ·
                  refine ⟨11384036813969925023107205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7589357875979950015404803 11384036813969925023107205)
                  ·
                    refine ⟨2134506902619360941832601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11384036813969925023107205 2134506902619360941832601)
                    ·
                      refine ⟨1600880176964520706374451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134506902619360941832601 1600880176964520706374451)
                      ·
                        rfl

theorem cell23_3117703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_3117703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117703 prefixEnd_3117703 := by exact prefixLift 3117703
  have htrace : WordTrace (prefixWord ++ tailWord_3117703) baseStart_3117703 baseEnd_3117703 := by
    simpa [prefixWord, tailWord_3117703, baseEnd_3117703] using wordTrace_append hprefix tailTrace_3117703
  have hstable : (prefixWord ++ tailWord_3117703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117703).length < 2 ^ (prefixWord ++ tailWord_3117703).sum := by decide
  have hdescent : baseEnd_3117703 < baseStart_3117703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117726 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_3117726 : Nat := 118140960795 + 3117726 * 2 ^ 59
def prefixEnd_3117726 : Nat := 4983230072969 + 3 ^ 40 * 3117726 * 2
def baseEnd_3117726 : Nat := 177876887446619346265205

theorem tailTrace_3117726 : CollatzResearch.WordTrace tailWord_3117726 prefixEnd_3117726 177876887446619346265205 := by
  unfold tailWord_3117726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14214101137877330256773629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75808539402012428036126021 14214101137877330256773629)
  ·
    refine ⟨5330287926703998846290111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14214101137877330256773629 5330287926703998846290111)
    ·
      refine ⟨7995431890055998269435167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5330287926703998846290111 7995431890055998269435167)
      ·
        refine ⟨11993147835083997404152751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7995431890055998269435167 11993147835083997404152751)
        ·
          refine ⟨17989721752625996106229127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11993147835083997404152751 17989721752625996106229127)
          ·
            refine ⟨26984582628938994159343691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17989721752625996106229127 26984582628938994159343691)
            ·
              refine ⟨40476873943408491239015537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26984582628938994159343691 40476873943408491239015537)
              ·
                refine ⟨30357655457556368429261653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40476873943408491239015537 30357655457556368429261653)
                ·
                  refine ⟨177876887446619346265205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30357655457556368429261653 177876887446619346265205)
                  ·
                    rfl

theorem cell23_3117726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_3117726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117726 prefixEnd_3117726 := by exact prefixLift 3117726
  have htrace : WordTrace (prefixWord ++ tailWord_3117726) baseStart_3117726 baseEnd_3117726 := by
    simpa [prefixWord, tailWord_3117726, baseEnd_3117726] using wordTrace_append hprefix tailTrace_3117726
  have hstable : (prefixWord ++ tailWord_3117726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117726).length < 2 ^ (prefixWord ++ tailWord_3117726).sum := by decide
  have hdescent : baseEnd_3117726 < baseStart_3117726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117793 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_3117793 : Nat := 118140960795 + 3117793 * 2 ^ 59
def prefixEnd_3117793 : Nat := 4983230072969 + 3 ^ 40 * 3117793 * 2
def baseEnd_3117793 : Nat := 1600926390223425354249037

theorem tailTrace_3117793 : CollatzResearch.WordTrace tailWord_3117793 prefixEnd_3117793 1600926390223425354249037 := by
  unfold tailWord_3117793
  simp only [CollatzResearch.WordTrace]
  refine ⟨113715252793775912496878033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75810168529183941664585355 113715252793775912496878033)
  ·
    refine ⟨85286439595331934372658525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113715252793775912496878033 85286439595331934372658525)
    ·
      refine ⟨31982414848249475389746947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85286439595331934372658525 31982414848249475389746947)
      ·
        refine ⟨47973622272374213084620421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31982414848249475389746947 47973622272374213084620421)
        ·
          refine ⟨8995054176070164953366329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47973622272374213084620421 8995054176070164953366329)
          ·
            refine ⟨6746290632052623715024747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8995054176070164953366329 6746290632052623715024747)
            ·
              refine ⟨10119435948078935572537121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6746290632052623715024747 10119435948078935572537121)
              ·
                refine ⟨7589576961059201679402841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10119435948078935572537121 7589576961059201679402841)
                ·
                  refine ⟨5692182720794401259552131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7589576961059201679402841 5692182720794401259552131)
                  ·
                    refine ⟨8538274081191601889328197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692182720794401259552131 8538274081191601889328197)
                    ·
                      refine ⟨1600926390223425354249037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8538274081191601889328197 1600926390223425354249037)
                      ·
                        rfl

theorem cell23_3117793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_3117793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117793 prefixEnd_3117793 := by exact prefixLift 3117793
  have htrace : WordTrace (prefixWord ++ tailWord_3117793) baseStart_3117793 baseEnd_3117793 := by
    simpa [prefixWord, tailWord_3117793, baseEnd_3117793] using wordTrace_append hprefix tailTrace_3117793
  have hstable : (prefixWord ++ tailWord_3117793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117793).length < 2 ^ (prefixWord ++ tailWord_3117793).sum := by decide
  have hdescent : baseEnd_3117793 < baseStart_3117793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117816 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 6]
def baseStart_3117816 : Nat := 118140960795 + 3117816 * 2 ^ 59
def prefixEnd_3117816 : Nat := 4983230072969 + 3 ^ 40 * 3117816 * 2
def baseEnd_3117816 : Nat := 177882022253164307140159

theorem tailTrace_3117816 : CollatzResearch.WordTrace tailWord_3117816 prefixEnd_3117816 177882022253164307140159 := by
  unfold tailWord_3117816
  simp only [CollatzResearch.WordTrace]
  refine ⟨56858045836346293712482651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75810727781795058283310201 56858045836346293712482651)
  ·
    refine ⟨85287068754519440568723977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56858045836346293712482651 85287068754519440568723977)
    ·
      refine ⟨63965301565889580426542983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85287068754519440568723977 63965301565889580426542983)
      ·
        refine ⟨95947952348834370639814475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63965301565889580426542983 95947952348834370639814475)
        ·
          refine ⟨143921928523251555959721713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95947952348834370639814475 143921928523251555959721713)
          ·
            refine ⟨107941446392438666969791285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143921928523251555959721713 107941446392438666969791285)
            ·
              refine ⟨10119510599291125028417933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107941446392438666969791285 10119510599291125028417933)
              ·
                refine ⟨3794816474734171885656725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10119510599291125028417933 3794816474734171885656725)
                ·
                  refine ⟨177882022253164307140159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3794816474734171885656725 177882022253164307140159)
                  ·
                    rfl

theorem cell23_3117816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 6].length) (baseStart_3117816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117816 prefixEnd_3117816 := by exact prefixLift 3117816
  have htrace : WordTrace (prefixWord ++ tailWord_3117816) baseStart_3117816 baseEnd_3117816 := by
    simpa [prefixWord, tailWord_3117816, baseEnd_3117816] using wordTrace_append hprefix tailTrace_3117816
  have hstable : (prefixWord ++ tailWord_3117816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117816).length < 2 ^ (prefixWord ++ tailWord_3117816).sum := by decide
  have hdescent : baseEnd_3117816 < baseStart_3117816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117819 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 8]
def baseStart_3117819 : Nat := 118140960795 + 3117819 * 2 ^ 59
def prefixEnd_3117819 : Nat := 4983230072969 + 3 ^ 40 * 3117819 * 2
def baseEnd_3117819 : Nat := 1600939740720442252523917

theorem tailTrace_3117819 : CollatzResearch.WordTrace tailWord_3117819 prefixEnd_3117819 1600939740720442252523917 := by
  unfold tailWord_3117819
  simp only [CollatzResearch.WordTrace]
  refine ⟨113716201091681718937324511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75810800727787812624883007 113716201091681718937324511)
  ·
    refine ⟨170574301637522578405986767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113716201091681718937324511 170574301637522578405986767)
    ·
      refine ⟨255861452456283867608980151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170574301637522578405986767 255861452456283867608980151)
      ·
        refine ⟨383792178684425801413470227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255861452456283867608980151 383792178684425801413470227)
        ·
          refine ⟨575688268026638702120205341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383792178684425801413470227 575688268026638702120205341)
          ·
            refine ⟨215883100509989513295077003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575688268026638702120205341 215883100509989513295077003)
            ·
              refine ⟨323824650764984269942615505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215883100509989513295077003 323824650764984269942615505)
              ·
                refine ⟨242868488073738202456961629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323824650764984269942615505 242868488073738202456961629)
                ·
                  refine ⟨91075683027651825921360611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242868488073738202456961629 91075683027651825921360611)
                  ·
                    refine ⟨136613524541477738882040917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91075683027651825921360611 136613524541477738882040917)
                    ·
                      refine ⟨1600939740720442252523917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 136613524541477738882040917 1600939740720442252523917)
                      ·
                        rfl

theorem cell23_3117819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_3117819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117819 prefixEnd_3117819 := by exact prefixLift 3117819
  have htrace : WordTrace (prefixWord ++ tailWord_3117819) baseStart_3117819 baseEnd_3117819 := by
    simpa [prefixWord, tailWord_3117819, baseEnd_3117819] using wordTrace_append hprefix tailTrace_3117819
  have hstable : (prefixWord ++ tailWord_3117819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117819).length < 2 ^ (prefixWord ++ tailWord_3117819).sum := by decide
  have hdescent : baseEnd_3117819 < baseStart_3117819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117887 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 2, 3, 2]
def baseStart_3117887 : Nat := 118140960795 + 3117887 * 2 ^ 59
def prefixEnd_3117887 : Nat := 4983230072969 + 3 ^ 40 * 3117887 * 2
def baseEnd_3117887 : Nat := 1600974657404947986473605

theorem tailTrace_3117887 : CollatzResearch.WordTrace tailWord_3117887 prefixEnd_3117887 1600974657404947986473605 := by
  unfold tailWord_3117887
  simp only [CollatzResearch.WordTrace]
  refine ⟨113718681255435366550799915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75812454170290244367199943 113718681255435366550799915)
  ·
    refine ⟨170578021883153049826199873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113718681255435366550799915 170578021883153049826199873)
    ·
      refine ⟨127933516412364787369649905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170578021883153049826199873 127933516412364787369649905)
      ·
        refine ⟨95950137309273590527237429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127933516412364787369649905 95950137309273590527237429)
        ·
          refine ⟨8995325372744399111928509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95950137309273590527237429 8995325372744399111928509)
          ·
            refine ⟨3373247014779149666973191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8995325372744399111928509 3373247014779149666973191)
            ·
              refine ⟨5059870522168724500459787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373247014779149666973191 5059870522168724500459787)
              ·
                refine ⟨7589805783253086750689681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059870522168724500459787 7589805783253086750689681)
                ·
                  refine ⟨5692354337439815063017261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7589805783253086750689681 5692354337439815063017261)
                  ·
                    refine ⟨2134632876539930648631473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5692354337439815063017261 2134632876539930648631473)
                    ·
                      refine ⟨1600974657404947986473605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134632876539930648631473 1600974657404947986473605)
                      ·
                        rfl

theorem cell23_3117887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_3117887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117887 prefixEnd_3117887 := by exact prefixLift 3117887
  have htrace : WordTrace (prefixWord ++ tailWord_3117887) baseStart_3117887 baseEnd_3117887 := by
    simpa [prefixWord, tailWord_3117887, baseEnd_3117887] using wordTrace_append hprefix tailTrace_3117887
  have hstable : (prefixWord ++ tailWord_3117887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117887).length < 2 ^ (prefixWord ++ tailWord_3117887).sum := by decide
  have hdescent : baseEnd_3117887 < baseStart_3117887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117900 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3117900 : Nat := 118140960795 + 3117900 * 2 ^ 59
def prefixEnd_3117900 : Nat := 4983230072969 + 3 ^ 40 * 3117900 * 2
def baseEnd_3117900 : Nat := 1600981332653456435611045

theorem tailTrace_3117900 : CollatzResearch.WordTrace tailWord_3117900 prefixEnd_3117900 1600981332653456435611045 := by
  unfold tailWord_3117900
  simp only [CollatzResearch.WordTrace]
  refine ⟨56859577702194134885511577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75812770269592179847348769 56859577702194134885511577)
  ·
    refine ⟨42644683276645601164133683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56859577702194134885511577 42644683276645601164133683)
    ·
      refine ⟨63967024914968401746200525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42644683276645601164133683 63967024914968401746200525)
      ·
        refine ⟨23987634343113150654825197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63967024914968401746200525 23987634343113150654825197)
        ·
          refine ⟨8995362878667431495559449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23987634343113150654825197 8995362878667431495559449)
          ·
            refine ⟨6746522159000573621669587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8995362878667431495559449 6746522159000573621669587)
            ·
              refine ⟨10119783238500860432504381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6746522159000573621669587 10119783238500860432504381)
              ·
                refine ⟨3794918714437822662189143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10119783238500860432504381 3794918714437822662189143)
                ·
                  refine ⟨5692378071656733993283715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794918714437822662189143 5692378071656733993283715)
                  ·
                    refine ⟨8538567107485100989925573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692378071656733993283715 8538567107485100989925573)
                    ·
                      refine ⟨1600981332653456435611045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8538567107485100989925573 1600981332653456435611045)
                      ·
                        rfl

theorem cell23_3117900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3117900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117900 prefixEnd_3117900 := by exact prefixLift 3117900
  have htrace : WordTrace (prefixWord ++ tailWord_3117900) baseStart_3117900 baseEnd_3117900 := by
    simpa [prefixWord, tailWord_3117900, baseEnd_3117900] using wordTrace_append hprefix tailTrace_3117900
  have hstable : (prefixWord ++ tailWord_3117900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117900).length < 2 ^ (prefixWord ++ tailWord_3117900).sum := by decide
  have hdescent : baseEnd_3117900 < baseStart_3117900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117906 : List Nat := [3, 2, 2, 1, 1, 2, 12]
def baseStart_3117906 : Nat := 118140960795 + 3117906 * 2 ^ 59
def prefixEnd_3117906 : Nat := 4983230072969 + 3 ^ 40 * 3117906 * 2
def baseEnd_3117906 : Nat := 19765239673301029779457

theorem tailTrace_3117906 : CollatzResearch.WordTrace tailWord_3117906 prefixEnd_3117906 19765239673301029779457 := by
  unfold tailWord_3117906
  simp only [CollatzResearch.WordTrace]
  refine ⟨28429843560591633198935393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75812916161577688530494381 28429843560591633198935393)
  ·
    refine ⟨21322382670443724899201545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28429843560591633198935393 21322382670443724899201545)
    ·
      refine ⟨15991787002832793674401159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21322382670443724899201545 15991787002832793674401159)
      ·
        refine ⟨23987680504249190511601739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15991787002832793674401159 23987680504249190511601739)
        ·
          refine ⟨35981520756373785767402609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23987680504249190511601739 35981520756373785767402609)
          ·
            refine ⟨26986140567280339325551957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35981520756373785767402609 26986140567280339325551957)
            ·
              refine ⟨19765239673301029779457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 26986140567280339325551957 19765239673301029779457)
              ·
                rfl

theorem cell23_3117906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 12].length) (baseStart_3117906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117906 prefixEnd_3117906 := by exact prefixLift 3117906
  have htrace : WordTrace (prefixWord ++ tailWord_3117906) baseStart_3117906 baseEnd_3117906 := by
    simpa [prefixWord, tailWord_3117906, baseEnd_3117906] using wordTrace_append hprefix tailTrace_3117906
  have hstable : (prefixWord ++ tailWord_3117906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117906).length < 2 ^ (prefixWord ++ tailWord_3117906).sum := by decide
  have hdescent : baseEnd_3117906 < baseStart_3117906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117927 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 2, 4]
def baseStart_3117927 : Nat := 118140960795 + 3117927 * 2 ^ 59
def prefixEnd_3117927 : Nat := 4983230072969 + 3 ^ 40 * 3117927 * 2
def baseEnd_3117927 : Nat := 533665065543709276657807

theorem tailTrace_3117927 : CollatzResearch.WordTrace tailWord_3117927 prefixEnd_3117927 533665065543709276657807 := by
  unfold tailWord_3117927
  simp only [CollatzResearch.WordTrace]
  refine ⟨113720140175290453382256035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75813426783526968921504023 113720140175290453382256035)
  ·
    refine ⟨170580210262935680073384053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113720140175290453382256035 170580210262935680073384053)
    ·
      refine ⟨15991894712150220006879755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170580210262935680073384053 15991894712150220006879755)
      ·
        refine ⟨23987842068225330010319633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15991894712150220006879755 23987842068225330010319633)
        ·
          refine ⟨17990881551168997507739725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23987842068225330010319633 17990881551168997507739725)
          ·
            refine ⟨6746580581688374065402397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17990881551168997507739725 6746580581688374065402397)
            ·
              refine ⟨2529967718133140274525899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6746580581688374065402397 2529967718133140274525899)
              ·
                refine ⟨3794951577199710411788849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529967718133140274525899 3794951577199710411788849)
                ·
                  refine ⟨2846213682899782808841637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3794951577199710411788849 2846213682899782808841637)
                  ·
                    refine ⟨533665065543709276657807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2846213682899782808841637 533665065543709276657807)
                    ·
                      rfl

theorem cell23_3117927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_3117927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117927 prefixEnd_3117927 := by exact prefixLift 3117927
  have htrace : WordTrace (prefixWord ++ tailWord_3117927) baseStart_3117927 baseEnd_3117927 := by
    simpa [prefixWord, tailWord_3117927, baseEnd_3117927] using wordTrace_append hprefix tailTrace_3117927
  have hstable : (prefixWord ++ tailWord_3117927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117927).length < 2 ^ (prefixWord ++ tailWord_3117927).sum := by decide
  have hdescent : baseEnd_3117927 < baseStart_3117927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117936 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 2, 7]
def baseStart_3117936 : Nat := 118140960795 + 3117936 * 2 ^ 59
def prefixEnd_3117936 : Nat := 4983230072969 + 3 ^ 40 * 3117936 * 2
def baseEnd_3117936 : Nat := 533666605985672764920293

theorem tailTrace_3117936 : CollatzResearch.WordTrace tailWord_3117936 prefixEnd_3117936 533666605985672764920293 := by
  unfold tailWord_3117936
  simp only [CollatzResearch.WordTrace]
  refine ⟨56860234216128923959666831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75813645621505231946222441 56860234216128923959666831)
  ·
    refine ⟨85290351324193385939500247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56860234216128923959666831 85290351324193385939500247)
    ·
      refine ⟨127935526986290078909250371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85290351324193385939500247 127935526986290078909250371)
      ·
        refine ⟨191903290479435118363875557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127935526986290078909250371 191903290479435118363875557)
        ·
          refine ⟨35981866964894084693226667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191903290479435118363875557 35981866964894084693226667)
          ·
            refine ⟨53972800447341127039840001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35981866964894084693226667 53972800447341127039840001)
            ·
              refine ⟨40479600335505845279880001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53972800447341127039840001 40479600335505845279880001)
              ·
                refine ⟨30359700251629383959910001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40479600335505845279880001 30359700251629383959910001)
                ·
                  refine ⟨22769775188722037969932501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30359700251629383959910001 22769775188722037969932501)
                  ·
                    refine ⟨533666605985672764920293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22769775188722037969932501 533666605985672764920293)
                    ·
                      rfl

theorem cell23_3117936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_3117936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117936 prefixEnd_3117936 := by exact prefixLift 3117936
  have htrace : WordTrace (prefixWord ++ tailWord_3117936) baseStart_3117936 baseEnd_3117936 := by
    simpa [prefixWord, tailWord_3117936, baseEnd_3117936] using wordTrace_append hprefix tailTrace_3117936
  have hstable : (prefixWord ++ tailWord_3117936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117936).length < 2 ^ (prefixWord ++ tailWord_3117936).sum := by decide
  have hdescent : baseEnd_3117936 < baseStart_3117936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117943 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 2, 7, 2]
def baseStart_3117943 : Nat := 118140960795 + 3117943 * 2 ^ 59
def prefixEnd_3117943 : Nat := 4983230072969 + 3 ^ 40 * 3117943 * 2
def baseEnd_3117943 : Nat := 1601003412321599767373347

theorem tailTrace_3117943 : CollatzResearch.WordTrace tailWord_3117943 prefixEnd_3117943 1601003412321599767373347 := by
  unfold tailWord_3117943
  simp only [CollatzResearch.WordTrace]
  refine ⟨113720723743232488114838483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75813815828821658743225655 113720723743232488114838483)
  ·
    refine ⟨170581085614848732172257725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113720723743232488114838483 170581085614848732172257725)
    ·
      refine ⟨63967907105568274564596647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170581085614848732172257725 63967907105568274564596647)
      ·
        refine ⟨95951860658352411846894971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63967907105568274564596647 95951860658352411846894971)
        ·
          refine ⟨143927790987528617770342457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95951860658352411846894971 143927790987528617770342457)
          ·
            refine ⟨107945843240646463327756843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143927790987528617770342457 107945843240646463327756843)
            ·
              refine ⟨161918764860969694991635265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107945843240646463327756843 161918764860969694991635265)
              ·
                refine ⟨121439073645727271243726449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161918764860969694991635265 121439073645727271243726449)
                ·
                  refine ⟨91079305234295453432794837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121439073645727271243726449 91079305234295453432794837)
                  ·
                    refine ⟨2134671216428799689831129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 91079305234295453432794837 2134671216428799689831129)
                    ·
                      refine ⟨1601003412321599767373347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134671216428799689831129 1601003412321599767373347)
                      ·
                        rfl

theorem cell23_3117943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_3117943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117943 prefixEnd_3117943 := by exact prefixLift 3117943
  have htrace : WordTrace (prefixWord ++ tailWord_3117943) baseStart_3117943 baseEnd_3117943 := by
    simpa [prefixWord, tailWord_3117943, baseEnd_3117943] using wordTrace_append hprefix tailTrace_3117943
  have hstable : (prefixWord ++ tailWord_3117943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117943).length < 2 ^ (prefixWord ++ tailWord_3117943).sum := by decide
  have hdescent : baseEnd_3117943 < baseStart_3117943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117954 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3117954 : Nat := 118140960795 + 3117954 * 2 ^ 59
def prefixEnd_3117954 : Nat := 4983230072969 + 3 ^ 40 * 3117954 * 2
def baseEnd_3117954 : Nat := 1601009060608799224335797

theorem tailTrace_3117954 : CollatzResearch.WordTrace tailWord_3117954 prefixEnd_3117954 1601009060608799224335797 := by
  unfold tailWord_3117954
  simp only [CollatzResearch.WordTrace]
  refine ⟨28430281236548159248372229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75814083297461757995659277 28430281236548159248372229)
  ·
    refine ⟨5330677731852779859069793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28430281236548159248372229 5330677731852779859069793)
    ·
      refine ⟨3998008298889584894302345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5330677731852779859069793 3998008298889584894302345)
      ·
        refine ⟨2998506224167188670726759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3998008298889584894302345 2998506224167188670726759)
        ·
          refine ⟨4497759336250783006090139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2998506224167188670726759 4497759336250783006090139)
          ·
            refine ⟨6746639004376174509135209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497759336250783006090139 6746639004376174509135209)
            ·
              refine ⟨5059979253282130881851407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746639004376174509135209 5059979253282130881851407)
              ·
                refine ⟨7589968879923196322777111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059979253282130881851407 7589968879923196322777111)
                ·
                  refine ⟨11384953319884794484165667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7589968879923196322777111 11384953319884794484165667)
                  ·
                    refine ⟨17077429979827191726248501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11384953319884794484165667 17077429979827191726248501)
                    ·
                      refine ⟨1601009060608799224335797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17077429979827191726248501 1601009060608799224335797)
                      ·
                        rfl

theorem cell23_3117954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3117954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3117954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3117954 prefixEnd_3117954 := by exact prefixLift 3117954
  have htrace : WordTrace (prefixWord ++ tailWord_3117954) baseStart_3117954 baseEnd_3117954 := by
    simpa [prefixWord, tailWord_3117954, baseEnd_3117954] using wordTrace_append hprefix tailTrace_3117954
  have hstable : (prefixWord ++ tailWord_3117954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117954).length < 2 ^ (prefixWord ++ tailWord_3117954).sum := by decide
  have hdescent : baseEnd_3117954 < baseStart_3117954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118040 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 2, 3, 3]
def baseStart_3118040 : Nat := 118140960795 + 3118040 * 2 ^ 59
def prefixEnd_3118040 : Nat := 4983230072969 + 3 ^ 40 * 3118040 * 2
def baseEnd_3118040 : Nat := 1601053219945085887860401

theorem tailTrace_3118040 : CollatzResearch.WordTrace tailWord_3118040 prefixEnd_3118040 1601053219945085887860401 := by
  unfold tailWord_3118040
  simp only [CollatzResearch.WordTrace]
  refine ⟨56862130811940536840559787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75816174415920715787413049 56862130811940536840559787)
  ·
    refine ⟨85293196217910805260839681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56862130811940536840559787 85293196217910805260839681)
    ·
      refine ⟨63969897163433103945629761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85293196217910805260839681 63969897163433103945629761)
      ·
        refine ⟨47977422872574827959222321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63969897163433103945629761 47977422872574827959222321)
        ·
          refine ⟨35983067154431120969416741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47977422872574827959222321 35983067154431120969416741)
          ·
            refine ⟨6746825091455835181765639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35983067154431120969416741 6746825091455835181765639)
            ·
              refine ⟨10120237637183752772648459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6746825091455835181765639 10120237637183752772648459)
              ·
                refine ⟨15180356455775629158972689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10120237637183752772648459 15180356455775629158972689)
                ·
                  refine ⟨11385267341831721869229517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15180356455775629158972689 11385267341831721869229517)
                  ·
                    refine ⟨4269475253186895700961069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11385267341831721869229517 4269475253186895700961069)
                    ·
                      refine ⟨1601053219945085887860401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4269475253186895700961069 1601053219945085887860401)
                      ·
                        rfl

theorem cell23_3118040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_3118040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118040 prefixEnd_3118040 := by exact prefixLift 3118040
  have htrace : WordTrace (prefixWord ++ tailWord_3118040) baseStart_3118040 baseEnd_3118040 := by
    simpa [prefixWord, tailWord_3118040, baseEnd_3118040] using wordTrace_append hprefix tailTrace_3118040
  have hstable : (prefixWord ++ tailWord_3118040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118040).length < 2 ^ (prefixWord ++ tailWord_3118040).sum := by decide
  have hdescent : baseEnd_3118040 < baseStart_3118040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118134 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3118134 : Nat := 118140960795 + 3118134 * 2 ^ 59
def prefixEnd_3118134 : Nat := 4983230072969 + 3 ^ 40 * 3118134 * 2
def baseEnd_3118134 : Nat := 1601101487126608520084969

theorem tailTrace_3118134 : CollatzResearch.WordTrace tailWord_3118134 prefixEnd_3118134 1601101487126608520084969 := by
  unfold tailWord_3118134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7107980630346282983440091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75818460057027018490027637 7107980630346282983440091)
  ·
    refine ⟨10661970945519424475160137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7107980630346282983440091 10661970945519424475160137)
    ·
      refine ⟨7996478209139568356370103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10661970945519424475160137 7996478209139568356370103)
      ·
        refine ⟨11994717313709352534555155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7996478209139568356370103 11994717313709352534555155)
        ·
          refine ⟨17992075970564028801832733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11994717313709352534555155 17992075970564028801832733)
          ·
            refine ⟨6747028488961510800687275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17992075970564028801832733 6747028488961510800687275)
            ·
              refine ⟨10120542733442266201030913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6747028488961510800687275 10120542733442266201030913)
              ·
                refine ⟨7590407050081699650773185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10120542733442266201030913 7590407050081699650773185)
                ·
                  refine ⟨5692805287561274738079889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7590407050081699650773185 5692805287561274738079889)
                  ·
                    refine ⟨4269603965670956053559917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5692805287561274738079889 4269603965670956053559917)
                    ·
                      refine ⟨1601101487126608520084969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4269603965670956053559917 1601101487126608520084969)
                      ·
                        rfl

theorem cell23_3118134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3118134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118134 prefixEnd_3118134 := by exact prefixLift 3118134
  have htrace : WordTrace (prefixWord ++ tailWord_3118134) baseStart_3118134 baseEnd_3118134 := by
    simpa [prefixWord, tailWord_3118134, baseEnd_3118134] using wordTrace_append hprefix tailTrace_3118134
  have hstable : (prefixWord ++ tailWord_3118134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118134).length < 2 ^ (prefixWord ++ tailWord_3118134).sum := by decide
  have hdescent : baseEnd_3118134 < baseStart_3118134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118141 : List Nat := [1, 4, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_3118141 : Nat := 118140960795 + 3118141 * 2 ^ 59
def prefixEnd_3118141 : Nat := 4983230072969 + 3 ^ 40 * 3118141 * 2
def baseEnd_3118141 : Nat := 533701693830396664232479

theorem tailTrace_3118141 : CollatzResearch.WordTrace tailWord_3118141 prefixEnd_3118141 533701693830396664232479 := by
  unfold tailWord_3118141
  simp only [CollatzResearch.WordTrace]
  refine ⟨113727945396515167930546277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75818630264343445287030851 113727945396515167930546277)
  ·
    refine ⟨21323989761846593986977427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113727945396515167930546277 21323989761846593986977427)
    ·
      refine ⟨31985984642769890980466141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21323989761846593986977427 31985984642769890980466141)
      ·
        refine ⟨11994744241038709117674803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31985984642769890980466141 11994744241038709117674803)
        ·
          refine ⟨17992116361558063676512205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11994744241038709117674803 17992116361558063676512205)
          ·
            refine ⟨6747043635584273878692077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17992116361558063676512205 6747043635584273878692077)
            ·
              refine ⟨2530141363344102704509529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6747043635584273878692077 2530141363344102704509529)
              ·
                refine ⟨1897606022508077028382147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2530141363344102704509529 1897606022508077028382147)
                ·
                  refine ⟨2846409033762115542573221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897606022508077028382147 2846409033762115542573221)
                  ·
                    refine ⟨533701693830396664232479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2846409033762115542573221 533701693830396664232479)
                    ·
                      rfl

theorem cell23_3118141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_3118141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118141 prefixEnd_3118141 := by exact prefixLift 3118141
  have htrace : WordTrace (prefixWord ++ tailWord_3118141) baseStart_3118141 baseEnd_3118141 := by
    simpa [prefixWord, tailWord_3118141, baseEnd_3118141] using wordTrace_append hprefix tailTrace_3118141
  have hstable : (prefixWord ++ tailWord_3118141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118141).length < 2 ^ (prefixWord ++ tailWord_3118141).sum := by decide
  have hdescent : baseEnd_3118141 < baseStart_3118141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118143 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_3118143 : Nat := 118140960795 + 3118143 * 2 ^ 59
def prefixEnd_3118143 : Nat := 4983230072969 + 3 ^ 40 * 3118143 * 2
def baseEnd_3118143 : Nat := 1601106108452498984872427

theorem tailTrace_3118143 : CollatzResearch.WordTrace tailWord_3118143 prefixEnd_3118143 1601106108452498984872427 := by
  unfold tailWord_3118143
  simp only [CollatzResearch.WordTrace]
  refine ⟨113728018342507922272119083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75818678895005281514746055 113728018342507922272119083)
  ·
    refine ⟨170592027513761883408178625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113728018342507922272119083 170592027513761883408178625)
    ·
      refine ⟨127944020635321412556133969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170592027513761883408178625 127944020635321412556133969)
      ·
        refine ⟨95958015476491059417100477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127944020635321412556133969 95958015476491059417100477)
        ·
          refine ⟨35984255803684147281412679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95958015476491059417100477 35984255803684147281412679)
          ·
            refine ⟨53976383705526220922119019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35984255803684147281412679 53976383705526220922119019)
            ·
              refine ⟨80964575558289331383178529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53976383705526220922119019 80964575558289331383178529)
              ·
                refine ⟨60723431668716998537383897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80964575558289331383178529 60723431668716998537383897)
                ·
                  refine ⟨45542573751537748903037923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60723431668716998537383897 45542573751537748903037923)
                  ·
                    refine ⟨68313860627306623354556885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45542573751537748903037923 68313860627306623354556885)
                    ·
                      refine ⟨1601106108452498984872427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68313860627306623354556885 1601106108452498984872427)
                      ·
                        rfl

theorem cell23_3118143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_3118143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118143 prefixEnd_3118143 := by exact prefixLift 3118143
  have htrace : WordTrace (prefixWord ++ tailWord_3118143) baseStart_3118143 baseEnd_3118143 := by
    simpa [prefixWord, tailWord_3118143, baseEnd_3118143] using wordTrace_append hprefix tailTrace_3118143
  have hstable : (prefixWord ++ tailWord_3118143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118143).length < 2 ^ (prefixWord ++ tailWord_3118143).sum := by decide
  have hdescent : baseEnd_3118143 < baseStart_3118143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118204 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 3, 2, 2]
def baseStart_3118204 : Nat := 118140960795 + 3118204 * 2 ^ 59
def prefixEnd_3118204 : Nat := 4983230072969 + 3 ^ 40 * 3118204 * 2
def baseEnd_3118204 : Nat := 1601137430772423246209647

theorem tailTrace_3118204 : CollatzResearch.WordTrace tailWord_3118204 prefixEnd_3118204 1601137430772423246209647 := by
  unfold tailWord_3118204
  simp only [CollatzResearch.WordTrace]
  refine ⟨56865121597643464845044833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75820162130191286460059777 56865121597643464845044833)
  ·
    refine ⟨42648841198232598633783625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56865121597643464845044833 42648841198232598633783625)
    ·
      refine ⟨31986630898674448975337719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42648841198232598633783625 31986630898674448975337719)
      ·
        refine ⟨47979946348011673463006579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31986630898674448975337719 47979946348011673463006579)
        ·
          refine ⟨71969919522017510194509869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47979946348011673463006579 71969919522017510194509869)
          ·
            refine ⟨26988719820756566322941201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71969919522017510194509869 26988719820756566322941201)
            ·
              refine ⟨20241539865567424742205901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26988719820756566322941201 20241539865567424742205901)
              ·
                refine ⟨7590577449587784278327213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20241539865567424742205901 7590577449587784278327213)
                ·
                  refine ⟨2846466543595419104372705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7590577449587784278327213 2846466543595419104372705)
                  ·
                    refine ⟨2134849907696564328279529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2846466543595419104372705 2134849907696564328279529)
                    ·
                      refine ⟨1601137430772423246209647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134849907696564328279529 1601137430772423246209647)
                      ·
                        rfl

theorem cell23_3118204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_3118204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118204 prefixEnd_3118204 := by exact prefixLift 3118204
  have htrace : WordTrace (prefixWord ++ tailWord_3118204) baseStart_3118204 baseEnd_3118204 := by
    simpa [prefixWord, tailWord_3118204, baseEnd_3118204] using wordTrace_append hprefix tailTrace_3118204
  have hstable : (prefixWord ++ tailWord_3118204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118204).length < 2 ^ (prefixWord ++ tailWord_3118204).sum := by decide
  have hdescent : baseEnd_3118204 < baseStart_3118204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118217 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 4]
def baseStart_3118217 : Nat := 118140960795 + 3118217 * 2 ^ 59
def prefixEnd_3118217 : Nat := 4983230072969 + 3 ^ 40 * 3118217 * 2
def baseEnd_3118217 : Nat := 1601144106020931695347087

theorem tailTrace_3118217 : CollatzResearch.WordTrace tailWord_3118217 prefixEnd_3118217 1601144106020931695347087 := by
  unfold tailWord_3118217
  simp only [CollatzResearch.WordTrace]
  refine ⟨113730717344239832910312905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75820478229493221940208603 113730717344239832910312905)
  ·
    refine ⟨85298038008179874682734679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113730717344239832910312905 85298038008179874682734679)
    ·
      refine ⟨127947057012269812024102019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85298038008179874682734679 127947057012269812024102019)
      ·
        refine ⟨191920585518404718036153029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127947057012269812024102019 191920585518404718036153029)
        ·
          refine ⟨35985109784700884631778693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191920585518404718036153029 35985109784700884631778693)
          ·
            refine ⟨6747208084631415868458505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35985109784700884631778693 6747208084631415868458505)
            ·
              refine ⟨5060406063473561901343879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6747208084631415868458505 5060406063473561901343879)
              ·
                refine ⟨7590609095210342852015819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060406063473561901343879 7590609095210342852015819)
                ·
                  refine ⟨11385913642815514278023729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7590609095210342852015819 11385913642815514278023729)
                  ·
                    refine ⟨8539435232111635708517797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11385913642815514278023729 8539435232111635708517797)
                    ·
                      refine ⟨1601144106020931695347087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8539435232111635708517797 1601144106020931695347087)
                      ·
                        rfl

theorem cell23_3118217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 4].length) (baseStart_3118217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118217 prefixEnd_3118217 := by exact prefixLift 3118217
  have htrace : WordTrace (prefixWord ++ tailWord_3118217) baseStart_3118217 baseEnd_3118217 := by
    simpa [prefixWord, tailWord_3118217, baseEnd_3118217] using wordTrace_append hprefix tailTrace_3118217
  have hstable : (prefixWord ++ tailWord_3118217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118217).length < 2 ^ (prefixWord ++ tailWord_3118217).sum := by decide
  have hdescent : baseEnd_3118217 < baseStart_3118217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118237 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_3118237 : Nat := 118140960795 + 3118237 * 2 ^ 59
def prefixEnd_3118237 : Nat := 4983230072969 + 3 ^ 40 * 3118237 * 2
def baseEnd_3118237 : Nat := 1601154375634021617096995

theorem tailTrace_3118237 : CollatzResearch.WordTrace tailWord_3118237 prefixEnd_3118237 1601154375634021617096995 := by
  unfold tailWord_3118237
  simp only [CollatzResearch.WordTrace]
  refine ⟨113731446804167376326040965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75820964536111584217360643 113731446804167376326040965)
  ·
    refine ⟨21324646275781383061132681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113731446804167376326040965 21324646275781383061132681)
    ·
      refine ⟨15993484706836037295849511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21324646275781383061132681 15993484706836037295849511)
      ·
        refine ⟨23990227060254055943774267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15993484706836037295849511 23990227060254055943774267)
        ·
          refine ⟨35985340590381083915661401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23990227060254055943774267 35985340590381083915661401)
          ·
            refine ⟨26989005442785812936746051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35985340590381083915661401 26989005442785812936746051)
            ·
              refine ⟨40483508164178719405119077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26989005442785812936746051 40483508164178719405119077)
              ·
                refine ⟨7590657780783509888459827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40483508164178719405119077 7590657780783509888459827)
                ·
                  refine ⟨11385986671175264832689741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7590657780783509888459827 11385986671175264832689741)
                  ·
                    refine ⟨4269745001690724312258653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11385986671175264832689741 4269745001690724312258653)
                    ·
                      refine ⟨1601154375634021617096995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4269745001690724312258653 1601154375634021617096995)
                      ·
                        rfl

theorem cell23_3118237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_3118237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118237 prefixEnd_3118237 := by exact prefixLift 3118237
  have htrace : WordTrace (prefixWord ++ tailWord_3118237) baseStart_3118237 baseEnd_3118237 := by
    simpa [prefixWord, tailWord_3118237, baseEnd_3118237] using wordTrace_append hprefix tailTrace_3118237
  have hstable : (prefixWord ++ tailWord_3118237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118237).length < 2 ^ (prefixWord ++ tailWord_3118237).sum := by decide
  have hdescent : baseEnd_3118237 < baseStart_3118237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118238 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_3118238 : Nat := 118140960795 + 3118238 * 2 ^ 59
def prefixEnd_3118238 : Nat := 4983230072969 + 3 ^ 40 * 3118238 * 2
def baseEnd_3118238 : Nat := 1601154889114676113184491

theorem tailTrace_3118238 : CollatzResearch.WordTrace tailWord_3118238 prefixEnd_3118238 1601154889114676113184491 := by
  unfold tailWord_3118238
  simp only [CollatzResearch.WordTrace]
  refine ⟨14216435409645469187103421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75820988851442502331218245 14216435409645469187103421)
  ·
    refine ⟨5331163278617050945163783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14216435409645469187103421 5331163278617050945163783)
    ·
      refine ⟨7996744917925576417745675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5331163278617050945163783 7996744917925576417745675)
      ·
        refine ⟨11995117376888364626618513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7996744917925576417745675 11995117376888364626618513)
        ·
          refine ⟨8996338032666273469963885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11995117376888364626618513 8996338032666273469963885)
          ·
            refine ⟨3373626762249852551236457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8996338032666273469963885 3373626762249852551236457)
            ·
              refine ⟨2530220071687389413427343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3373626762249852551236457 2530220071687389413427343)
              ·
                refine ⟨3795330107531084120141015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530220071687389413427343 3795330107531084120141015)
                ·
                  refine ⟨5692995161296626180211523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795330107531084120141015 5692995161296626180211523)
                  ·
                    refine ⟨8539492741944939270317285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692995161296626180211523 8539492741944939270317285)
                    ·
                      refine ⟨1601154889114676113184491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8539492741944939270317285 1601154889114676113184491)
                      ·
                        rfl

theorem cell23_3118238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_3118238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118238 prefixEnd_3118238 := by exact prefixLift 3118238
  have htrace : WordTrace (prefixWord ++ tailWord_3118238) baseStart_3118238 baseEnd_3118238 := by
    simpa [prefixWord, tailWord_3118238, baseEnd_3118238] using wordTrace_append hprefix tailTrace_3118238
  have hstable : (prefixWord ++ tailWord_3118238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118238).length < 2 ^ (prefixWord ++ tailWord_3118238).sum := by decide
  have hdescent : baseEnd_3118238 < baseStart_3118238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118347 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 2, 5]
def baseStart_3118347 : Nat := 118140960795 + 3118347 * 2 ^ 59
def prefixEnd_3118347 : Nat := 4983230072969 + 3 ^ 40 * 3118347 * 2
def baseEnd_3118347 : Nat := 533736952835338728907163

theorem tailTrace_3118347 : CollatzResearch.WordTrace tailWord_3118347 prefixEnd_3118347 533736952835338728907163 := by
  unfold tailWord_3118347
  simp only [CollatzResearch.WordTrace]
  refine ⟨113735458833768865112545295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75823639222512576741696863 113735458833768865112545295)
  ·
    refine ⟨170603188250653297668817943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113735458833768865112545295 170603188250653297668817943)
    ·
      refine ⟨255904782375979946503226915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170603188250653297668817943 255904782375979946503226915)
      ·
        refine ⟨383857173563969919754840373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255904782375979946503226915 383857173563969919754840373)
        ·
          refine ⟨35986610021622179977016285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 383857173563969919754840373 35986610021622179977016285)
          ·
            refine ⟨13494978758108317491381107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35986610021622179977016285 13494978758108317491381107)
            ·
              refine ⟨20242468137162476237071661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13494978758108317491381107 20242468137162476237071661)
              ·
                refine ⟨7590925551435928588901873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20242468137162476237071661 7590925551435928588901873)
                ·
                  refine ⟨5693194163576946441676405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7590925551435928588901873 5693194163576946441676405)
                  ·
                    refine ⟨533736952835338728907163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5693194163576946441676405 533736952835338728907163)
                    ·
                      rfl

theorem cell23_3118347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 5].length) (baseStart_3118347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118347 prefixEnd_3118347 := by exact prefixLift 3118347
  have htrace : WordTrace (prefixWord ++ tailWord_3118347) baseStart_3118347 baseEnd_3118347 := by
    simpa [prefixWord, tailWord_3118347, baseEnd_3118347] using wordTrace_append hprefix tailTrace_3118347
  have hstable : (prefixWord ++ tailWord_3118347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118347).length < 2 ^ (prefixWord ++ tailWord_3118347).sum := by decide
  have hdescent : baseEnd_3118347 < baseStart_3118347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118368 : List Nat := [2, 1, 1, 5, 3, 2, 2, 2, 5]
def baseStart_3118368 : Nat := 118140960795 + 3118368 * 2 ^ 59
def prefixEnd_3118368 : Nat := 4983230072969 + 3 ^ 40 * 3118368 * 2
def baseEnd_3118368 : Nat := 177913515733306733839877

theorem tailTrace_3118368 : CollatzResearch.WordTrace tailWord_3118368 prefixEnd_3118368 177913515733306733839877 := by
  unfold tailWord_3118368
  simp only [CollatzResearch.WordTrace]
  refine ⟨56868112383346392849529879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75824149844461857132706505 56868112383346392849529879)
  ·
    refine ⟨85302168575019589274294819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56868112383346392849529879 85302168575019589274294819)
    ·
      refine ⟨127953252862529383911442229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85302168575019589274294819 127953252862529383911442229)
      ·
        refine ⟨11995617455862129741697709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127953252862529383911442229 11995617455862129741697709)
        ·
          refine ⟨4498356545948298653136641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11995617455862129741697709 4498356545948298653136641)
          ·
            refine ⟨3373767409461223989852481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4498356545948298653136641 3373767409461223989852481)
            ·
              refine ⟨2530325557095917992389361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3373767409461223989852481 2530325557095917992389361)
              ·
                refine ⟨1897744167821938494292021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2530325557095917992389361 1897744167821938494292021)
                ·
                  refine ⟨177913515733306733839877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1897744167821938494292021 177913515733306733839877)
                  ·
                    rfl

theorem cell23_3118368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 5].length) (baseStart_3118368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118368 prefixEnd_3118368 := by exact prefixLift 3118368
  have htrace : WordTrace (prefixWord ++ tailWord_3118368) baseStart_3118368 baseEnd_3118368 := by
    simpa [prefixWord, tailWord_3118368, baseEnd_3118368] using wordTrace_append hprefix tailTrace_3118368
  have hstable : (prefixWord ++ tailWord_3118368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118368).length < 2 ^ (prefixWord ++ tailWord_3118368).sum := by decide
  have hdescent : baseEnd_3118368 < baseStart_3118368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118384 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 2, 4, 2]
def baseStart_3118384 : Nat := 118140960795 + 3118384 * 2 ^ 59
def prefixEnd_3118384 : Nat := 4983230072969 + 3 ^ 40 * 3118384 * 2
def baseEnd_3118384 : Nat := 1601229857290232541958819

theorem tailTrace_3118384 : CollatzResearch.WordTrace tailWord_3118384 prefixEnd_3118384 1601229857290232541958819 := by
  unfold tailWord_3118384
  simp only [CollatzResearch.WordTrace]
  refine ⟨56868404167317410215821103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75824538889756546954428137 56868404167317410215821103)
  ·
    refine ⟨85302606250976115323731655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56868404167317410215821103 85302606250976115323731655)
    ·
      refine ⟨127953909376464172985597483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85302606250976115323731655 127953909376464172985597483)
      ·
        refine ⟨191930864064696259478396225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127953909376464172985597483 191930864064696259478396225)
        ·
          refine ⟨143948148048522194608797169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191930864064696259478396225 143948148048522194608797169)
          ·
            refine ⟨107961111036391645956597877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143948148048522194608797169 107961111036391645956597877)
            ·
              refine ⟨10121354159661716808431051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107961111036391645956597877 10121354159661716808431051)
              ·
                refine ⟨15182031239492575212646577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10121354159661716808431051 15182031239492575212646577)
                ·
                  refine ⟨11386523429619431409484933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15182031239492575212646577 11386523429619431409484933)
                  ·
                    refine ⟨2134973143053643389278425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11386523429619431409484933 2134973143053643389278425)
                    ·
                      refine ⟨1601229857290232541958819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2134973143053643389278425 1601229857290232541958819)
                      ·
                        rfl

theorem cell23_3118384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 4, 2].length) (baseStart_3118384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118384 prefixEnd_3118384 := by exact prefixLift 3118384
  have htrace : WordTrace (prefixWord ++ tailWord_3118384) baseStart_3118384 baseEnd_3118384 := by
    simpa [prefixWord, tailWord_3118384, baseEnd_3118384] using wordTrace_append hprefix tailTrace_3118384
  have hstable : (prefixWord ++ tailWord_3118384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118384).length < 2 ^ (prefixWord ++ tailWord_3118384).sum := by decide
  have hdescent : baseEnd_3118384 < baseStart_3118384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118394 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_3118394 : Nat := 118140960795 + 3118394 * 2 ^ 59
def prefixEnd_3118394 : Nat := 4983230072969 + 3 ^ 40 * 3118394 * 2
def baseEnd_3118394 : Nat := 533744997365592500944591

theorem tailTrace_3118394 : CollatzResearch.WordTrace tailWord_3118394 prefixEnd_3118394 533744997365592500944591 := by
  unfold tailWord_3118394
  simp only [CollatzResearch.WordTrace]
  refine ⟨28434293266149648034876559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75824782043065728093004157 28434293266149648034876559)
  ·
    refine ⟨42651439899224472052314839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28434293266149648034876559 42651439899224472052314839)
    ·
      refine ⟨63977159848836708078472259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42651439899224472052314839 63977159848836708078472259)
      ·
        refine ⟨95965739773255062117708389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63977159848836708078472259 95965739773255062117708389)
        ·
          refine ⟨17993576207485324147070323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95965739773255062117708389 17993576207485324147070323)
          ·
            refine ⟨26990364311227986220605485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17993576207485324147070323 26990364311227986220605485)
            ·
              refine ⟨10121386616710494832727057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26990364311227986220605485 10121386616710494832727057)
              ·
                refine ⟨7591039962532871124545293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10121386616710494832727057 7591039962532871124545293)
                ·
                  refine ⟨2846639985949826671704485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7591039962532871124545293 2846639985949826671704485)
                  ·
                    refine ⟨533744997365592500944591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2846639985949826671704485 533744997365592500944591)
                    ·
                      rfl

theorem cell23_3118394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_3118394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118394 prefixEnd_3118394 := by exact prefixLift 3118394
  have htrace : WordTrace (prefixWord ++ tailWord_3118394) baseStart_3118394 baseEnd_3118394 := by
    simpa [prefixWord, tailWord_3118394, baseEnd_3118394] using wordTrace_append hprefix tailTrace_3118394
  have hstable : (prefixWord ++ tailWord_3118394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118394).length < 2 ^ (prefixWord ++ tailWord_3118394).sum := by decide
  have hdescent : baseEnd_3118394 < baseStart_3118394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118401 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3118401 : Nat := 118140960795 + 3118401 * 2 ^ 59
def prefixEnd_3118401 : Nat := 4983230072969 + 3 ^ 40 * 3118401 * 2
def baseEnd_3118401 : Nat := 1601238586461358975446241

theorem tailTrace_3118401 : CollatzResearch.WordTrace tailWord_3118401 prefixEnd_3118401 1601238586461358975446241 := by
  unfold tailWord_3118401
  simp only [CollatzResearch.WordTrace]
  refine ⟨113737428375573232335011057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75824952250382154890007371 113737428375573232335011057)
  ·
    refine ⟨85303071281679924251258293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113737428375573232335011057 85303071281679924251258293)
    ·
      refine ⟨7997162932657492898555465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85303071281679924251258293 7997162932657492898555465)
      ·
        refine ⟨5997872199493119673916599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7997162932657492898555465 5997872199493119673916599)
        ·
          refine ⟨8996808299239679510874899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5997872199493119673916599 8996808299239679510874899)
          ·
            refine ⟨13495212448859519266312349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8996808299239679510874899 13495212448859519266312349)
            ·
              refine ⟨5060704668322319724867131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13495212448859519266312349 5060704668322319724867131)
              ·
                refine ⟨7591057002483479587300697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060704668322319724867131 7591057002483479587300697)
                ·
                  refine ⟨5693292751862609690475523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7591057002483479587300697 5693292751862609690475523)
                  ·
                    refine ⟨8539939127793914535713285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5693292751862609690475523 8539939127793914535713285)
                    ·
                      refine ⟨1601238586461358975446241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8539939127793914535713285 1601238586461358975446241)
                      ·
                        rfl

theorem cell23_3118401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3118401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118401 prefixEnd_3118401 := by exact prefixLift 3118401
  have htrace : WordTrace (prefixWord ++ tailWord_3118401) baseStart_3118401 baseEnd_3118401 := by
    simpa [prefixWord, tailWord_3118401, baseEnd_3118401] using wordTrace_append hprefix tailTrace_3118401
  have hstable : (prefixWord ++ tailWord_3118401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118401).length < 2 ^ (prefixWord ++ tailWord_3118401).sum := by decide
  have hdescent : baseEnd_3118401 < baseStart_3118401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118461 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 2, 3, 2]
def baseStart_3118461 : Nat := 118140960795 + 3118461 * 2 ^ 59
def prefixEnd_3118461 : Nat := 4983230072969 + 3 ^ 40 * 3118461 * 2
def baseEnd_3118461 : Nat := 1601269395300628740695965

theorem tailTrace_3118461 : CollatzResearch.WordTrace tailWord_3118461 prefixEnd_3118461 1601269395300628740695965 := by
  unfold tailWord_3118461
  simp only [CollatzResearch.WordTrace]
  refine ⟨113739616755355862582195237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75826411170237241721463491 113739616755355862582195237)
  ·
    refine ⟨21326178141629224234161607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113739616755355862582195237 21326178141629224234161607)
    ·
      refine ⟨31989267212443836351242411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21326178141629224234161607 31989267212443836351242411)
      ·
        refine ⟨47983900818665754526863617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31989267212443836351242411 47983900818665754526863617)
        ·
          refine ⟨35987925613999315895147713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47983900818665754526863617 35987925613999315895147713)
          ·
            refine ⟨26990944210499486921360785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35987925613999315895147713 26990944210499486921360785)
            ·
              refine ⟨20243208157874615191020589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26990944210499486921360785 20243208157874615191020589)
              ·
                refine ⟨7591203059202980696632721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20243208157874615191020589 7591203059202980696632721)
                ·
                  refine ⟨5693402294402235522474541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7591203059202980696632721 5693402294402235522474541)
                  ·
                    refine ⟨2135025860400838320927953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5693402294402235522474541 2135025860400838320927953)
                    ·
                      refine ⟨1601269395300628740695965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135025860400838320927953 1601269395300628740695965)
                      ·
                        rfl

theorem cell23_3118461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_3118461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118461 prefixEnd_3118461 := by exact prefixLift 3118461
  have htrace : WordTrace (prefixWord ++ tailWord_3118461) baseStart_3118461 baseEnd_3118461 := by
    simpa [prefixWord, tailWord_3118461, baseEnd_3118461] using wordTrace_append hprefix tailTrace_3118461
  have hstable : (prefixWord ++ tailWord_3118461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118461).length < 2 ^ (prefixWord ++ tailWord_3118461).sum := by decide
  have hdescent : baseEnd_3118461 < baseStart_3118461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118521 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 4]
def baseStart_3118521 : Nat := 118140960795 + 3118521 * 2 ^ 59
def prefixEnd_3118521 : Nat := 4983230072969 + 3 ^ 40 * 3118521 * 2
def baseEnd_3118521 : Nat := 1601300204139898505945689

theorem tailTrace_3118521 : CollatzResearch.WordTrace tailWord_3118521 prefixEnd_3118521 1601300204139898505945689 := by
  unfold tailWord_3118521
  simp only [CollatzResearch.WordTrace]
  refine ⟨113741805135138492829379417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75827870090092328552919611 113741805135138492829379417)
  ·
    refine ⟨85306353851353869622034563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113741805135138492829379417 85306353851353869622034563)
    ·
      refine ⟨127959530777030804433051845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85306353851353869622034563 127959530777030804433051845)
      ·
        refine ⟨23992412020693275831197221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127959530777030804433051845 23992412020693275831197221)
        ·
          refine ⟨4498577253879989218349479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23992412020693275831197221 4498577253879989218349479)
          ·
            refine ⟨6747865880819983827524219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498577253879989218349479 6747865880819983827524219)
            ·
              refine ⟨10121798821229975741286329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6747865880819983827524219 10121798821229975741286329)
              ·
                refine ⟨7591349115922481805964747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10121798821229975741286329 7591349115922481805964747)
                ·
                  refine ⟨11387023673883722708947121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7591349115922481805964747 11387023673883722708947121)
                  ·
                    refine ⟨8540267755412792031710341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11387023673883722708947121 8540267755412792031710341)
                    ·
                      refine ⟨1601300204139898505945689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8540267755412792031710341 1601300204139898505945689)
                      ·
                        rfl

theorem cell23_3118521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_3118521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118521 prefixEnd_3118521 := by exact prefixLift 3118521
  have htrace : WordTrace (prefixWord ++ tailWord_3118521) baseStart_3118521 baseEnd_3118521 := by
    simpa [prefixWord, tailWord_3118521, baseEnd_3118521] using wordTrace_append hprefix tailTrace_3118521
  have hstable : (prefixWord ++ tailWord_3118521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118521).length < 2 ^ (prefixWord ++ tailWord_3118521).sum := by decide
  have hdescent : baseEnd_3118521 < baseStart_3118521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118525 : List Nat := [1, 4, 1, 2, 2, 1, 2, 5, 1, 2, 2]
def baseStart_3118525 : Nat := 118140960795 + 3118525 * 2 ^ 59
def prefixEnd_3118525 : Nat := 4983230072969 + 3 ^ 40 * 3118525 * 2
def baseEnd_3118525 : Nat := 1601302258062516490295671

theorem tailTrace_3118525 : CollatzResearch.WordTrace tailWord_3118525 prefixEnd_3118525 1601302258062516490295671 := by
  unfold tailWord_3118525
  simp only [CollatzResearch.WordTrace]
  refine ⟨113741951027124001512525029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75827967351416001008350019 113741951027124001512525029)
  ·
    refine ⟨21326615817585750283598443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113741951027124001512525029 21326615817585750283598443)
    ·
      refine ⟨31989923726378625425397665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21326615817585750283598443 31989923726378625425397665)
      ·
        refine ⟨23992442794783969069048249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31989923726378625425397665 23992442794783969069048249)
        ·
          refine ⟨17994332096087976801786187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23992442794783969069048249 17994332096087976801786187)
          ·
            refine ⟨26991498144131965202679281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17994332096087976801786187 26991498144131965202679281)
            ·
              refine ⟨20243623608098973902009461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26991498144131965202679281 20243623608098973902009461)
              ·
                refine ⟨1897839713259278803313387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20243623608098973902009461 1897839713259278803313387)
                ·
                  refine ⟨2846759569888918204970081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897839713259278803313387 2846759569888918204970081)
                  ·
                    refine ⟨2135069677416688653727561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2846759569888918204970081 2135069677416688653727561)
                    ·
                      refine ⟨1601302258062516490295671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135069677416688653727561 1601302258062516490295671)
                      ·
                        rfl

theorem cell23_3118525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_3118525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118525 prefixEnd_3118525 := by exact prefixLift 3118525
  have htrace : WordTrace (prefixWord ++ tailWord_3118525) baseStart_3118525 baseEnd_3118525 := by
    simpa [prefixWord, tailWord_3118525, baseEnd_3118525] using wordTrace_append hprefix tailTrace_3118525
  have hstable : (prefixWord ++ tailWord_3118525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118525).length < 2 ^ (prefixWord ++ tailWord_3118525).sum := by decide
  have hdescent : baseEnd_3118525 < baseStart_3118525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118527 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 4, 7]
def baseStart_3118527 : Nat := 118140960795 + 3118527 * 2 ^ 59
def prefixEnd_3118527 : Nat := 4983230072969 + 3 ^ 40 * 3118527 * 2
def baseEnd_3118527 : Nat := 533767761674608494156887

theorem tailTrace_3118527 : CollatzResearch.WordTrace tailWord_3118527 prefixEnd_3118527 533767761674608494156887 := by
  unfold tailWord_3118527
  simp only [CollatzResearch.WordTrace]
  refine ⟨113742023973116755854097835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75828015982077837236065223 113742023973116755854097835)
  ·
    refine ⟨170613035959675133781146753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113742023973116755854097835 170613035959675133781146753)
    ·
      refine ⟨127959776969756350335860065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170613035959675133781146753 127959776969756350335860065)
      ·
        refine ⟨95969832727317262751895049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127959776969756350335860065 95969832727317262751895049)
        ·
          refine ⟨71977374545487947063921287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95969832727317262751895049 71977374545487947063921287)
          ·
            refine ⟨107966061818231920595881931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71977374545487947063921287 107966061818231920595881931)
            ·
              refine ⟨161949092727347880893822897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107966061818231920595881931 161949092727347880893822897)
              ·
                refine ⟨121461819545510910670367173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161949092727347880893822897 121461819545510910670367173)
                ·
                  refine ⟨22774091164783295750693845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121461819545510910670367173 22774091164783295750693845)
                  ·
                    refine ⟨533767761674608494156887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22774091164783295750693845 533767761674608494156887)
                    ·
                      rfl

theorem cell23_3118527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_3118527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118527 prefixEnd_3118527 := by exact prefixLift 3118527
  have htrace : WordTrace (prefixWord ++ tailWord_3118527) baseStart_3118527 baseEnd_3118527 := by
    simpa [prefixWord, tailWord_3118527, baseEnd_3118527] using wordTrace_append hprefix tailTrace_3118527
  have hstable : (prefixWord ++ tailWord_3118527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118527).length < 2 ^ (prefixWord ++ tailWord_3118527).sum := by decide
  have hdescent : baseEnd_3118527 < baseStart_3118527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118542 : List Nat := [4, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2]
def baseStart_3118542 : Nat := 118140960795 + 3118542 * 2 ^ 59
def prefixEnd_3118542 : Nat := 4983230072969 + 3 ^ 40 * 3118542 * 2
def baseEnd_3118542 : Nat := 1601310987233642923783093

theorem tailTrace_3118542 : CollatzResearch.WordTrace tailWord_3118542 prefixEnd_3118542 1601310987233642923783093 := by
  unfold tailWord_3118542
  simp only [CollatzResearch.WordTrace]
  refine ⟨14217821383507801676986735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75828380712041608943929253 14217821383507801676986735)
  ·
    refine ⟨21326732075261702515480103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14217821383507801676986735 21326732075261702515480103)
    ·
      refine ⟨31990098112892553773220155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21326732075261702515480103 31990098112892553773220155)
      ·
        refine ⟨47985147169338830659830233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31990098112892553773220155 47985147169338830659830233)
        ·
          refine ⟨35988860377004122994872675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47985147169338830659830233 35988860377004122994872675)
          ·
            refine ⟨53983290565506184492309013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35988860377004122994872675 53983290565506184492309013)
            ·
              refine ⟨2530466745258102398076985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53983290565506184492309013 2530466745258102398076985)
              ·
                refine ⟨1897850058943576798557739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2530466745258102398076985 1897850058943576798557739)
                ·
                  refine ⟨2846775088415365197836609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897850058943576798557739 2846775088415365197836609)
                  ·
                    refine ⟨2135081316311523898377457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2846775088415365197836609 2135081316311523898377457)
                    ·
                      refine ⟨1601310987233642923783093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135081316311523898377457 1601310987233642923783093)
                      ·
                        rfl

theorem cell23_3118542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_3118542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118542 prefixEnd_3118542 := by exact prefixLift 3118542
  have htrace : WordTrace (prefixWord ++ tailWord_3118542) baseStart_3118542 baseEnd_3118542 := by
    simpa [prefixWord, tailWord_3118542, baseEnd_3118542] using wordTrace_append hprefix tailTrace_3118542
  have hstable : (prefixWord ++ tailWord_3118542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118542).length < 2 ^ (prefixWord ++ tailWord_3118542).sum := by decide
  have hdescent : baseEnd_3118542 < baseStart_3118542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118548 : List Nat := [2, 4, 1, 2, 4, 1, 1, 8]
def baseStart_3118548 : Nat := 118140960795 + 3118548 * 2 ^ 59
def prefixEnd_3118548 : Nat := 4983230072969 + 3 ^ 40 * 3118548 * 2
def baseEnd_3118548 : Nat := 59307928448798885196595

theorem tailTrace_3118548 : CollatzResearch.WordTrace tailWord_3118548 prefixEnd_3118548 59307928448798885196595 := by
  unfold tailWord_3118548
  simp only [CollatzResearch.WordTrace]
  refine ⟨56871394953020338220306149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75828526604027117627074865 56871394953020338220306149)
  ·
    refine ⟨10663386553691313416307403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56871394953020338220306149 10663386553691313416307403)
    ·
      refine ⟨15995079830536970124461105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10663386553691313416307403 15995079830536970124461105)
      ·
        refine ⟨11996309872902727593345829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15995079830536970124461105 11996309872902727593345829)
        ·
          refine ⟨2249308101169261423752343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11996309872902727593345829 2249308101169261423752343)
          ·
            refine ⟨3373962151753892135628515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2249308101169261423752343 3373962151753892135628515)
            ·
              refine ⟨5060943227630838203442773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373962151753892135628515 5060943227630838203442773)
              ·
                refine ⟨59307928448798885196595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5060943227630838203442773 59307928448798885196595)
                ·
                  rfl

theorem cell23_3118548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 8].length) (baseStart_3118548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118548 prefixEnd_3118548 := by exact prefixLift 3118548
  have htrace : WordTrace (prefixWord ++ tailWord_3118548) baseStart_3118548 baseEnd_3118548 := by
    simpa [prefixWord, tailWord_3118548, baseEnd_3118548] using wordTrace_append hprefix tailTrace_3118548
  have hstable : (prefixWord ++ tailWord_3118548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118548).length < 2 ^ (prefixWord ++ tailWord_3118548).sum := by decide
  have hdescent : baseEnd_3118548 < baseStart_3118548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118568 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_3118568 : Nat := 118140960795 + 3118568 * 2 ^ 59
def prefixEnd_3118568 : Nat := 4983230072969 + 3 ^ 40 * 3118568 * 2
def baseEnd_3118568 : Nat := 1601324337730659822057973

theorem tailTrace_3118568 : CollatzResearch.WordTrace tailWord_3118568 prefixEnd_3118568 1601324337730659822057973 := by
  unfold tailWord_3118568
  simp only [CollatzResearch.WordTrace]
  refine ⟨56871759682984109928170179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75829012910645479904226905 56871759682984109928170179)
  ·
    refine ⟨85307639524476164892255269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56871759682984109928170179 85307639524476164892255269)
    ·
      refine ⟨15995182410839280917297863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85307639524476164892255269 15995182410839280917297863)
      ·
        refine ⟨23992773616258921375946795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15995182410839280917297863 23992773616258921375946795)
        ·
          refine ⟨35989160424388382063920193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23992773616258921375946795 35989160424388382063920193)
          ·
            refine ⟨26991870318291286547940145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35989160424388382063920193 26991870318291286547940145)
            ·
              refine ⟨20243902738718464910955109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26991870318291286547940145 20243902738718464910955109)
              ·
                refine ⟨3795731763509712170804083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20243902738718464910955109 3795731763509712170804083)
                ·
                  refine ⟨5693597645264568256206125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795731763509712170804083 5693597645264568256206125)
                  ·
                    refine ⟨2135099116974213096077297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5693597645264568256206125 2135099116974213096077297)
                    ·
                      refine ⟨1601324337730659822057973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135099116974213096077297 1601324337730659822057973)
                      ·
                        rfl

theorem cell23_3118568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_3118568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118568 prefixEnd_3118568 := by exact prefixLift 3118568
  have htrace : WordTrace (prefixWord ++ tailWord_3118568) baseStart_3118568 baseEnd_3118568 := by
    simpa [prefixWord, tailWord_3118568, baseEnd_3118568] using wordTrace_append hprefix tailTrace_3118568
  have hstable : (prefixWord ++ tailWord_3118568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118568).length < 2 ^ (prefixWord ++ tailWord_3118568).sum := by decide
  have hdescent : baseEnd_3118568 < baseStart_3118568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118574 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3118574 : Nat := 118140960795 + 3118574 * 2 ^ 59
def prefixEnd_3118574 : Nat := 4983230072969 + 3 ^ 40 * 3118574 * 2
def baseEnd_3118574 : Nat := 533775806204862266194315

theorem tailTrace_3118574 : CollatzResearch.WordTrace tailWord_3118574 prefixEnd_3118574 533775806204862266194315 := by
  unfold tailWord_3118574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14217967275493310360132347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75829158802630988587372517 14217967275493310360132347)
  ·
    refine ⟨21326950913239965540198521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14217967275493310360132347 21326950913239965540198521)
    ·
      refine ⟨15995213184929974155148891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21326950913239965540198521 15995213184929974155148891)
      ·
        refine ⟨23992819777394961232723337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15995213184929974155148891 23992819777394961232723337)
        ·
          refine ⟨17994614833046220924542503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23992819777394961232723337 17994614833046220924542503)
          ·
            refine ⟨26991922249569331386813755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17994614833046220924542503 26991922249569331386813755)
            ·
              refine ⟨40487883374353997080220633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26991922249569331386813755 40487883374353997080220633)
              ·
                refine ⟨30365912530765497810165475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40487883374353997080220633 30365912530765497810165475)
                ·
                  refine ⟨45548868796148246715248213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30365912530765497810165475 45548868796148246715248213)
                  ·
                    refine ⟨533775806204862266194315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45548868796148246715248213 533775806204862266194315)
                    ·
                      rfl

theorem cell23_3118574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3118574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118574 prefixEnd_3118574 := by exact prefixLift 3118574
  have htrace : WordTrace (prefixWord ++ tailWord_3118574) baseStart_3118574 baseEnd_3118574 := by
    simpa [prefixWord, tailWord_3118574, baseEnd_3118574] using wordTrace_append hprefix tailTrace_3118574
  have hstable : (prefixWord ++ tailWord_3118574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118574).length < 2 ^ (prefixWord ++ tailWord_3118574).sum := by decide
  have hdescent : baseEnd_3118574 < baseStart_3118574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118641 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 1, 7, 2]
def baseStart_3118641 : Nat := 118140960795 + 3118641 * 2 ^ 59
def prefixEnd_3118641 : Nat := 4983230072969 + 3 ^ 40 * 3118641 * 2
def baseEnd_3118641 : Nat := 1601361821818438036445137

theorem tailTrace_3118641 : CollatzResearch.WordTrace tailWord_3118641 prefixEnd_3118641 1601361821818438036445137 := by
  unfold tailWord_3118641
  simp only [CollatzResearch.WordTrace]
  refine ⟨113746181894703753323747777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75830787929802502215831851 113746181894703753323747777)
  ·
    refine ⟨85309636421027814992810833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113746181894703753323747777 85309636421027814992810833)
    ·
      refine ⟨63982227315770861244608125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85309636421027814992810833 63982227315770861244608125)
      ·
        refine ⟨23993335243414072966728047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63982227315770861244608125 23993335243414072966728047)
        ·
          refine ⟨35990002865121109450092071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23993335243414072966728047 35990002865121109450092071)
          ·
            refine ⟨53985004297681664175138107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35990002865121109450092071 53985004297681664175138107)
            ·
              refine ⟨80977506446522496262707161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53985004297681664175138107 80977506446522496262707161)
              ·
                refine ⟨60733129834891872197030371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80977506446522496262707161 60733129834891872197030371)
                ·
                  refine ⟨91099694752337808295545557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60733129834891872197030371 91099694752337808295545557)
                  ·
                    refine ⟨2135149095757917381926849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 91099694752337808295545557 2135149095757917381926849)
                    ·
                      refine ⟨1601361821818438036445137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135149095757917381926849 1601361821818438036445137)
                      ·
                        rfl

theorem cell23_3118641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_3118641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118641 prefixEnd_3118641 := by exact prefixLift 3118641
  have htrace : WordTrace (prefixWord ++ tailWord_3118641) baseStart_3118641 baseEnd_3118641 := by
    simpa [prefixWord, tailWord_3118641, baseEnd_3118641] using wordTrace_append hprefix tailTrace_3118641
  have hstable : (prefixWord ++ tailWord_3118641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118641).length < 2 ^ (prefixWord ++ tailWord_3118641).sum := by decide
  have hdescent : baseEnd_3118641 < baseStart_3118641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118671 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 1, 6, 2]
def baseStart_3118671 : Nat := 118140960795 + 3118671 * 2 ^ 59
def prefixEnd_3118671 : Nat := 4983230072969 + 3 ^ 40 * 3118671 * 2
def baseEnd_3118671 : Nat := 1601377226238072919069999

theorem tailTrace_3118671 : CollatzResearch.WordTrace tailWord_3118671 prefixEnd_3118671 1601377226238072919069999 := by
  unfold tailWord_3118671
  simp only [CollatzResearch.WordTrace]
  refine ⟨113747276084595068447339867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75831517389730045631559911 113747276084595068447339867)
  ·
    refine ⟨170620914126892602671009801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113747276084595068447339867 170620914126892602671009801)
    ·
      refine ⟨127965685595169452003257351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170620914126892602671009801 127965685595169452003257351)
      ·
        refine ⟨191948528392754178004886027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127965685595169452003257351 191948528392754178004886027)
        ·
          refine ⟨287922792589131267007329041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191948528392754178004886027 287922792589131267007329041)
          ·
            refine ⟨215942094441848450255496781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287922792589131267007329041 215942094441848450255496781)
            ·
              refine ⟨80978285415693168845811293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215942094441848450255496781 80978285415693168845811293)
              ·
                refine ⟨30366857030884938317179235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80978285415693168845811293 30366857030884938317179235)
                ·
                  refine ⟨45550285546327407475768853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30366857030884938317179235 45550285546327407475768853)
                  ·
                    refine ⟨2135169634984097225426665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45550285546327407475768853 2135169634984097225426665)
                    ·
                      refine ⟨1601377226238072919069999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135169634984097225426665 1601377226238072919069999)
                      ·
                        rfl

theorem cell23_3118671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 6, 2].length) (baseStart_3118671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118671 prefixEnd_3118671 := by exact prefixLift 3118671
  have htrace : WordTrace (prefixWord ++ tailWord_3118671) baseStart_3118671 baseEnd_3118671 := by
    simpa [prefixWord, tailWord_3118671, baseEnd_3118671] using wordTrace_append hprefix tailTrace_3118671
  have hstable : (prefixWord ++ tailWord_3118671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118671).length < 2 ^ (prefixWord ++ tailWord_3118671).sum := by decide
  have hdescent : baseEnd_3118671 < baseStart_3118671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118681 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 3, 4]
def baseStart_3118681 : Nat := 118140960795 + 3118681 * 2 ^ 59
def prefixEnd_3118681 : Nat := 4983230072969 + 3 ^ 40 * 3118681 * 2
def baseEnd_3118681 : Nat := 533794120348205959981651

theorem tailTrace_3118681 : CollatzResearch.WordTrace tailWord_3118681 prefixEnd_3118681 533794120348205959981651 := by
  unfold tailWord_3118681
  simp only [CollatzResearch.WordTrace]
  refine ⟨113747640814558840155203897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75831760543039226770135931 113747640814558840155203897)
  ·
    refine ⟨85310730610919130116402923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113747640814558840155203897 85310730610919130116402923)
    ·
      refine ⟨127966095916378695174604385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85310730610919130116402923 127966095916378695174604385)
      ·
        refine ⟨95974571937284021380953289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127966095916378695174604385 95974571937284021380953289)
        ·
          refine ⟨71980928952963016035714967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95974571937284021380953289 71980928952963016035714967)
          ·
            refine ⟨107971393429444524053572451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71980928952963016035714967 107971393429444524053572451)
            ·
              refine ⟨161957090144166786080358677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107971393429444524053572451 161957090144166786080358677)
              ·
                refine ⟨7591738600507818097516813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161957090144166786080358677 7591738600507818097516813)
                ·
                  refine ⟨2846901975190431786568805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7591738600507818097516813 2846901975190431786568805)
                  ·
                    refine ⟨533794120348205959981651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2846901975190431786568805 533794120348205959981651)
                    ·
                      rfl

theorem cell23_3118681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 4].length) (baseStart_3118681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118681 prefixEnd_3118681 := by exact prefixLift 3118681
  have htrace : WordTrace (prefixWord ++ tailWord_3118681) baseStart_3118681 baseEnd_3118681 := by
    simpa [prefixWord, tailWord_3118681, baseEnd_3118681] using wordTrace_append hprefix tailTrace_3118681
  have hstable : (prefixWord ++ tailWord_3118681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118681).length < 2 ^ (prefixWord ++ tailWord_3118681).sum := by decide
  have hdescent : baseEnd_3118681 < baseStart_3118681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118765 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_3118765 : Nat := 118140960795 + 3118765 * 2 ^ 59
def prefixEnd_3118765 : Nat := 4983230072969 + 3 ^ 40 * 3118765 * 2
def baseEnd_3118765 : Nat := 1601425493419595551294567

theorem tailTrace_3118765 : CollatzResearch.WordTrace tailWord_3118765 prefixEnd_3118765 1601425493419595551294567 := by
  unfold tailWord_3118765
  simp only [CollatzResearch.WordTrace]
  refine ⟨113750704546254522501261749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75833803030836348334174499 113750704546254522501261749)
  ·
    refine ⟨10664128551211361484493289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113750704546254522501261749 10664128551211361484493289)
    ·
      refine ⟨7998096413408521113369967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10664128551211361484493289 7998096413408521113369967)
      ·
        refine ⟨11997144620112781670054951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7998096413408521113369967 11997144620112781670054951)
        ·
          refine ⟨17995716930169172505082427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11997144620112781670054951 17995716930169172505082427)
          ·
            refine ⟨26993575395253758757623641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17995716930169172505082427 26993575395253758757623641)
            ·
              refine ⟨20245181546440319068217731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26993575395253758757623641 20245181546440319068217731)
              ·
                refine ⟨30367772319660478602326597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20245181546440319068217731 30367772319660478602326597)
                ·
                  refine ⟨5693957309936339737936237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30367772319660478602326597 5693957309936339737936237)
                  ·
                    refine ⟨2135233991226127401726089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5693957309936339737936237 2135233991226127401726089)
                    ·
                      refine ⟨1601425493419595551294567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135233991226127401726089 1601425493419595551294567)
                      ·
                        rfl

theorem cell23_3118765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_3118765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118765 prefixEnd_3118765 := by exact prefixLift 3118765
  have htrace : WordTrace (prefixWord ++ tailWord_3118765) baseStart_3118765 baseEnd_3118765 := by
    simpa [prefixWord, tailWord_3118765, baseEnd_3118765] using wordTrace_append hprefix tailTrace_3118765
  have hstable : (prefixWord ++ tailWord_3118765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118765).length < 2 ^ (prefixWord ++ tailWord_3118765).sum := by decide
  have hdescent : baseEnd_3118765 < baseStart_3118765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118791 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_3118791 : Nat := 118140960795 + 3118791 * 2 ^ 59
def prefixEnd_3118791 : Nat := 4983230072969 + 3 ^ 40 * 3118791 * 2
def baseEnd_3118791 : Nat := 1601438843916612449569447

theorem tailTrace_3118791 : CollatzResearch.WordTrace tailWord_3118791 prefixEnd_3118791 1601438843916612449569447 := by
  unfold tailWord_3118791
  simp only [CollatzResearch.WordTrace]
  refine ⟨113751652844160328941708227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75834435229440219294472151 113751652844160328941708227)
  ·
    refine ⟨170627479266240493412562341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113751652844160328941708227 170627479266240493412562341)
    ·
      refine ⟨31992652362420092514855439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170627479266240493412562341 31992652362420092514855439)
      ·
        refine ⟨47988978543630138772283159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31992652362420092514855439 47988978543630138772283159)
        ·
          refine ⟨71983467815445208158424739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47988978543630138772283159 71983467815445208158424739)
          ·
            refine ⟨107975201723167812237637109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71983467815445208158424739 107975201723167812237637109)
            ·
              refine ⟨10122675161546982397278479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107975201723167812237637109 10122675161546982397278479)
              ·
                refine ⟨15184012742320473595917719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10122675161546982397278479 15184012742320473595917719)
                ·
                  refine ⟨22776019113480710393876579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15184012742320473595917719 22776019113480710393876579)
                  ·
                    refine ⟨34164028670221065590814869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22776019113480710393876579 34164028670221065590814869)
                    ·
                      refine ⟨1601438843916612449569447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34164028670221065590814869 1601438843916612449569447)
                      ·
                        rfl

theorem cell23_3118791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_3118791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118791 prefixEnd_3118791 := by exact prefixLift 3118791
  have htrace : WordTrace (prefixWord ++ tailWord_3118791) baseStart_3118791 baseEnd_3118791 := by
    simpa [prefixWord, tailWord_3118791, baseEnd_3118791] using wordTrace_append hprefix tailTrace_3118791
  have hstable : (prefixWord ++ tailWord_3118791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118791).length < 2 ^ (prefixWord ++ tailWord_3118791).sum := by decide
  have hdescent : baseEnd_3118791 < baseStart_3118791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118801 : List Nat := [1, 2, 2, 1, 2, 5, 1, 9]
def baseStart_3118801 : Nat := 118140960795 + 3118801 * 2 ^ 59
def prefixEnd_3118801 : Nat := 4983230072969 + 3 ^ 40 * 3118801 * 2
def baseEnd_3118801 : Nat := 59312739952709533720163

theorem tailTrace_3118801 : CollatzResearch.WordTrace tailWord_3118801 prefixEnd_3118801 59312739952709533720163 := by
  unfold tailWord_3118801
  simp only [CollatzResearch.WordTrace]
  refine ⟨113752017574124100649572257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75834678382749400433048171 113752017574124100649572257)
  ·
    refine ⟨85314013180593075487179193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113752017574124100649572257 85314013180593075487179193)
    ·
      refine ⟨63985509885444806615384395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85314013180593075487179193 63985509885444806615384395)
      ·
        refine ⟨95978264828167209923076593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63985509885444806615384395 95978264828167209923076593)
        ·
          refine ⟨71983698621125407442307445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95978264828167209923076593 71983698621125407442307445)
          ·
            refine ⟨6748471745730506947716323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71983698621125407442307445 6748471745730506947716323)
            ·
              refine ⟨10122707618595760421574485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6748471745730506947716323 10122707618595760421574485)
              ·
                refine ⟨59312739952709533720163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10122707618595760421574485 59312739952709533720163)
                ·
                  rfl

theorem cell23_3118801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 9].length) (baseStart_3118801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118801 prefixEnd_3118801 := by exact prefixLift 3118801
  have htrace : WordTrace (prefixWord ++ tailWord_3118801) baseStart_3118801 baseEnd_3118801 := by
    simpa [prefixWord, tailWord_3118801, baseEnd_3118801] using wordTrace_append hprefix tailTrace_3118801
  have hstable : (prefixWord ++ tailWord_3118801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118801).length < 2 ^ (prefixWord ++ tailWord_3118801).sum := by decide
  have hdescent : baseEnd_3118801 < baseStart_3118801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118829 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_3118829 : Nat := 118140960795 + 3118829 * 2 ^ 59
def prefixEnd_3118829 : Nat := 4983230072969 + 3 ^ 40 * 3118829 * 2
def baseEnd_3118829 : Nat := 1601458356181483300894273

theorem tailTrace_3118829 : CollatzResearch.WordTrace tailWord_3118829 prefixEnd_3118829 1601458356181483300894273 := by
  unfold tailWord_3118829
  simp only [CollatzResearch.WordTrace]
  refine ⟨113753038818022661431591541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75835359212015107621061027 113753038818022661431591541)
  ·
    refine ⟨10664347389189624509211707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113753038818022661431591541 10664347389189624509211707)
    ·
      refine ⟨15996521083784436763817561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10664347389189624509211707 15996521083784436763817561)
      ·
        refine ⟨11997390812838327572863171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15996521083784436763817561 11997390812838327572863171)
        ·
          refine ⟨17996086219257491359294757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11997390812838327572863171 17996086219257491359294757)
          ·
            refine ⟨3374266166110779629867767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17996086219257491359294757 3374266166110779629867767)
            ·
              refine ⟨5061399249166169444801651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374266166110779629867767 5061399249166169444801651)
              ·
                refine ⟨7592098873749254167202477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5061399249166169444801651 7592098873749254167202477)
                ·
                  refine ⟨2847037077655970312700929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7592098873749254167202477 2847037077655970312700929)
                  ·
                    refine ⟨2135277808241977734525697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2847037077655970312700929 2135277808241977734525697)
                    ·
                      refine ⟨1601458356181483300894273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135277808241977734525697 1601458356181483300894273)
                      ·
                        rfl

theorem cell23_3118829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_3118829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118829 prefixEnd_3118829 := by exact prefixLift 3118829
  have htrace : WordTrace (prefixWord ++ tailWord_3118829) baseStart_3118829 baseEnd_3118829 := by
    simpa [prefixWord, tailWord_3118829, baseEnd_3118829] using wordTrace_append hprefix tailTrace_3118829
  have hstable : (prefixWord ++ tailWord_3118829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118829).length < 2 ^ (prefixWord ++ tailWord_3118829).sum := by decide
  have hdescent : baseEnd_3118829 < baseStart_3118829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118831 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 2, 7]
def baseStart_3118831 : Nat := 118140960795 + 3118831 * 2 ^ 59
def prefixEnd_3118831 : Nat := 4983230072969 + 3 ^ 40 * 3118831 * 2
def baseEnd_3118831 : Nat := 533819794380930764356421

theorem tailTrace_3118831 : CollatzResearch.WordTrace tailWord_3118831 prefixEnd_3118831 533819794380930764356421 := by
  unfold tailWord_3118831
  simp only [CollatzResearch.WordTrace]
  refine ⟨113753111764015415773164347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75835407842676943848776231 113753111764015415773164347)
  ·
    refine ⟨170629667646023123659746521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113753111764015415773164347 170629667646023123659746521)
    ·
      refine ⟨127972250734517342744809891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170629667646023123659746521 127972250734517342744809891)
      ·
        refine ⟨191958376101776014117214837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127972250734517342744809891 191958376101776014117214837)
        ·
          refine ⟨17996097759541501323488891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191958376101776014117214837 17996097759541501323488891)
          ·
            refine ⟨26994146639312251985233337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17996097759541501323488891 26994146639312251985233337)
            ·
              refine ⟨20245609979484188988925003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26994146639312251985233337 20245609979484188988925003)
              ·
                refine ⟨30368414969226283483387505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20245609979484188988925003 30368414969226283483387505)
                ·
                  refine ⟨22776311226919712612540629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30368414969226283483387505 22776311226919712612540629)
                  ·
                    refine ⟨533819794380930764356421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22776311226919712612540629 533819794380930764356421)
                    ·
                      rfl

theorem cell23_3118831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_3118831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118831 prefixEnd_3118831 := by exact prefixLift 3118831
  have htrace : WordTrace (prefixWord ++ tailWord_3118831) baseStart_3118831 baseEnd_3118831 := by
    simpa [prefixWord, tailWord_3118831, baseEnd_3118831] using wordTrace_append hprefix tailTrace_3118831
  have hstable : (prefixWord ++ tailWord_3118831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118831).length < 2 ^ (prefixWord ++ tailWord_3118831).sum := by decide
  have hdescent : baseEnd_3118831 < baseStart_3118831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118898 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3118898 : Nat := 118140960795 + 3118898 * 2 ^ 59
def prefixEnd_3118898 : Nat := 4983230072969 + 3 ^ 40 * 3118898 * 2
def baseEnd_3118898 : Nat := 1601493786346643530931455

theorem tailTrace_3118898 : CollatzResearch.WordTrace tailWord_3118898 prefixEnd_3118898 1601493786346643530931455 := by
  unfold tailWord_3118898
  simp only [CollatzResearch.WordTrace]
  refine ⟨28438888863693171553963337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75837036969848457477235565 28438888863693171553963337)
  ·
    refine ⟨21329166647769878665472503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28438888863693171553963337 21329166647769878665472503)
    ·
      refine ⟨31993749971654817998208755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21329166647769878665472503 31993749971654817998208755)
      ·
        refine ⟨47990624957482226997313133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31993749971654817998208755 47990624957482226997313133)
        ·
          refine ⟨17996484359055835123992425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47990624957482226997313133 17996484359055835123992425)
          ·
            refine ⟨13497363269291876342994319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17996484359055835123992425 13497363269291876342994319)
            ·
              refine ⟨20246044903937814514491479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13497363269291876342994319 20246044903937814514491479)
              ·
                refine ⟨30369067355906721771737219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20246044903937814514491479 30369067355906721771737219)
                ·
                  refine ⟨45553601033860082657605829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30369067355906721771737219 45553601033860082657605829)
                  ·
                    refine ⟨8541300193848765498301093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45553601033860082657605829 8541300193848765498301093)
                    ·
                      refine ⟨1601493786346643530931455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8541300193848765498301093 1601493786346643530931455)
                      ·
                        rfl

theorem cell23_3118898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3118898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118898 prefixEnd_3118898 := by exact prefixLift 3118898
  have htrace : WordTrace (prefixWord ++ tailWord_3118898) baseStart_3118898 baseEnd_3118898 := by
    simpa [prefixWord, tailWord_3118898, baseEnd_3118898] using wordTrace_append hprefix tailTrace_3118898
  have hstable : (prefixWord ++ tailWord_3118898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118898).length < 2 ^ (prefixWord ++ tailWord_3118898).sum := by decide
  have hdescent : baseEnd_3118898 < baseStart_3118898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118938 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_3118938 : Nat := 118140960795 + 3118938 * 2 ^ 59
def prefixEnd_3118938 : Nat := 4983230072969 + 3 ^ 40 * 3118938 * 2
def baseEnd_3118938 : Nat := 533838108524274458143757

theorem tailTrace_3118938 : CollatzResearch.WordTrace tailWord_3118938 prefixEnd_3118938 533838108524274458143757 := by
  unfold tailWord_3118938
  simp only [CollatzResearch.WordTrace]
  refine ⟨28439253593656943261827367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75838009583085182031539645 28439253593656943261827367)
  ·
    refine ⟨42658880390485414892741051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28439253593656943261827367 42658880390485414892741051)
    ·
      refine ⟨63988320585728122339111577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42658880390485414892741051 63988320585728122339111577)
      ·
        refine ⟨47991240439296091754333683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63988320585728122339111577 47991240439296091754333683)
        ·
          refine ⟨71986860658944137631500525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47991240439296091754333683 71986860658944137631500525)
          ·
            refine ⟨26995072747104051611812697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71986860658944137631500525 26995072747104051611812697)
            ·
              refine ⟨20246304560328038708859523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26995072747104051611812697 20246304560328038708859523)
              ·
                refine ⟨30369456840492058063289285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20246304560328038708859523 30369456840492058063289285)
                ·
                  refine ⟨5694273157592260886866741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30369456840492058063289285 5694273157592260886866741)
                  ·
                    refine ⟨533838108524274458143757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5694273157592260886866741 533838108524274458143757)
                    ·
                      rfl

theorem cell23_3118938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_3118938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3118938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3118938 prefixEnd_3118938 := by exact prefixLift 3118938
  have htrace : WordTrace (prefixWord ++ tailWord_3118938) baseStart_3118938 baseEnd_3118938 := by
    simpa [prefixWord, tailWord_3118938, baseEnd_3118938] using wordTrace_append hprefix tailTrace_3118938
  have hstable : (prefixWord ++ tailWord_3118938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118938).length < 2 ^ (prefixWord ++ tailWord_3118938).sum := by decide
  have hdescent : baseEnd_3118938 < baseStart_3118938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119002 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_3119002 : Nat := 118140960795 + 3119002 * 2 ^ 59
def prefixEnd_3119002 : Nat := 4983230072969 + 3 ^ 40 * 3119002 * 2
def baseEnd_3119002 : Nat := 533849062778237041343659

theorem tailTrace_3119002 : CollatzResearch.WordTrace tailWord_3119002 prefixEnd_3119002 533849062778237041343659 := by
  unfold tailWord_3119002
  simp only [CollatzResearch.WordTrace]
  refine ⟨28439837161598977994409815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75839565764263941318426173 28439837161598977994409815)
  ·
    refine ⟨42659755742398466991614723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28439837161598977994409815 42659755742398466991614723)
    ·
      refine ⟨63989633613597700487422085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42659755742398466991614723 63989633613597700487422085)
      ·
        refine ⟨11998056302549568841391641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63989633613597700487422085 11998056302549568841391641)
        ·
          refine ⟨8998542226912176631043731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11998056302549568841391641 8998542226912176631043731)
          ·
            refine ⟨13497813340368264946565597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8998542226912176631043731 13497813340368264946565597)
            ·
              refine ⟨5061680002638099354962099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13497813340368264946565597 5061680002638099354962099)
              ·
                refine ⟨7592520003957149032443149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5061680002638099354962099 7592520003957149032443149)
                ·
                  refine ⟨2847195001483930887166181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7592520003957149032443149 2847195001483930887166181)
                  ·
                    refine ⟨533849062778237041343659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2847195001483930887166181 533849062778237041343659)
                    ·
                      rfl

theorem cell23_3119002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_3119002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119002 prefixEnd_3119002 := by exact prefixLift 3119002
  have htrace : WordTrace (prefixWord ++ tailWord_3119002) baseStart_3119002 baseEnd_3119002 := by
    simpa [prefixWord, tailWord_3119002, baseEnd_3119002] using wordTrace_append hprefix tailTrace_3119002
  have hstable : (prefixWord ++ tailWord_3119002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119002).length < 2 ^ (prefixWord ++ tailWord_3119002).sum := by decide
  have hdescent : baseEnd_3119002 < baseStart_3119002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119075 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 1, 6]
def baseStart_3119075 : Nat := 118140960795 + 3119075 * 2 ^ 59
def prefixEnd_3119075 : Nat := 4983230072969 + 3 ^ 40 * 3119075 * 2
def baseEnd_3119075 : Nat := 533861557474163112806047

theorem tailTrace_3119075 : CollatzResearch.WordTrace tailWord_3119075 prefixEnd_3119075 533861557474163112806047 := by
  unfold tailWord_3119075
  simp only [CollatzResearch.WordTrace]
  refine ⟨113762011175131445445046679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75841340783420963630031119 113762011175131445445046679)
  ·
    refine ⟨170643016762697168167570019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113762011175131445445046679 170643016762697168167570019)
    ·
      refine ⟨255964525144045752251355029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170643016762697168167570019 255964525144045752251355029)
      ·
        refine ⟨11998337116127144636782267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255964525144045752251355029 11998337116127144636782267)
        ·
          refine ⟨17997505674190716955173401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11998337116127144636782267 17997505674190716955173401)
          ·
            refine ⟨13498129255643037716380051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17997505674190716955173401 13498129255643037716380051)
            ·
              refine ⟨20247193883464556574570077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13498129255643037716380051 20247193883464556574570077)
              ·
                refine ⟨7592697706299208715463779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20247193883464556574570077 7592697706299208715463779)
                ·
                  refine ⟨11389046559448813073195669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7592697706299208715463779 11389046559448813073195669)
                  ·
                    refine ⟨533861557474163112806047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11389046559448813073195669 533861557474163112806047)
                    ·
                      rfl

theorem cell23_3119075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 6].length) (baseStart_3119075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119075 prefixEnd_3119075 := by exact prefixLift 3119075
  have htrace : WordTrace (prefixWord ++ tailWord_3119075) baseStart_3119075 baseEnd_3119075 := by
    simpa [prefixWord, tailWord_3119075, baseEnd_3119075] using wordTrace_append hprefix tailTrace_3119075
  have hstable : (prefixWord ++ tailWord_3119075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119075).length < 2 ^ (prefixWord ++ tailWord_3119075).sum := by decide
  have hdescent : baseEnd_3119075 < baseStart_3119075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119082 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_3119082 : Nat := 118140960795 + 3119082 * 2 ^ 59
def prefixEnd_3119082 : Nat := 4983230072969 + 3 ^ 40 * 3119082 * 2
def baseEnd_3119082 : Nat := 1601588266787070811030609

theorem tailTrace_3119082 : CollatzResearch.WordTrace tailWord_3119082 prefixEnd_3119082 1601588266787070811030609 := by
  unfold tailWord_3119082
  simp only [CollatzResearch.WordTrace]
  refine ⟨28440566621526521410137875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75841510990737390427034333 28440566621526521410137875)
  ·
    refine ⟨42660849932289782115206813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28440566621526521410137875 42660849932289782115206813)
    ·
      refine ⟨15997818724608668293202555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42660849932289782115206813 15997818724608668293202555)
      ·
        refine ⟨23996728086913002439803833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15997818724608668293202555 23996728086913002439803833)
        ·
          refine ⟨17997546065184751829852875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23996728086913002439803833 17997546065184751829852875)
          ·
            refine ⟨26996319097777127744779313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17997546065184751829852875 26996319097777127744779313)
            ·
              refine ⟨20247239323332845808584485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26996319097777127744779313 20247239323332845808584485)
              ·
                refine ⟨3796357373124908589109591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20247239323332845808584485 3796357373124908589109591)
                ·
                  refine ⟨5694536059687362883664387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3796357373124908589109591 5694536059687362883664387)
                  ·
                    refine ⟨8541804089531044325496581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5694536059687362883664387 8541804089531044325496581)
                    ·
                      refine ⟨1601588266787070811030609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8541804089531044325496581 1601588266787070811030609)
                      ·
                        rfl

theorem cell23_3119082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_3119082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119082 prefixEnd_3119082 := by exact prefixLift 3119082
  have htrace : WordTrace (prefixWord ++ tailWord_3119082) baseStart_3119082 baseEnd_3119082 := by
    simpa [prefixWord, tailWord_3119082, baseEnd_3119082] using wordTrace_append hprefix tailTrace_3119082
  have hstable : (prefixWord ++ tailWord_3119082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119082).length < 2 ^ (prefixWord ++ tailWord_3119082).sum := by decide
  have hdescent : baseEnd_3119082 < baseStart_3119082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119086 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_3119086 : Nat := 118140960795 + 3119086 * 2 ^ 59
def prefixEnd_3119086 : Nat := 4983230072969 + 3 ^ 40 * 3119086 * 2
def baseEnd_3119086 : Nat := 1601590320709688795380591

theorem tailTrace_3119086 : CollatzResearch.WordTrace tailWord_3119086 prefixEnd_3119086 1601590320709688795380591 := by
  unfold tailWord_3119086
  simp only [CollatzResearch.WordTrace]
  refine ⟨14220301547261449290462139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75841608252061062882464741 14220301547261449290462139)
  ·
    refine ⟨21330452320892173935693209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14220301547261449290462139 21330452320892173935693209)
    ·
      refine ⟨15997839240669130451769907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21330452320892173935693209 15997839240669130451769907)
      ·
        refine ⟨23996758861003695677654861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15997839240669130451769907 23996758861003695677654861)
        ·
          refine ⟨8998784572876385879120573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23996758861003695677654861 8998784572876385879120573)
          ·
            refine ⟨3374544214828644704670215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8998784572876385879120573 3374544214828644704670215)
            ·
              refine ⟨5061816322242967057005323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374544214828644704670215 5061816322242967057005323)
              ·
                refine ⟨7592724483364450585507985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5061816322242967057005323 7592724483364450585507985)
                ·
                  refine ⟨5694543362523337939130989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7592724483364450585507985 5694543362523337939130989)
                  ·
                    refine ⟨2135453760946251727174121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5694543362523337939130989 2135453760946251727174121)
                    ·
                      refine ⟨1601590320709688795380591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135453760946251727174121 1601590320709688795380591)
                      ·
                        rfl

theorem cell23_3119086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_3119086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119086 prefixEnd_3119086 := by exact prefixLift 3119086
  have htrace : WordTrace (prefixWord ++ tailWord_3119086) baseStart_3119086 baseEnd_3119086 := by
    simpa [prefixWord, tailWord_3119086, baseEnd_3119086] using wordTrace_append hprefix tailTrace_3119086
  have hstable : (prefixWord ++ tailWord_3119086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119086).length < 2 ^ (prefixWord ++ tailWord_3119086).sum := by decide
  have hdescent : baseEnd_3119086 < baseStart_3119086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119088 : List Nat := [2, 1, 1, 1, 3, 2, 2, 11]
def baseStart_3119088 : Nat := 118140960795 + 3119088 * 2 ^ 59
def prefixEnd_3119088 : Nat := 4983230072969 + 3 ^ 40 * 3119088 * 2
def baseEnd_3119088 : Nat := 59318198061888806946503

theorem tailTrace_3119088 : CollatzResearch.WordTrace tailWord_3119088 prefixEnd_3119088 59318198061888806946503 := by
  unfold tailWord_3119088
  simp only [CollatzResearch.WordTrace]
  refine ⟨56881242662042174332634959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75841656882722899110179945 56881242662042174332634959)
  ·
    refine ⟨85321863993063261498952439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56881242662042174332634959 85321863993063261498952439)
    ·
      refine ⟨127982795989594892248428659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85321863993063261498952439 127982795989594892248428659)
      ·
        refine ⟨191974193984392338372642989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127982795989594892248428659 191974193984392338372642989)
        ·
          refine ⟨71990322744147126889741121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191974193984392338372642989 71990322744147126889741121)
          ·
            refine ⟨53992742058110345167305841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71990322744147126889741121 53992742058110345167305841)
            ·
              refine ⟨40494556543582758875479381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53992742058110345167305841 40494556543582758875479381)
              ·
                refine ⟨59318198061888806946503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 40494556543582758875479381 59318198061888806946503)
                ·
                  rfl

theorem cell23_3119088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 11].length) (baseStart_3119088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119088 prefixEnd_3119088 := by exact prefixLift 3119088
  have htrace : WordTrace (prefixWord ++ tailWord_3119088) baseStart_3119088 baseEnd_3119088 := by
    simpa [prefixWord, tailWord_3119088, baseEnd_3119088] using wordTrace_append hprefix tailTrace_3119088
  have hstable : (prefixWord ++ tailWord_3119088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119088).length < 2 ^ (prefixWord ++ tailWord_3119088).sum := by decide
  have hdescent : baseEnd_3119088 < baseStart_3119088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119109 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_3119109 : Nat := 118140960795 + 3119109 * 2 ^ 59
def prefixEnd_3119109 : Nat := 4983230072969 + 3 ^ 40 * 3119109 * 2
def baseEnd_3119109 : Nat := 533867376921580735130995

theorem tailTrace_3119109 : CollatzResearch.WordTrace tailWord_3119109 prefixEnd_3119109 533867376921580735130995 := by
  unfold tailWord_3119109
  simp only [CollatzResearch.WordTrace]
  refine ⟨113763251257008269251784381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75842167504672179501189587 113763251257008269251784381)
  ·
    refine ⟨42661219221378100969419143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113763251257008269251784381 42661219221378100969419143)
    ·
      refine ⟨63991828832067151454128715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42661219221378100969419143 63991828832067151454128715)
      ·
        refine ⟨95987743248100727181193073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63991828832067151454128715 95987743248100727181193073)
        ·
          refine ⟨71990807436075545385894805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95987743248100727181193073 71990807436075545385894805)
          ·
            refine ⟨3374569098566041189963819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71990807436075545385894805 3374569098566041189963819)
            ·
              refine ⟨5061853647849061784945729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374569098566041189963819 5061853647849061784945729)
              ·
                refine ⟨3796390235886796338709297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5061853647849061784945729 3796390235886796338709297)
                ·
                  refine ⟨2847292676915097254031973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3796390235886796338709297 2847292676915097254031973)
                  ·
                    refine ⟨533867376921580735130995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2847292676915097254031973 533867376921580735130995)
                    ·
                      rfl

theorem cell23_3119109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_3119109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119109 prefixEnd_3119109 := by exact prefixLift 3119109
  have htrace : WordTrace (prefixWord ++ tailWord_3119109) baseStart_3119109 baseEnd_3119109 := by
    simpa [prefixWord, tailWord_3119109, baseEnd_3119109] using wordTrace_append hprefix tailTrace_3119109
  have hstable : (prefixWord ++ tailWord_3119109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119109).length < 2 ^ (prefixWord ++ tailWord_3119109).sum := by decide
  have hdescent : baseEnd_3119109 < baseStart_3119109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119116 : List Nat := [2, 2, 1, 2, 3, 1, 1, 6, 1, 2, 2]
def baseStart_3119116 : Nat := 118140960795 + 3119116 * 2 ^ 59
def prefixEnd_3119116 : Nat := 4983230072969 + 3 ^ 40 * 3119116 * 2
def baseEnd_3119116 : Nat := 1601605725129323678005453

theorem tailTrace_3119116 : CollatzResearch.WordTrace tailWord_3119116 prefixEnd_3119116 1601605725129323678005453 := by
  unfold tailWord_3119116
  simp only [CollatzResearch.WordTrace]
  refine ⟨56881753283991454723644601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75842337711988606298192801 56881753283991454723644601)
  ·
    refine ⟨42661314962993591042733451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56881753283991454723644601 42661314962993591042733451)
    ·
      refine ⟨63991972444490386564100177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42661314962993591042733451 63991972444490386564100177)
      ·
        refine ⟨47993979333367789923075133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63991972444490386564100177 47993979333367789923075133)
        ·
          refine ⟨17997742250012921221153175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47993979333367789923075133 17997742250012921221153175)
          ·
            refine ⟨26996613375019381831729763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17997742250012921221153175 26996613375019381831729763)
            ·
              refine ⟨40494920062529072747594645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26996613375019381831729763 40494920062529072747594645)
              ·
                refine ⟨1898199377931050285043499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40494920062529072747594645 1898199377931050285043499)
                ·
                  refine ⟨2847299066896575427565249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898199377931050285043499 2847299066896575427565249)
                  ·
                    refine ⟨2135474300172431570673937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2847299066896575427565249 2135474300172431570673937)
                    ·
                      refine ⟨1601605725129323678005453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135474300172431570673937 1601605725129323678005453)
                      ·
                        rfl

theorem cell23_3119116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_3119116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119116 prefixEnd_3119116 := by exact prefixLift 3119116
  have htrace : WordTrace (prefixWord ++ tailWord_3119116) baseStart_3119116 baseEnd_3119116 := by
    simpa [prefixWord, tailWord_3119116, baseEnd_3119116] using wordTrace_append hprefix tailTrace_3119116
  have hstable : (prefixWord ++ tailWord_3119116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119116).length < 2 ^ (prefixWord ++ tailWord_3119116).sum := by decide
  have hdescent : baseEnd_3119116 < baseStart_3119116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119150 : List Nat := [4, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_3119150 : Nat := 118140960795 + 3119150 * 2 ^ 59
def prefixEnd_3119150 : Nat := 4983230072969 + 3 ^ 40 * 3119150 * 2
def baseEnd_3119150 : Nat := 1601623183471576544980297

theorem tailTrace_3119150 : CollatzResearch.WordTrace tailWord_3119150 prefixEnd_3119150 1601623183471576544980297 := by
  unfold tailWord_3119150
  simp only [CollatzResearch.WordTrace]
  refine ⟨14220593331232466656753363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75843164433239822169351269 14220593331232466656753363)
  ·
    refine ⟨21330889996848699985130045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14220593331232466656753363 21330889996848699985130045)
    ·
      refine ⟨7999083748818262494423767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21330889996848699985130045 7999083748818262494423767)
      ·
        refine ⟨11998625623227393741635651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7999083748818262494423767 11998625623227393741635651)
        ·
          refine ⟨17997938434841090612453477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11998625623227393741635651 17997938434841090612453477)
          ·
            refine ⟨3374613456532704489835027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17997938434841090612453477 3374613456532704489835027)
            ·
              refine ⟨5061920184799056734752541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374613456532704489835027 5061920184799056734752541)
              ·
                refine ⟨1898220069299646275532203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5061920184799056734752541 1898220069299646275532203)
                ·
                  refine ⟨2847330103949469413298305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898220069299646275532203 2847330103949469413298305)
                  ·
                    refine ⟨2135497577962102059973729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2847330103949469413298305 2135497577962102059973729)
                    ·
                      refine ⟨1601623183471576544980297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135497577962102059973729 1601623183471576544980297)
                      ·
                        rfl

theorem cell23_3119150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_3119150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119150 prefixEnd_3119150 := by exact prefixLift 3119150
  have htrace : WordTrace (prefixWord ++ tailWord_3119150) baseStart_3119150 baseEnd_3119150 := by
    simpa [prefixWord, tailWord_3119150, baseEnd_3119150] using wordTrace_append hprefix tailTrace_3119150
  have hstable : (prefixWord ++ tailWord_3119150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119150).length < 2 ^ (prefixWord ++ tailWord_3119150).sum := by decide
  have hdescent : baseEnd_3119150 < baseStart_3119150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119159 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 1, 3, 2]
def baseStart_3119159 : Nat := 118140960795 + 3119159 * 2 ^ 59
def prefixEnd_3119159 : Nat := 4983230072969 + 3 ^ 40 * 3119159 * 2
def baseEnd_3119159 : Nat := 1601627804797467009767755

theorem tailTrace_3119159 : CollatzResearch.WordTrace tailWord_3119159 prefixEnd_3119159 1601627804797467009767755 := by
  unfold tailWord_3119159
  simp only [CollatzResearch.WordTrace]
  refine ⟨113765074906827127791104531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75843383271218085194069687 113765074906827127791104531)
  ·
    refine ⟨170647612360240691686656797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113765074906827127791104531 170647612360240691686656797)
    ·
      refine ⟨63992854635090259382496299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170647612360240691686656797 63992854635090259382496299)
      ·
        refine ⟨95989281952635389073744449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63992854635090259382496299 95989281952635389073744449)
        ·
          refine ⟨71991961464476541805308337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95989281952635389073744449 71991961464476541805308337)
          ·
            refine ⟨53993971098357406353981253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71991961464476541805308337 53993971098357406353981253)
            ·
              refine ⟨10123869580942013691371485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53993971098357406353981253 10123869580942013691371485)
              ·
                refine ⟨3796451092853255134264307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10123869580942013691371485 3796451092853255134264307)
                ·
                  refine ⟨5694676639279882701396461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3796451092853255134264307 5694676639279882701396461)
                  ·
                    refine ⟨2135503739729956013023673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5694676639279882701396461 2135503739729956013023673)
                    ·
                      refine ⟨1601627804797467009767755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135503739729956013023673 1601627804797467009767755)
                      ·
                        rfl

theorem cell23_3119159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_3119159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119159 prefixEnd_3119159 := by exact prefixLift 3119159
  have htrace : WordTrace (prefixWord ++ tailWord_3119159) baseStart_3119159 baseEnd_3119159 := by
    simpa [prefixWord, tailWord_3119159, baseEnd_3119159] using wordTrace_append hprefix tailTrace_3119159
  have hstable : (prefixWord ++ tailWord_3119159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119159).length < 2 ^ (prefixWord ++ tailWord_3119159).sum := by decide
  have hdescent : baseEnd_3119159 < baseStart_3119159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119175 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_3119175 : Nat := 118140960795 + 3119175 * 2 ^ 59
def prefixEnd_3119175 : Nat := 4983230072969 + 3 ^ 40 * 3119175 * 2
def baseEnd_3119175 : Nat := 1601636020487938947167681

theorem tailTrace_3119175 : CollatzResearch.WordTrace tailWord_3119175 prefixEnd_3119175 1601636020487938947167681 := by
  unfold tailWord_3119175
  simp only [CollatzResearch.WordTrace]
  refine ⟨113765658474769162523686979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75843772316512775015791319 113765658474769162523686979)
  ·
    refine ⟨170648487712153743785530469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113765658474769162523686979 170648487712153743785530469)
    ·
      refine ⟨31996591446028826959786963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170648487712153743785530469 31996591446028826959786963)
      ·
        refine ⟨47994887169043240439680445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31996591446028826959786963 47994887169043240439680445)
        ·
          refine ⟨17998082688391215164880167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47994887169043240439680445 17998082688391215164880167)
          ·
            refine ⟨26997124032586822747320251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17998082688391215164880167 26997124032586822747320251)
            ·
              refine ⟨40495686048880234120980377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26997124032586822747320251 40495686048880234120980377)
              ·
                refine ⟨30371764536660175590735283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40495686048880234120980377 30371764536660175590735283)
                ·
                  refine ⟨45557646804990263386102925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30371764536660175590735283 45557646804990263386102925)
                  ·
                    refine ⟨17084117551871348769788597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45557646804990263386102925 17084117551871348769788597)
                    ·
                      refine ⟨1601636020487938947167681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17084117551871348769788597 1601636020487938947167681)
                      ·
                        rfl

theorem cell23_3119175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_3119175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119175 prefixEnd_3119175 := by exact prefixLift 3119175
  have htrace : WordTrace (prefixWord ++ tailWord_3119175) baseStart_3119175 baseEnd_3119175 := by
    simpa [prefixWord, tailWord_3119175, baseEnd_3119175] using wordTrace_append hprefix tailTrace_3119175
  have hstable : (prefixWord ++ tailWord_3119175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119175).length < 2 ^ (prefixWord ++ tailWord_3119175).sum := by decide
  have hdescent : baseEnd_3119175 < baseStart_3119175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119185 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_3119185 : Nat := 118140960795 + 3119185 * 2 ^ 59
def prefixEnd_3119185 : Nat := 4983230072969 + 3 ^ 40 * 3119185 * 2
def baseEnd_3119185 : Nat := 1601641155294483908042635

theorem tailTrace_3119185 : CollatzResearch.WordTrace tailWord_3119185 prefixEnd_3119185 1601641155294483908042635 := by
  unfold tailWord_3119185
  simp only [CollatzResearch.WordTrace]
  refine ⟨113766023204732934231551009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75844015469821956154367339 113766023204732934231551009)
  ·
    refine ⟨85324517403549700673663257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113766023204732934231551009 85324517403549700673663257)
    ·
      refine ⟨63993388052662275505247443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85324517403549700673663257 63993388052662275505247443)
      ·
        refine ⟨95990082078993413257871165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63993388052662275505247443 95990082078993413257871165)
        ·
          refine ⟨35996280779622529971701687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95990082078993413257871165 35996280779622529971701687)
          ·
            refine ⟨53994421169433794957552531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35996280779622529971701687 53994421169433794957552531)
            ·
              refine ⟨80991631754150692436328797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53994421169433794957552531 80991631754150692436328797)
              ·
                refine ⟨30371861907806509663623299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80991631754150692436328797 30371861907806509663623299)
                ·
                  refine ⟨45557792861709764495434949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30371861907806509663623299 45557792861709764495434949)
                  ·
                    refine ⟨8542086161570580842894053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45557792861709764495434949 8542086161570580842894053)
                    ·
                      refine ⟨1601641155294483908042635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8542086161570580842894053 1601641155294483908042635)
                      ·
                        rfl

theorem cell23_3119185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_3119185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119185 prefixEnd_3119185 := by exact prefixLift 3119185
  have htrace : WordTrace (prefixWord ++ tailWord_3119185) baseStart_3119185 baseEnd_3119185 := by
    simpa [prefixWord, tailWord_3119185, baseEnd_3119185] using wordTrace_append hprefix tailTrace_3119185
  have hstable : (prefixWord ++ tailWord_3119185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119185).length < 2 ^ (prefixWord ++ tailWord_3119185).sum := by decide
  have hdescent : baseEnd_3119185 < baseStart_3119185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119229 : List Nat := [1, 4, 1, 1, 3, 3, 1, 4, 5]
def baseStart_3119229 : Nat := 118140960795 + 3119229 * 2 ^ 59
def prefixEnd_3119229 : Nat := 4983230072969 + 3 ^ 40 * 3119229 * 2
def baseEnd_3119229 : Nat := 177962638715920192876937

theorem tailTrace_3119229 : CollatzResearch.WordTrace tailWord_3119229 prefixEnd_3119229 177962638715920192876937 := by
  unfold tailWord_3119229
  simp only [CollatzResearch.WordTrace]
  refine ⟨113767628016573529746152741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75845085344382353164101827 113767628016573529746152741)
  ·
    refine ⟨21331430253107536827403639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113767628016573529746152741 21331430253107536827403639)
    ·
      refine ⟨31997145379661305241105459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21331430253107536827403639 31997145379661305241105459)
      ·
        refine ⟨47995718069491957861658189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31997145379661305241105459 47995718069491957861658189)
        ·
          refine ⟨17998394276059484198121821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47995718069491957861658189 17998394276059484198121821)
          ·
            refine ⟨6749397853522306574295683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17998394276059484198121821 6749397853522306574295683)
            ·
              refine ⟨10124096780283459861443525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6749397853522306574295683 10124096780283459861443525)
              ·
                refine ⟨1898268146303148724020661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10124096780283459861443525 1898268146303148724020661)
                ·
                  refine ⟨177962638715920192876937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1898268146303148724020661 177962638715920192876937)
                  ·
                    rfl

theorem cell23_3119229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_3119229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119229 prefixEnd_3119229 := by exact prefixLift 3119229
  have htrace : WordTrace (prefixWord ++ tailWord_3119229) baseStart_3119229 baseEnd_3119229 := by
    simpa [prefixWord, tailWord_3119229, baseEnd_3119229] using wordTrace_append hprefix tailTrace_3119229
  have hstable : (prefixWord ++ tailWord_3119229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119229).length < 2 ^ (prefixWord ++ tailWord_3119229).sum := by decide
  have hdescent : baseEnd_3119229 < baseStart_3119229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119289 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 3, 4]
def baseStart_3119289 : Nat := 118140960795 + 3119289 * 2 ^ 59
def prefixEnd_3119289 : Nat := 4983230072969 + 3 ^ 40 * 3119289 * 2
def baseEnd_3119289 : Nat := 533898185760850500380719

theorem tailTrace_3119289 : CollatzResearch.WordTrace tailWord_3119289 prefixEnd_3119289 533898185760850500380719 := by
  unfold tailWord_3119289
  simp only [CollatzResearch.WordTrace]
  refine ⟨113769816396356159993336921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75846544264237439995557947 113769816396356159993336921)
  ·
    refine ⟨85327362297267119995002691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113769816396356159993336921 85327362297267119995002691)
    ·
      refine ⟨127991043445900679992504037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85327362297267119995002691 127991043445900679992504037)
      ·
        refine ⟨23998320646106377498594507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127991043445900679992504037 23998320646106377498594507)
        ·
          refine ⟨35997480969159566247891761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23998320646106377498594507 35997480969159566247891761)
          ·
            refine ⟨26998110726869674685918821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35997480969159566247891761 26998110726869674685918821)
            ·
              refine ⟨5062145761288064003609779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26998110726869674685918821 5062145761288064003609779)
              ·
                refine ⟨7593218641932096005414669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5062145761288064003609779 7593218641932096005414669)
                ·
                  refine ⟨2847456990724536002030501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7593218641932096005414669 2847456990724536002030501)
                  ·
                    refine ⟨533898185760850500380719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2847456990724536002030501 533898185760850500380719)
                    ·
                      rfl

theorem cell23_3119289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 4].length) (baseStart_3119289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119289 prefixEnd_3119289 := by exact prefixLift 3119289
  have htrace : WordTrace (prefixWord ++ tailWord_3119289) baseStart_3119289 baseEnd_3119289 := by
    simpa [prefixWord, tailWord_3119289, baseEnd_3119289] using wordTrace_append hprefix tailTrace_3119289
  have hstable : (prefixWord ++ tailWord_3119289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119289).length < 2 ^ (prefixWord ++ tailWord_3119289).sum := by decide
  have hdescent : baseEnd_3119289 < baseStart_3119289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119330 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3119330 : Nat := 118140960795 + 3119330 * 2 ^ 59
def prefixEnd_3119330 : Nat := 4983230072969 + 3 ^ 40 * 3119330 * 2
def baseEnd_3119330 : Nat := 1601715609989385840729469

theorem tailTrace_3119330 : CollatzResearch.WordTrace tailWord_3119330 prefixEnd_3119330 1601715609989385840729469 := by
  unfold tailWord_3119330
  simp only [CollatzResearch.WordTrace]
  refine ⟨28442827947301905998894861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75847541192805082663719629 28442827947301905998894861)
  ·
    refine ⟨10666060480238214749585573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28442827947301905998894861 10666060480238214749585573)
    ·
      refine ⟨1999886340044665265547295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10666060480238214749585573 1999886340044665265547295)
      ·
        refine ⟨2999829510066997898320943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999886340044665265547295 2999829510066997898320943)
        ·
          refine ⟨4499744265100496847481415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999829510066997898320943 4499744265100496847481415)
          ·
            refine ⟨6749616397650745271222123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499744265100496847481415 6749616397650745271222123)
            ·
              refine ⟨10124424596476117906833185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6749616397650745271222123 10124424596476117906833185)
              ·
                refine ⟨7593318447357088430124889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10124424596476117906833185 7593318447357088430124889)
                ·
                  refine ⟨5694988835517816322593667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7593318447357088430124889 5694988835517816322593667)
                  ·
                    refine ⟨8542483253276724483890501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5694988835517816322593667 8542483253276724483890501)
                    ·
                      refine ⟨1601715609989385840729469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8542483253276724483890501 1601715609989385840729469)
                      ·
                        rfl

theorem cell23_3119330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3119330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119330 prefixEnd_3119330 := by exact prefixLift 3119330
  have htrace : WordTrace (prefixWord ++ tailWord_3119330) baseStart_3119330 baseEnd_3119330 := by
    simpa [prefixWord, tailWord_3119330, baseEnd_3119330] using wordTrace_append hprefix tailTrace_3119330
  have hstable : (prefixWord ++ tailWord_3119330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119330).length < 2 ^ (prefixWord ++ tailWord_3119330).sum := by decide
  have hdescent : baseEnd_3119330 < baseStart_3119330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119332 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_3119332 : Nat := 118140960795 + 3119332 * 2 ^ 59
def prefixEnd_3119332 : Nat := 4983230072969 + 3 ^ 40 * 3119332 * 2
def baseEnd_3119332 : Nat := 533905545650231610968153

theorem tailTrace_3119332 : CollatzResearch.WordTrace tailWord_3119332 prefixEnd_3119332 533905545650231610968153 := by
  unfold tailWord_3119332
  simp only [CollatzResearch.WordTrace]
  refine ⟨56885692367600189168576125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75847589823466918891434833 56885692367600189168576125)
  ·
    refine ⟨21332134637850070938216047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56885692367600189168576125 21332134637850070938216047)
    ·
      refine ⟨31998201956775106407324071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21332134637850070938216047 31998201956775106407324071)
      ·
        refine ⟨47997302935162659610986107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31998201956775106407324071 47997302935162659610986107)
        ·
          refine ⟨71995954402743989416479161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47997302935162659610986107 71995954402743989416479161)
          ·
            refine ⟨53996965802057992062359371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71995954402743989416479161 53996965802057992062359371)
            ·
              refine ⟨80995448703086988093539057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53996965802057992062359371 80995448703086988093539057)
              ·
                refine ⟨60746586527315241070154293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80995448703086988093539057 60746586527315241070154293)
                ·
                  refine ⟨5694992486935803850326965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60746586527315241070154293 5694992486935803850326965)
                  ·
                    refine ⟨533905545650231610968153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5694992486935803850326965 533905545650231610968153)
                    ·
                      rfl

theorem cell23_3119332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_3119332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119332 prefixEnd_3119332 := by exact prefixLift 3119332
  have htrace : WordTrace (prefixWord ++ tailWord_3119332) baseStart_3119332 baseEnd_3119332 := by
    simpa [prefixWord, tailWord_3119332, baseEnd_3119332] using wordTrace_append hprefix tailTrace_3119332
  have hstable : (prefixWord ++ tailWord_3119332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119332).length < 2 ^ (prefixWord ++ tailWord_3119332).sum := by decide
  have hdescent : baseEnd_3119332 < baseStart_3119332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119342 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3119342 : Nat := 118140960795 + 3119342 * 2 ^ 59
def prefixEnd_3119342 : Nat := 4983230072969 + 3 ^ 40 * 3119342 * 2
def baseEnd_3119342 : Nat := 1601721771757239793779413

theorem tailTrace_3119342 : CollatzResearch.WordTrace tailWord_3119342 prefixEnd_3119342 1601721771757239793779413 := by
  unfold tailWord_3119342
  simp only [CollatzResearch.WordTrace]
  refine ⟨14221468683145518755627035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75847832976776100030010853 14221468683145518755627035)
  ·
    refine ⟨21332203024718278133440553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14221468683145518755627035 21332203024718278133440553)
    ·
      refine ⟨15999152268538708600080415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21332203024718278133440553 15999152268538708600080415)
      ·
        refine ⟨23998728402808062900120623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15999152268538708600080415 23998728402808062900120623)
        ·
          refine ⟨35998092604212094350180935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23998728402808062900120623 35998092604212094350180935)
          ·
            refine ⟨53997138906318141525271403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35998092604212094350180935 53997138906318141525271403)
            ·
              refine ⟨80995708359477212287907105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53997138906318141525271403 80995708359477212287907105)
              ·
                refine ⟨60746781269607909215930329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80995708359477212287907105 60746781269607909215930329)
                ·
                  refine ⟨45560085952205931911947747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60746781269607909215930329 45560085952205931911947747)
                  ·
                    refine ⟨68340128928308897867921621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45560085952205931911947747 68340128928308897867921621)
                    ·
                      refine ⟨1601721771757239793779413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68340128928308897867921621 1601721771757239793779413)
                      ·
                        rfl

theorem cell23_3119342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3119342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119342 prefixEnd_3119342 := by exact prefixLift 3119342
  have htrace : WordTrace (prefixWord ++ tailWord_3119342) baseStart_3119342 baseEnd_3119342 := by
    simpa [prefixWord, tailWord_3119342, baseEnd_3119342] using wordTrace_append hprefix tailTrace_3119342
  have hstable : (prefixWord ++ tailWord_3119342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119342).length < 2 ^ (prefixWord ++ tailWord_3119342).sum := by decide
  have hdescent : baseEnd_3119342 < baseStart_3119342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119369 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 4]
def baseStart_3119369 : Nat := 118140960795 + 3119369 * 2 ^ 59
def prefixEnd_3119369 : Nat := 4983230072969 + 3 ^ 40 * 3119369 * 2
def baseEnd_3119369 : Nat := 1601735635734911188141789

theorem tailTrace_3119369 : CollatzResearch.WordTrace tailWord_3119369 prefixEnd_3119369 1601735635734911188141789 := by
  unfold tailWord_3119369
  simp only [CollatzResearch.WordTrace]
  refine ⟨113772734236066333656249161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75848489490710889104166107 113772734236066333656249161)
  ·
    refine ⟨85329550677049750242186871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113772734236066333656249161 85329550677049750242186871)
    ·
      refine ⟨127994326015574625363280307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85329550677049750242186871 127994326015574625363280307)
      ·
        refine ⟨191991489023361938044920461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127994326015574625363280307 191991489023361938044920461)
        ·
          refine ⟨71996808383760726766845173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191991489023361938044920461 71996808383760726766845173)
          ·
            refine ⟨6749700785977568134391735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71996808383760726766845173 6749700785977568134391735)
            ·
              refine ⟨10124551178966352201587603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6749700785977568134391735 10124551178966352201587603)
              ·
                refine ⟨15186826768449528302381405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10124551178966352201587603 15186826768449528302381405)
                ·
                  refine ⟨5695060038168573113393027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15186826768449528302381405 5695060038168573113393027)
                  ·
                    refine ⟨8542590057252859670089541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5695060038168573113393027 8542590057252859670089541)
                    ·
                      refine ⟨1601735635734911188141789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8542590057252859670089541 1601735635734911188141789)
                      ·
                        rfl

theorem cell23_3119369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_3119369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119369 prefixEnd_3119369 := by exact prefixLift 3119369
  have htrace : WordTrace (prefixWord ++ tailWord_3119369) baseStart_3119369 baseEnd_3119369 := by
    simpa [prefixWord, tailWord_3119369, baseEnd_3119369] using wordTrace_append hprefix tailTrace_3119369
  have hstable : (prefixWord ++ tailWord_3119369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119369).length < 2 ^ (prefixWord ++ tailWord_3119369).sum := by decide
  have hdescent : baseEnd_3119369 < baseStart_3119369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119390 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_3119390 : Nat := 118140960795 + 3119390 * 2 ^ 59
def prefixEnd_3119390 : Nat := 4983230072969 + 3 ^ 40 * 3119390 * 2
def baseEnd_3119390 : Nat := 1601746418828655605979193

theorem tailTrace_3119390 : CollatzResearch.WordTrace tailWord_3119390 prefixEnd_3119390 1601746418828655605979193 := by
  unfold tailWord_3119390
  simp only [CollatzResearch.WordTrace]
  refine ⟨14221687521123781780345453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75849000112660169495175749 14221687521123781780345453)
  ·
    refine ⟨5333132820421418167629545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14221687521123781780345453 5333132820421418167629545)
    ·
      refine ⟨3999849615316063625722159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5333132820421418167629545 3999849615316063625722159)
      ·
        refine ⟨5999774422974095438583239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3999849615316063625722159 5999774422974095438583239)
        ·
          refine ⟨8999661634461143157874859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5999774422974095438583239 8999661634461143157874859)
          ·
            refine ⟨13499492451691714736812289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8999661634461143157874859 13499492451691714736812289)
            ·
              refine ⟨10124619338768786052609217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13499492451691714736812289 10124619338768786052609217)
              ·
                refine ⟨7593464504076589539456913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10124619338768786052609217 7593464504076589539456913)
                ·
                  refine ⟨5695098378057442154592685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7593464504076589539456913 5695098378057442154592685)
                  ·
                    refine ⟨2135661891771540807972257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5695098378057442154592685 2135661891771540807972257)
                    ·
                      refine ⟨1601746418828655605979193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135661891771540807972257 1601746418828655605979193)
                      ·
                        rfl

theorem cell23_3119390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_3119390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119390 prefixEnd_3119390 := by exact prefixLift 3119390
  have htrace : WordTrace (prefixWord ++ tailWord_3119390) baseStart_3119390 baseEnd_3119390 := by
    simpa [prefixWord, tailWord_3119390, baseEnd_3119390] using wordTrace_append hprefix tailTrace_3119390
  have hstable : (prefixWord ++ tailWord_3119390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119390).length < 2 ^ (prefixWord ++ tailWord_3119390).sum := by decide
  have hdescent : baseEnd_3119390 < baseStart_3119390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119392 : List Nat := [2, 1, 1, 5, 2, 12]
def baseStart_3119392 : Nat := 118140960795 + 3119392 * 2 ^ 59
def prefixEnd_3119392 : Nat := 4983230072969 + 3 ^ 40 * 3119392 * 2
def baseEnd_3119392 : Nat := 6591553274855821391581

theorem tailTrace_3119392 : CollatzResearch.WordTrace tailWord_3119392 prefixEnd_3119392 6591553274855821391581 := by
  unfold tailWord_3119392
  simp only [CollatzResearch.WordTrace]
  refine ⟨56886786557491504292168215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75849048743322005722890953 56886786557491504292168215)
  ·
    refine ⟨85330179836237256438252323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56886786557491504292168215 85330179836237256438252323)
    ·
      refine ⟨127995269754355884657378485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85330179836237256438252323 127995269754355884657378485)
      ·
        refine ⟨11999556539470864186629233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127995269754355884657378485 11999556539470864186629233)
        ·
          refine ⟨8999667404603148139971925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11999556539470864186629233 8999667404603148139971925)
          ·
            refine ⟨6591553274855821391581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8999667404603148139971925 6591553274855821391581)
            ·
              rfl

theorem cell23_3119392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 12].length) (baseStart_3119392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119392 prefixEnd_3119392 := by exact prefixLift 3119392
  have htrace : WordTrace (prefixWord ++ tailWord_3119392) baseStart_3119392 baseEnd_3119392 := by
    simpa [prefixWord, tailWord_3119392, baseEnd_3119392] using wordTrace_append hprefix tailTrace_3119392
  have hstable : (prefixWord ++ tailWord_3119392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119392).length < 2 ^ (prefixWord ++ tailWord_3119392).sum := by decide
  have hdescent : baseEnd_3119392 < baseStart_3119392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119396 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_3119396 : Nat := 118140960795 + 3119396 * 2 ^ 59
def prefixEnd_3119396 : Nat := 4983230072969 + 3 ^ 40 * 3119396 * 2
def baseEnd_3119396 : Nat := 533916499904194194168055

theorem tailTrace_3119396 : CollatzResearch.WordTrace tailWord_3119396 prefixEnd_3119396 533916499904194194168055 := by
  unfold tailWord_3119396
  simp only [CollatzResearch.WordTrace]
  refine ⟨56886859503484258633741021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75849146004645678178321361 56886859503484258633741021)
  ·
    refine ⟨21332572313806596987652883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56886859503484258633741021 21332572313806596987652883)
    ·
      refine ⟨31998858470709895481479325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21332572313806596987652883 31998858470709895481479325)
      ·
        refine ⟨11999571926516210805554747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31998858470709895481479325 11999571926516210805554747)
        ·
          refine ⟨17999357889774316208332121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11999571926516210805554747 17999357889774316208332121)
          ·
            refine ⟨13499518417330737156249091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17999357889774316208332121 13499518417330737156249091)
            ·
              refine ⟨20249277625996105734373637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13499518417330737156249091 20249277625996105734373637)
              ·
                refine ⟨3796739554874269825195057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20249277625996105734373637 3796739554874269825195057)
                ·
                  refine ⟨2847554666155702368896293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3796739554874269825195057 2847554666155702368896293)
                  ·
                    refine ⟨533916499904194194168055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2847554666155702368896293 533916499904194194168055)
                    ·
                      rfl

theorem cell23_3119396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_3119396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119396 prefixEnd_3119396 := by exact prefixLift 3119396
  have htrace : WordTrace (prefixWord ++ tailWord_3119396) baseStart_3119396 baseEnd_3119396 := by
    simpa [prefixWord, tailWord_3119396, baseEnd_3119396] using wordTrace_append hprefix tailTrace_3119396
  have hstable : (prefixWord ++ tailWord_3119396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119396).length < 2 ^ (prefixWord ++ tailWord_3119396).sum := by decide
  have hdescent : baseEnd_3119396 < baseStart_3119396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119397 : List Nat := [1, 3, 1, 2, 5, 2, 2, 2, 1, 1, 3]
def baseStart_3119397 : Nat := 118140960795 + 3119397 * 2 ^ 59
def prefixEnd_3119397 : Nat := 4983230072969 + 3 ^ 40 * 3119397 * 2
def baseEnd_3119397 : Nat := 1601750013193237078591661

theorem tailTrace_3119397 : CollatzResearch.WordTrace tailWord_3119397 prefixEnd_3119397 1601750013193237078591661 := by
  unfold tailWord_3119397
  simp only [CollatzResearch.WordTrace]
  refine ⟨113773755479964894438268445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75849170319976596292178963 113773755479964894438268445)
  ·
    refine ⟨42665158304986835414350667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113773755479964894438268445 42665158304986835414350667)
    ·
      refine ⟨63997737457480253121526001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42665158304986835414350667 63997737457480253121526001)
      ·
        refine ⟨47998303093110189841144501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63997737457480253121526001 47998303093110189841144501)
        ·
          refine ⟨4499840914979080297607297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47998303093110189841144501 4499840914979080297607297)
          ·
            refine ⟨3374880686234310223205473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4499840914979080297607297 3374880686234310223205473)
            ·
              refine ⟨2531160514675732667404105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3374880686234310223205473 2531160514675732667404105)
              ·
                refine ⟨1898370386006799500553079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2531160514675732667404105 1898370386006799500553079)
                ·
                  refine ⟨2847555579010199250829619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898370386006799500553079 2847555579010199250829619)
                  ·
                    refine ⟨4271333368515298876244429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2847555579010199250829619 4271333368515298876244429)
                    ·
                      refine ⟨1601750013193237078591661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4271333368515298876244429 1601750013193237078591661)
                      ·
                        rfl

theorem cell23_3119397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_3119397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119397 prefixEnd_3119397 := by exact prefixLift 3119397
  have htrace : WordTrace (prefixWord ++ tailWord_3119397) baseStart_3119397 baseEnd_3119397 := by
    simpa [prefixWord, tailWord_3119397, baseEnd_3119397] using wordTrace_append hprefix tailTrace_3119397
  have hstable : (prefixWord ++ tailWord_3119397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119397).length < 2 ^ (prefixWord ++ tailWord_3119397).sum := by decide
  have hdescent : baseEnd_3119397 < baseStart_3119397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119436 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3119436 : Nat := 118140960795 + 3119436 * 2 ^ 59
def prefixEnd_3119436 : Nat := 4983230072969 + 3 ^ 40 * 3119436 * 2
def baseEnd_3119436 : Nat := 1601770038938762426003981

theorem tailTrace_3119436 : CollatzResearch.WordTrace tailWord_3119436 prefixEnd_3119436 1601770038938762426003981 := by
  unfold tailWord_3119436
  simp only [CollatzResearch.WordTrace]
  refine ⟨56887588963411802049469081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75850118617882402732625441 56887588963411802049469081)
  ·
    refine ⟨42665691722558851537101811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56887588963411802049469081 42665691722558851537101811)
    ·
      refine ⟨63998537583838277305652717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42665691722558851537101811 63998537583838277305652717)
      ·
        refine ⟨23999451593939353989619769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63998537583838277305652717 23999451593939353989619769)
        ·
          refine ⟨17999588695454515492214827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23999451593939353989619769 17999588695454515492214827)
          ·
            refine ⟨26999383043181773238322241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17999588695454515492214827 26999383043181773238322241)
            ·
              refine ⟨20249537282386329928741681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26999383043181773238322241 20249537282386329928741681)
              ·
                refine ⟨15187152961789747446556261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20249537282386329928741681 15187152961789747446556261)
                ·
                  refine ⟨2847591180335577646229299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15187152961789747446556261 2847591180335577646229299)
                  ·
                    refine ⟨4271386770503366469343949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2847591180335577646229299 4271386770503366469343949)
                    ·
                      refine ⟨1601770038938762426003981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4271386770503366469343949 1601770038938762426003981)
                      ·
                        rfl

theorem cell23_3119436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3119436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119436 prefixEnd_3119436 := by exact prefixLift 3119436
  have htrace : WordTrace (prefixWord ++ tailWord_3119436) baseStart_3119436 baseEnd_3119436 := by
    simpa [prefixWord, tailWord_3119436, baseEnd_3119436] using wordTrace_append hprefix tailTrace_3119436
  have hstable : (prefixWord ++ tailWord_3119436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119436).length < 2 ^ (prefixWord ++ tailWord_3119436).sum := by decide
  have hdescent : baseEnd_3119436 < baseStart_3119436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119469 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_3119469 : Nat := 118140960795 + 3119469 * 2 ^ 59
def prefixEnd_3119469 : Nat := 4983230072969 + 3 ^ 40 * 3119469 * 2
def baseEnd_3119469 : Nat := 533928994600120265630443

theorem tailTrace_3119469 : CollatzResearch.WordTrace tailWord_3119469 prefixEnd_3119469 533928994600120265630443 := by
  unfold tailWord_3119469
  simp only [CollatzResearch.WordTrace]
  refine ⟨113776381535704050734889461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75850921023802700489926307 113776381535704050734889461)
  ·
    refine ⟨10666535768972254756395887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113776381535704050734889461 10666535768972254756395887)
    ·
      refine ⟨15999803653458382134593831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10666535768972254756395887 15999803653458382134593831)
      ·
        refine ⟨23999705480187573201890747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15999803653458382134593831 23999705480187573201890747)
        ·
          refine ⟨35999558220281359802836121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23999705480187573201890747 35999558220281359802836121)
          ·
            refine ⟨26999668665211019852127091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35999558220281359802836121 26999668665211019852127091)
            ·
              refine ⟨40499502997816529778190637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26999668665211019852127091 40499502997816529778190637)
              ·
                refine ⟨15187313624181198666821489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40499502997816529778190637 15187313624181198666821489)
                ·
                  refine ⟨11390485218135899000116117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15187313624181198666821489 11390485218135899000116117)
                  ·
                    refine ⟨533928994600120265630443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11390485218135899000116117 533928994600120265630443)
                    ·
                      rfl

theorem cell23_3119469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_3119469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119469 prefixEnd_3119469 := by exact prefixLift 3119469
  have htrace : WordTrace (prefixWord ++ tailWord_3119469) baseStart_3119469 baseEnd_3119469 := by
    simpa [prefixWord, tailWord_3119469, baseEnd_3119469] using wordTrace_append hprefix tailTrace_3119469
  have hstable : (prefixWord ++ tailWord_3119469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119469).length < 2 ^ (prefixWord ++ tailWord_3119469).sum := by decide
  have hdescent : baseEnd_3119469 < baseStart_3119469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119527 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_3119527 : Nat := 118140960795 + 3119527 * 2 ^ 59
def prefixEnd_3119527 : Nat := 4983230072969 + 3 ^ 40 * 3119527 * 2
def baseEnd_3119527 : Nat := 1601816765678321569966063

theorem tailTrace_3119527 : CollatzResearch.WordTrace tailWord_3119527 prefixEnd_3119527 1601816765678321569966063 := by
  unfold tailWord_3119527
  simp only [CollatzResearch.WordTrace]
  refine ⟨113778496969493926640500835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75852331312995951093667223 113778496969493926640500835)
  ·
    refine ⟨170667745454240889960751253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113778496969493926640500835 170667745454240889960751253)
    ·
      refine ⟨8000050568167541716910215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170667745454240889960751253 8000050568167541716910215)
      ·
        refine ⟨12000075852251312575365323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8000050568167541716910215 12000075852251312575365323)
        ·
          refine ⟨18000113778376968863047985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12000075852251312575365323 18000113778376968863047985)
          ·
            refine ⟨13500085333782726647285989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18000113778376968863047985 13500085333782726647285989)
            ·
              refine ⟨2531266000084261246366123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13500085333782726647285989 2531266000084261246366123)
              ·
                refine ⟨3796899000126391869549185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2531266000084261246366123 3796899000126391869549185)
                ·
                  refine ⟨2847674250094793902161889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3796899000126391869549185 2847674250094793902161889)
                  ·
                    refine ⟨2135755687571095426621417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2847674250094793902161889 2135755687571095426621417)
                    ·
                      refine ⟨1601816765678321569966063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135755687571095426621417 1601816765678321569966063)
                      ·
                        rfl

theorem cell23_3119527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_3119527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119527 prefixEnd_3119527 := by exact prefixLift 3119527
  have htrace : WordTrace (prefixWord ++ tailWord_3119527) baseStart_3119527 baseEnd_3119527 := by
    simpa [prefixWord, tailWord_3119527, baseEnd_3119527] using wordTrace_append hprefix tailTrace_3119527
  have hstable : (prefixWord ++ tailWord_3119527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119527).length < 2 ^ (prefixWord ++ tailWord_3119527).sum := by decide
  have hdescent : baseEnd_3119527 < baseStart_3119527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119576 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 3, 4]
def baseStart_3119576 : Nat := 118140960795 + 3119576 * 2 ^ 59
def prefixEnd_3119576 : Nat := 4983230072969 + 3 ^ 40 * 3119576 * 2
def baseEnd_3119576 : Nat := 533947308743463959417779

theorem tailTrace_3119576 : CollatzResearch.WordTrace tailWord_3119576 prefixEnd_3119576 533947308743463959417779 := by
  unfold tailWord_3119576
  simp only [CollatzResearch.WordTrace]
  refine ⟨56890142073158204004517291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75853522764210938672689721 56890142073158204004517291)
  ·
    refine ⟨85335213109737306006775937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56890142073158204004517291 85335213109737306006775937)
    ·
      refine ⟨64001409832302979505081953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85335213109737306006775937 64001409832302979505081953)
      ·
        refine ⟨48001057374227234628811465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64001409832302979505081953 48001057374227234628811465)
        ·
          refine ⟨36000793030670425971608599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48001057374227234628811465 36000793030670425971608599)
          ·
            refine ⟨54001189546005638957412899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36000793030670425971608599 54001189546005638957412899)
            ·
              refine ⟨81001784319008458436119349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54001189546005638957412899 81001784319008458436119349)
              ·
                refine ⟨7593917279907042978386189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81001784319008458436119349 7593917279907042978386189)
                ·
                  refine ⟨2847718979965141116894821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7593917279907042978386189 2847718979965141116894821)
                  ·
                    refine ⟨533947308743463959417779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2847718979965141116894821 533947308743463959417779)
                    ·
                      rfl

theorem cell23_3119576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_3119576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119576 prefixEnd_3119576 := by exact prefixLift 3119576
  have htrace : WordTrace (prefixWord ++ tailWord_3119576) baseStart_3119576 baseEnd_3119576 := by
    simpa [prefixWord, tailWord_3119576, baseEnd_3119576] using wordTrace_append hprefix tailTrace_3119576
  have hstable : (prefixWord ++ tailWord_3119576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119576).length < 2 ^ (prefixWord ++ tailWord_3119576).sum := by decide
  have hdescent : baseEnd_3119576 < baseStart_3119576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119583 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 2, 4, 2]
def baseStart_3119583 : Nat := 118140960795 + 3119583 * 2 ^ 59
def prefixEnd_3119583 : Nat := 4983230072969 + 3 ^ 40 * 3119583 * 2
def baseEnd_3119583 : Nat := 1601845520594973350865805

theorem tailTrace_3119583 : CollatzResearch.WordTrace tailWord_3119583 prefixEnd_3119583 1601845520594973350865805 := by
  unfold tailWord_3119583
  simp only [CollatzResearch.WordTrace]
  refine ⟨113780539457291048204539403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75853692971527365469692935 113780539457291048204539403)
  ·
    refine ⟨170670809185936572306809105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113780539457291048204539403 170670809185936572306809105)
    ·
      refine ⟨128003106889452429230106829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170670809185936572306809105 128003106889452429230106829)
      ·
        refine ⟨48001165083544660961290061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128003106889452429230106829 48001165083544660961290061)
        ·
          refine ⟨18000436906329247860483773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48001165083544660961290061 18000436906329247860483773)
          ·
            refine ⟨6750163839873467947681415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18000436906329247860483773 6750163839873467947681415)
            ·
              refine ⟨10125245759810201921522123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6750163839873467947681415 10125245759810201921522123)
              ·
                refine ⟨15187868639715302882283185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10125245759810201921522123 15187868639715302882283185)
                ·
                  refine ⟨11390901479786477161712389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15187868639715302882283185 11390901479786477161712389)
                  ·
                    refine ⟨2135794027459964467821073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11390901479786477161712389 2135794027459964467821073)
                    ·
                      refine ⟨1601845520594973350865805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135794027459964467821073 1601845520594973350865805)
                      ·
                        rfl

theorem cell23_3119583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_3119583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119583 prefixEnd_3119583 := by exact prefixLift 3119583
  have htrace : WordTrace (prefixWord ++ tailWord_3119583) baseStart_3119583 baseEnd_3119583 := by
    simpa [prefixWord, tailWord_3119583, baseEnd_3119583] using wordTrace_append hprefix tailTrace_3119583
  have hstable : (prefixWord ++ tailWord_3119583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119583).length < 2 ^ (prefixWord ++ tailWord_3119583).sum := by decide
  have hdescent : baseEnd_3119583 < baseStart_3119583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119606 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_3119606 : Nat := 118140960795 + 3119606 * 2 ^ 59
def prefixEnd_3119606 : Nat := 4983230072969 + 3 ^ 40 * 3119606 * 2
def baseEnd_3119606 : Nat := 177984147850002973430911

theorem tailTrace_3119606 : CollatzResearch.WordTrace tailWord_3119606 prefixEnd_3119606 177984147850002973430911 := by
  unfold tailWord_3119606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7111336146012982695789167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75854252224138482088417781 7111336146012982695789167)
  ·
    refine ⟨10667004219019474043683751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7111336146012982695789167 10667004219019474043683751)
    ·
      refine ⟨16000506328529211065525627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10667004219019474043683751 16000506328529211065525627)
      ·
        refine ⟨24000759492793816598288441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16000506328529211065525627 24000759492793816598288441)
        ·
          refine ⟨18000569619595362448716331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24000759492793816598288441 18000569619595362448716331)
          ·
            refine ⟨27000854429393043673074497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18000569619595362448716331 27000854429393043673074497)
            ·
              refine ⟨20250640822044782754805873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27000854429393043673074497 20250640822044782754805873)
              ·
                refine ⟨15187980616533587066104405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20250640822044782754805873 15187980616533587066104405)
                ·
                  refine ⟨177984147850002973430911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15187980616533587066104405 177984147850002973430911)
                  ·
                    rfl

theorem cell23_3119606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_3119606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119606 prefixEnd_3119606 := by exact prefixLift 3119606
  have htrace : WordTrace (prefixWord ++ tailWord_3119606) baseStart_3119606 baseEnd_3119606 := by
    simpa [prefixWord, tailWord_3119606, baseEnd_3119606] using wordTrace_append hprefix tailTrace_3119606
  have hstable : (prefixWord ++ tailWord_3119606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119606).length < 2 ^ (prefixWord ++ tailWord_3119606).sum := by decide
  have hdescent : baseEnd_3119606 < baseStart_3119606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119666 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_3119666 : Nat := 118140960795 + 3119666 * 2 ^ 59
def prefixEnd_3119666 : Nat := 4983230072969 + 3 ^ 40 * 3119666 * 2
def baseEnd_3119666 : Nat := 533962713163098842042641

theorem tailTrace_3119666 : CollatzResearch.WordTrace tailWord_3119666 prefixEnd_3119666 533962713163098842042641 := by
  unfold tailWord_3119666
  simp only [CollatzResearch.WordTrace]
  refine ⟨28445891678997588344952713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75855711143993568919873901 28445891678997588344952713)
  ·
    refine ⟨21334418759248191258714535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28445891678997588344952713 21334418759248191258714535)
    ·
      refine ⟨32001628138872286888071803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21334418759248191258714535 32001628138872286888071803)
      ·
        refine ⟨48002442208308430332107705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32001628138872286888071803 48002442208308430332107705)
        ·
          refine ⟨36001831656231322749080779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48002442208308430332107705 36001831656231322749080779)
          ·
            refine ⟨54002747484346984123621169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36001831656231322749080779 54002747484346984123621169)
            ·
              refine ⟨40502060613260238092715877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54002747484346984123621169 40502060613260238092715877)
              ·
                refine ⟨7594136364986294642384227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40502060613260238092715877 7594136364986294642384227)
                ·
                  refine ⟨11391204547479441963576341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7594136364986294642384227 11391204547479441963576341)
                  ·
                    refine ⟨533962713163098842042641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11391204547479441963576341 533962713163098842042641)
                    ·
                      rfl

theorem cell23_3119666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_3119666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119666 prefixEnd_3119666 := by exact prefixLift 3119666
  have htrace : WordTrace (prefixWord ++ tailWord_3119666) baseStart_3119666 baseEnd_3119666 := by
    simpa [prefixWord, tailWord_3119666, baseEnd_3119666] using wordTrace_append hprefix tailTrace_3119666
  have hstable : (prefixWord ++ tailWord_3119666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119666).length < 2 ^ (prefixWord ++ tailWord_3119666).sum := by decide
  have hdescent : baseEnd_3119666 < baseStart_3119666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119670 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_3119670 : Nat := 118140960795 + 3119670 * 2 ^ 59
def prefixEnd_3119670 : Nat := 4983230072969 + 3 ^ 40 * 3119670 * 2
def baseEnd_3119670 : Nat := 533963397803971503492635

theorem tailTrace_3119670 : CollatzResearch.WordTrace tailWord_3119670 prefixEnd_3119670 533963397803971503492635 := by
  unfold tailWord_3119670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7111482037998491378934779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75855808405317241375304309 7111482037998491378934779)
  ·
    refine ⟨10667223056997737068402169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7111482037998491378934779 10667223056997737068402169)
    ·
      refine ⟨8000417292748302801301627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10667223056997737068402169 8000417292748302801301627)
      ·
        refine ⟨12000625939122454201952441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8000417292748302801301627 12000625939122454201952441)
        ·
          refine ⟨9000469454341840651464331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12000625939122454201952441 9000469454341840651464331)
          ·
            refine ⟨13500704181512760977196497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9000469454341840651464331 13500704181512760977196497)
            ·
              refine ⟨10125528136134570732897373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13500704181512760977196497 10125528136134570732897373)
              ·
                refine ⟨3797073051050464024836515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10125528136134570732897373 3797073051050464024836515)
                ·
                  refine ⟨5695609576575696037254773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797073051050464024836515 5695609576575696037254773)
                  ·
                    refine ⟨533963397803971503492635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5695609576575696037254773 533963397803971503492635)
                    ·
                      rfl

theorem cell23_3119670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_3119670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119670 prefixEnd_3119670 := by exact prefixLift 3119670
  have htrace : WordTrace (prefixWord ++ tailWord_3119670) baseStart_3119670 baseEnd_3119670 := by
    simpa [prefixWord, tailWord_3119670, baseEnd_3119670] using wordTrace_append hprefix tailTrace_3119670
  have hstable : (prefixWord ++ tailWord_3119670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119670).length < 2 ^ (prefixWord ++ tailWord_3119670).sum := by decide
  have hdescent : baseEnd_3119670 < baseStart_3119670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119673 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3119673 : Nat := 118140960795 + 3119673 * 2 ^ 59
def prefixEnd_3119673 : Nat := 4983230072969 + 3 ^ 40 * 3119673 * 2
def baseEnd_3119673 : Nat := 1601891733853877998740391

theorem tailTrace_3119673 : CollatzResearch.WordTrace tailWord_3119673 prefixEnd_3119673 1601891733853877998740391 := by
  unfold tailWord_3119673
  simp only [CollatzResearch.WordTrace]
  refine ⟨113783822026964993575315673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75855881351309995716877115 113783822026964993575315673)
  ·
    refine ⟨85337866520223745181486755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113783822026964993575315673 85337866520223745181486755)
    ·
      refine ⟨128006799780335617772230133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85337866520223745181486755 128006799780335617772230133)
      ·
        refine ⟨12000637479406464166146575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128006799780335617772230133 12000637479406464166146575)
        ·
          refine ⟨18000956219109696249219863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12000637479406464166146575 18000956219109696249219863)
          ·
            refine ⟨27001434328664544373829795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18000956219109696249219863 27001434328664544373829795)
            ·
              refine ⟨40502151492996816560744693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27001434328664544373829795 40502151492996816560744693)
              ·
                refine ⟨3797076702468451552569815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40502151492996816560744693 3797076702468451552569815)
                ·
                  refine ⟨5695615053702677328854723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797076702468451552569815 5695615053702677328854723)
                  ·
                    refine ⟨8543422580554015993282085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5695615053702677328854723 8543422580554015993282085)
                    ·
                      refine ⟨1601891733853877998740391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8543422580554015993282085 1601891733853877998740391)
                      ·
                        rfl

theorem cell23_3119673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3119673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119673 prefixEnd_3119673 := by exact prefixLift 3119673
  have htrace : WordTrace (prefixWord ++ tailWord_3119673) baseStart_3119673 baseEnd_3119673 := by
    simpa [prefixWord, tailWord_3119673, baseEnd_3119673] using wordTrace_append hprefix tailTrace_3119673
  have hstable : (prefixWord ++ tailWord_3119673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119673).length < 2 ^ (prefixWord ++ tailWord_3119673).sum := by decide
  have hdescent : baseEnd_3119673 < baseStart_3119673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119700 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_3119700 : Nat := 118140960795 + 3119700 * 2 ^ 59
def prefixEnd_3119700 : Nat := 4983230072969 + 3 ^ 40 * 3119700 * 2
def baseEnd_3119700 : Nat := 533968532610516464367589

theorem tailTrace_3119700 : CollatzResearch.WordTrace tailWord_3119700 prefixEnd_3119700 533968532610516464367589 := by
  unfold tailWord_3119700
  simp only [CollatzResearch.WordTrace]
  refine ⟨56892403398933588593274277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75856537865244784791032369 56892403398933588593274277)
  ·
    refine ⟨10667325637300047861238927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56892403398933588593274277 10667325637300047861238927)
    ·
      refine ⟨16000988455950071791858391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10667325637300047861238927 16000988455950071791858391)
      ·
        refine ⟨24001482683925107687787587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16000988455950071791858391 24001482683925107687787587)
        ·
          refine ⟨36002224025887661531681381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24001482683925107687787587 36002224025887661531681381)
          ·
            refine ⟨6750417004853936537190259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36002224025887661531681381 6750417004853936537190259)
            ·
              refine ⟨10125625507280904805785389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6750417004853936537190259 10125625507280904805785389)
              ·
                refine ⟨3797109565230339302169521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10125625507280904805785389 3797109565230339302169521)
                ·
                  refine ⟨2847832173922754476627141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3797109565230339302169521 2847832173922754476627141)
                  ·
                    refine ⟨533968532610516464367589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2847832173922754476627141 533968532610516464367589)
                    ·
                      rfl

theorem cell23_3119700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_3119700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119700 prefixEnd_3119700 := by exact prefixLift 3119700
  have htrace : WordTrace (prefixWord ++ tailWord_3119700) baseStart_3119700 baseEnd_3119700 := by
    simpa [prefixWord, tailWord_3119700, baseEnd_3119700] using wordTrace_append hprefix tailTrace_3119700
  have hstable : (prefixWord ++ tailWord_3119700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119700).length < 2 ^ (prefixWord ++ tailWord_3119700).sum := by decide
  have hdescent : baseEnd_3119700 < baseStart_3119700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119720 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3119720 : Nat := 118140960795 + 3119720 * 2 ^ 59
def prefixEnd_3119720 : Nat := 4983230072969 + 3 ^ 40 * 3119720 * 2
def baseEnd_3119720 : Nat := 1601915867444639314852675

theorem tailTrace_3119720 : CollatzResearch.WordTrace tailWord_3119720 prefixEnd_3119720 1601915867444639314852675 := by
  unfold tailWord_3119720
  simp only [CollatzResearch.WordTrace]
  refine ⟨56892768128897360301138307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75857024171863147068184409 56892768128897360301138307)
  ·
    refine ⟨85339152193346040451707461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56892768128897360301138307 85339152193346040451707461)
    ·
      refine ⟨16001091036252382584695149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85339152193346040451707461 16001091036252382584695149)
      ·
        refine ⟨6000409138594643469260681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16001091036252382584695149 6000409138594643469260681)
        ·
          refine ⟨4500306853945982601945511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6000409138594643469260681 4500306853945982601945511)
          ·
            refine ⟨6750460280918973902918267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500306853945982601945511 6750460280918973902918267)
            ·
              refine ⟨10125690421378460854377401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6750460280918973902918267 10125690421378460854377401)
              ·
                refine ⟨7594267816033845640783051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10125690421378460854377401 7594267816033845640783051)
                ·
                  refine ⟨11391401724050768461174577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7594267816033845640783051 11391401724050768461174577)
                  ·
                    refine ⟨8543551293038076345880933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11391401724050768461174577 8543551293038076345880933)
                    ·
                      refine ⟨1601915867444639314852675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8543551293038076345880933 1601915867444639314852675)
                      ·
                        rfl

theorem cell23_3119720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3119720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119720 prefixEnd_3119720 := by exact prefixLift 3119720
  have htrace : WordTrace (prefixWord ++ tailWord_3119720) baseStart_3119720 baseEnd_3119720 := by
    simpa [prefixWord, tailWord_3119720, baseEnd_3119720] using wordTrace_append hprefix tailTrace_3119720
  have hstable : (prefixWord ++ tailWord_3119720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119720).length < 2 ^ (prefixWord ++ tailWord_3119720).sum := by decide
  have hdescent : baseEnd_3119720 < baseStart_3119720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119723 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 4, 1, 3]
def baseStart_3119723 : Nat := 118140960795 + 3119723 * 2 ^ 59
def prefixEnd_3119723 : Nat := 4983230072969 + 3 ^ 40 * 3119723 * 2
def baseEnd_3119723 : Nat := 1601917407886602803115161

theorem tailTrace_3119723 : CollatzResearch.WordTrace tailWord_3119723 prefixEnd_3119723 1601917407886602803115161 := by
  unfold tailWord_3119723
  simp only [CollatzResearch.WordTrace]
  refine ⟨113785645676783852114635823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75857097117855901409757215 113785645676783852114635823)
  ·
    refine ⟨170678468515175778171953735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113785645676783852114635823 170678468515175778171953735)
    ·
      refine ⟨256017702772763667257930603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170678468515175778171953735 256017702772763667257930603)
      ·
        refine ⟨384026554159145500886895905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256017702772763667257930603 384026554159145500886895905)
        ·
          refine ⟨288019915619359125665171929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384026554159145500886895905 288019915619359125665171929)
          ·
            refine ⟨216014936714519344248878947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288019915619359125665171929 216014936714519344248878947)
            ·
              refine ⟨324022405071779016373318421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216014936714519344248878947 324022405071779016373318421)
              ·
                refine ⟨15188550237739641392499301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 324022405071779016373318421 15188550237739641392499301)
                ·
                  refine ⟨2847853169576182761093619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15188550237739641392499301 2847853169576182761093619)
                  ·
                    refine ⟨4271779754364274141640429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2847853169576182761093619 4271779754364274141640429)
                    ·
                      refine ⟨1601917407886602803115161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4271779754364274141640429 1601917407886602803115161)
                      ·
                        rfl

theorem cell23_3119723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 1, 3].length) (baseStart_3119723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119723 prefixEnd_3119723 := by exact prefixLift 3119723
  have htrace : WordTrace (prefixWord ++ tailWord_3119723) baseStart_3119723 baseEnd_3119723 := by
    simpa [prefixWord, tailWord_3119723, baseEnd_3119723] using wordTrace_append hprefix tailTrace_3119723
  have hstable : (prefixWord ++ tailWord_3119723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119723).length < 2 ^ (prefixWord ++ tailWord_3119723).sum := by decide
  have hdescent : baseEnd_3119723 < baseStart_3119723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119740 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_3119740 : Nat := 118140960795 + 3119740 * 2 ^ 59
def prefixEnd_3119740 : Nat := 4983230072969 + 3 ^ 40 * 3119740 * 2
def baseEnd_3119740 : Nat := 1601926137057729236602583

theorem tailTrace_3119740 : CollatzResearch.WordTrace tailWord_3119740 prefixEnd_3119740 1601926137057729236602583 := by
  unfold tailWord_3119740
  simp only [CollatzResearch.WordTrace]
  refine ⟨56893132858861132009002337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75857510478481509345336449 56893132858861132009002337)
  ·
    refine ⟨42669849644145849006751753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56893132858861132009002337 42669849644145849006751753)
    ·
      refine ⟨32002387233109386755063815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42669849644145849006751753 32002387233109386755063815)
      ·
        refine ⟨48003580849664080132595723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32002387233109386755063815 48003580849664080132595723)
        ·
          refine ⟨72005371274496120198893585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48003580849664080132595723 72005371274496120198893585)
          ·
            refine ⟨54004028455872090149170189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72005371274496120198893585 54004028455872090149170189)
            ·
              refine ⟨20251510670952033805938821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54004028455872090149170189 20251510670952033805938821)
              ·
                refine ⟨3797158250803506338613529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20251510670952033805938821 3797158250803506338613529)
                ·
                  refine ⟨2847868688102629753960147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3797158250803506338613529 2847868688102629753960147)
                  ·
                    refine ⟨4271803032153944630940221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2847868688102629753960147 4271803032153944630940221)
                    ·
                      refine ⟨1601926137057729236602583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4271803032153944630940221 1601926137057729236602583)
                      ·
                        rfl

theorem cell23_3119740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_3119740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119740 prefixEnd_3119740 := by exact prefixLift 3119740
  have htrace : WordTrace (prefixWord ++ tailWord_3119740) baseStart_3119740 baseEnd_3119740 := by
    simpa [prefixWord, tailWord_3119740, baseEnd_3119740] using wordTrace_append hprefix tailTrace_3119740
  have hstable : (prefixWord ++ tailWord_3119740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119740).length < 2 ^ (prefixWord ++ tailWord_3119740).sum := by decide
  have hdescent : baseEnd_3119740 < baseStart_3119740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119763 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 5, 4, 2]
def baseStart_3119763 : Nat := 118140960795 + 3119763 * 2 ^ 59
def prefixEnd_3119763 : Nat := 4983230072969 + 3 ^ 40 * 3119763 * 2
def baseEnd_3119763 : Nat := 1601937947112782646614977

theorem tailTrace_3119763 : CollatzResearch.WordTrace tailWord_3119763 prefixEnd_3119763 1601937947112782646614977 := by
  unfold tailWord_3119763
  simp only [CollatzResearch.WordTrace]
  refine ⟨113787104596638938946091943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75858069731092625964061295 113787104596638938946091943)
  ·
    refine ⟨170680656894958408419137915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113787104596638938946091943 170680656894958408419137915)
    ·
      refine ⟨256020985342437612628706873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170680656894958408419137915 256020985342437612628706873)
      ·
        refine ⟨192015739006828209471530155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256020985342437612628706873 192015739006828209471530155)
        ·
          refine ⟨288023608510242314207295233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192015739006828209471530155 288023608510242314207295233)
          ·
            refine ⟨216017706382681735655471425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288023608510242314207295233 216017706382681735655471425)
            ·
              refine ⟨162013279787011301741603569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216017706382681735655471425 162013279787011301741603569)
              ·
                refine ⟨121509959840258476306202677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162013279787011301741603569 121509959840258476306202677)
                ·
                  refine ⟨11391558735024232153706501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121509959840258476306202677 11391558735024232153706501)
                  ·
                    refine ⟨2135917262817043528819969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11391558735024232153706501 2135917262817043528819969)
                    ·
                      refine ⟨1601937947112782646614977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135917262817043528819969 1601937947112782646614977)
                      ·
                        rfl

theorem cell23_3119763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 4, 2].length) (baseStart_3119763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119763 prefixEnd_3119763 := by exact prefixLift 3119763
  have htrace : WordTrace (prefixWord ++ tailWord_3119763) baseStart_3119763 baseEnd_3119763 := by
    simpa [prefixWord, tailWord_3119763, baseEnd_3119763] using wordTrace_append hprefix tailTrace_3119763
  have hstable : (prefixWord ++ tailWord_3119763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119763).length < 2 ^ (prefixWord ++ tailWord_3119763).sum := by decide
  have hdescent : baseEnd_3119763 < baseStart_3119763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119780 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 1, 4, 2]
def baseStart_3119780 : Nat := 118140960795 + 3119780 * 2 ^ 59
def prefixEnd_3119780 : Nat := 4983230072969 + 3 ^ 40 * 3119780 * 2
def baseEnd_3119780 : Nat := 1601946676283909080102399

theorem tailTrace_3119780 : CollatzResearch.WordTrace tailWord_3119780 prefixEnd_3119780 1601946676283909080102399 := by
  unfold tailWord_3119780
  simp only [CollatzResearch.WordTrace]
  refine ⟨56893862318788675424730397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75858483091718233899640529 56893862318788675424730397)
  ·
    refine ⟨21335198369545753284273899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56893862318788675424730397 21335198369545753284273899)
    ·
      refine ⟨32002797554318629926410849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21335198369545753284273899 32002797554318629926410849)
      ·
        refine ⟨24002098165738972444808137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32002797554318629926410849 24002098165738972444808137)
        ·
          refine ⟨18001573624304229333606103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24002098165738972444808137 18001573624304229333606103)
          ·
            refine ⟨27002360436456344000409155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18001573624304229333606103 27002360436456344000409155)
            ·
              refine ⟨40503540654684516000613733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27002360436456344000409155 40503540654684516000613733)
              ·
                refine ⟨7594413872753346750115075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40503540654684516000613733 7594413872753346750115075)
                ·
                  refine ⟨11391620809130020125172613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7594413872753346750115075 11391620809130020125172613)
                  ·
                    refine ⟨2135928901711878773469865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11391620809130020125172613 2135928901711878773469865)
                    ·
                      refine ⟨1601946676283909080102399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2135928901711878773469865 1601946676283909080102399)
                      ·
                        rfl

theorem cell23_3119780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_3119780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119780 prefixEnd_3119780 := by exact prefixLift 3119780
  have htrace : WordTrace (prefixWord ++ tailWord_3119780) baseStart_3119780 baseEnd_3119780 := by
    simpa [prefixWord, tailWord_3119780, baseEnd_3119780] using wordTrace_append hprefix tailTrace_3119780
  have hstable : (prefixWord ++ tailWord_3119780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119780).length < 2 ^ (prefixWord ++ tailWord_3119780).sum := by decide
  have hdescent : baseEnd_3119780 < baseStart_3119780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119790 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3119790 : Nat := 118140960795 + 3119790 * 2 ^ 59
def prefixEnd_3119790 : Nat := 4983230072969 + 3 ^ 40 * 3119790 * 2
def baseEnd_3119790 : Nat := 533983937030151346992451

theorem tailTrace_3119790 : CollatzResearch.WordTrace tailWord_3119790 prefixEnd_3119790 533983937030151346992451 := by
  unfold tailWord_3119790
  simp only [CollatzResearch.WordTrace]
  refine ⟨14223511170942640319665603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75858726245027415038216549 14223511170942640319665603)
  ·
    refine ⟨21335266756413960479498405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14223511170942640319665603 21335266756413960479498405)
    ·
      refine ⟨4000362516827617589905951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21335266756413960479498405 4000362516827617589905951)
      ·
        refine ⟨6000543775241426384858927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4000362516827617589905951 6000543775241426384858927)
        ·
          refine ⟨9000815662862139577288391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6000543775241426384858927 9000815662862139577288391)
          ·
            refine ⟨13501223494293209365932587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9000815662862139577288391 13501223494293209365932587)
            ·
              refine ⟨20251835241439814048898881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13501223494293209365932587 20251835241439814048898881)
              ·
                refine ⟨15188876431079860536674161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20251835241439814048898881 15188876431079860536674161)
                ·
                  refine ⟨11391657323309895402505621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15188876431079860536674161 11391657323309895402505621)
                  ·
                    refine ⟨533983937030151346992451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11391657323309895402505621 533983937030151346992451)
                    ·
                      rfl

theorem cell23_3119790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3119790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119790 prefixEnd_3119790 := by exact prefixLift 3119790
  have htrace : WordTrace (prefixWord ++ tailWord_3119790) baseStart_3119790 baseEnd_3119790 := by
    simpa [prefixWord, tailWord_3119790, baseEnd_3119790] using wordTrace_append hprefix tailTrace_3119790
  have hstable : (prefixWord ++ tailWord_3119790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119790).length < 2 ^ (prefixWord ++ tailWord_3119790).sum := by decide
  have hdescent : baseEnd_3119790 < baseStart_3119790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119833 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 2, 5]
def baseStart_3119833 : Nat := 118140960795 + 3119833 * 2 ^ 59
def prefixEnd_3119833 : Nat := 4983230072969 + 3 ^ 40 * 3119833 * 2
def baseEnd_3119833 : Nat := 533991296919532457579885

theorem tailTrace_3119833 : CollatzResearch.WordTrace tailWord_3119833 prefixEnd_3119833 533991296919532457579885 := by
  unfold tailWord_3119833
  simp only [CollatzResearch.WordTrace]
  refine ⟨113789657706385340901140153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75859771804256893934093435 113789657706385340901140153)
  ·
    refine ⟨85342243279789005675855115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113789657706385340901140153 85342243279789005675855115)
    ·
      refine ⟨128013364919683508513782673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85342243279789005675855115 128013364919683508513782673)
      ·
        refine ⟨96010023689762631385337005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128013364919683508513782673 96010023689762631385337005)
        ·
          refine ⟨36003758883660986769501377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96010023689762631385337005 36003758883660986769501377)
          ·
            refine ⟨27002819162745740077126033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36003758883660986769501377 27002819162745740077126033)
            ·
              refine ⟨20252114372059305057844525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27002819162745740077126033 20252114372059305057844525)
              ·
                refine ⟨7594542889522239396691697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20252114372059305057844525 7594542889522239396691697)
                ·
                  refine ⟨5695907167141679547518773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7594542889522239396691697 5695907167141679547518773)
                  ·
                    refine ⟨533991296919532457579885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5695907167141679547518773 533991296919532457579885)
                    ·
                      rfl

theorem cell23_3119833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_3119833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119833 prefixEnd_3119833 := by exact prefixLift 3119833
  have htrace : WordTrace (prefixWord ++ tailWord_3119833) baseStart_3119833 baseEnd_3119833 := by
    simpa [prefixWord, tailWord_3119833, baseEnd_3119833] using wordTrace_append hprefix tailTrace_3119833
  have hstable : (prefixWord ++ tailWord_3119833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119833).length < 2 ^ (prefixWord ++ tailWord_3119833).sum := by decide
  have hdescent : baseEnd_3119833 < baseStart_3119833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119920 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 7, 1, 3]
def baseStart_3119920 : Nat := 118140960795 + 3119920 * 2 ^ 59
def prefixEnd_3119920 : Nat := 4983230072969 + 3 ^ 40 * 3119920 * 2
def baseEnd_3119920 : Nat := 1602018563575538532351755

theorem tailTrace_3119920 : CollatzResearch.WordTrace tailWord_3119920 prefixEnd_3119920 1602018563575538532351755 := by
  unfold tailWord_3119920
  simp only [CollatzResearch.WordTrace]
  refine ⟨56896415428535077379778607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75861887238046769839704809 56896415428535077379778607)
  ·
    refine ⟨85344623142802616069667911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56896415428535077379778607 85344623142802616069667911)
    ·
      refine ⟨128016934714203924104501867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85344623142802616069667911 128016934714203924104501867)
      ·
        refine ⟨192025402071305886156752801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128016934714203924104501867 192025402071305886156752801)
        ·
          refine ⟨144019051553479414617564601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192025402071305886156752801 144019051553479414617564601)
          ·
            refine ⟨108014288665109560963173451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144019051553479414617564601 108014288665109560963173451)
            ·
              refine ⟨162021432997664341444760177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108014288665109560963173451 162021432997664341444760177)
              ·
                refine ⟨121516074748248256083570133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162021432997664341444760177 121516074748248256083570133)
                ·
                  refine ⟨2848033001912068501958675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 121516074748248256083570133 2848033001912068501958675)
                  ·
                    refine ⟨4272049502868102752938013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2848033001912068501958675 4272049502868102752938013)
                    ·
                      refine ⟨1602018563575538532351755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4272049502868102752938013 1602018563575538532351755)
                      ·
                        rfl

theorem cell23_3119920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7, 1, 3].length) (baseStart_3119920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119920 prefixEnd_3119920 := by exact prefixLift 3119920
  have htrace : WordTrace (prefixWord ++ tailWord_3119920) baseStart_3119920 baseEnd_3119920 := by
    simpa [prefixWord, tailWord_3119920, baseEnd_3119920] using wordTrace_append hprefix tailTrace_3119920
  have hstable : (prefixWord ++ tailWord_3119920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119920).length < 2 ^ (prefixWord ++ tailWord_3119920).sum := by decide
  have hdescent : baseEnd_3119920 < baseStart_3119920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119960 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 1, 8, 2]
def baseStart_3119960 : Nat := 118140960795 + 3119960 * 2 ^ 59
def prefixEnd_3119960 : Nat := 4983230072969 + 3 ^ 40 * 3119960 * 2
def baseEnd_3119960 : Nat := 1602039102801718375851571

theorem tailTrace_3119960 : CollatzResearch.WordTrace tailWord_3119960 prefixEnd_3119960 1602039102801718375851571 := by
  unfold tailWord_3119960
  simp only [CollatzResearch.WordTrace]
  refine ⟨56897144888462620795506667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75862859851283494394008889 56897144888462620795506667)
  ·
    refine ⟨85345717332693931193260001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56897144888462620795506667 85345717332693931193260001)
    ·
      refine ⟨64009287999520448394945001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85345717332693931193260001 64009287999520448394945001)
      ·
        refine ⟨48006965999640336296208751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64009287999520448394945001 48006965999640336296208751)
        ·
          refine ⟨72010448999460504444313127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48006965999640336296208751 72010448999460504444313127)
          ·
            refine ⟨108015673499190756666469691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72010448999460504444313127 108015673499190756666469691)
            ·
              refine ⟨162023510248786134999704537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108015673499190756666469691 162023510248786134999704537)
              ·
                refine ⟨121517632686589601249778403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162023510248786134999704537 121517632686589601249778403)
                ·
                  refine ⟨182276449029884401874667605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121517632686589601249778403 182276449029884401874667605)
                  ·
                    refine ⟨2136052137068957834468761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 182276449029884401874667605 2136052137068957834468761)
                    ·
                      refine ⟨1602039102801718375851571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136052137068957834468761 1602039102801718375851571)
                      ·
                        rfl

theorem cell23_3119960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_3119960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119960 prefixEnd_3119960 := by exact prefixLift 3119960
  have htrace : WordTrace (prefixWord ++ tailWord_3119960) baseStart_3119960 baseEnd_3119960 := by
    simpa [prefixWord, tailWord_3119960, baseEnd_3119960] using wordTrace_append hprefix tailTrace_3119960
  have hstable : (prefixWord ++ tailWord_3119960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119960).length < 2 ^ (prefixWord ++ tailWord_3119960).sum := by decide
  have hdescent : baseEnd_3119960 < baseStart_3119960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119980 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_3119980 : Nat := 118140960795 + 3119980 * 2 ^ 59
def prefixEnd_3119980 : Nat := 4983230072969 + 3 ^ 40 * 3119980 * 2
def baseEnd_3119980 : Nat := 1602049372414808297601479

theorem tailTrace_3119980 : CollatzResearch.WordTrace tailWord_3119980 prefixEnd_3119980 1602049372414808297601479 := by
  unfold tailWord_3119980
  simp only [CollatzResearch.WordTrace]
  refine ⟨56897509618426392503370697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75863346157901856671160929 56897509618426392503370697)
  ·
    refine ⟨42673132213819794377528023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56897509618426392503370697 42673132213819794377528023)
    ·
      refine ⟨64009698320729691566292035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42673132213819794377528023 64009698320729691566292035)
      ·
        refine ⟨96014547481094537349438053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64009698320729691566292035 96014547481094537349438053)
        ·
          refine ⟨18002727652705225753019635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96014547481094537349438053 18002727652705225753019635)
          ·
            refine ⟨27004091479057838629529453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18002727652705225753019635 27004091479057838629529453)
            ·
              refine ⟨10126534304646689486073545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27004091479057838629529453 10126534304646689486073545)
              ·
                refine ⟨7594900728485017114555159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10126534304646689486073545 7594900728485017114555159)
                ·
                  refine ⟨11392351092727525671832739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7594900728485017114555159 11392351092727525671832739)
                  ·
                    refine ⟨17088526639091288507749109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11392351092727525671832739 17088526639091288507749109)
                    ·
                      refine ⟨1602049372414808297601479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17088526639091288507749109 1602049372414808297601479)
                      ·
                        rfl

theorem cell23_3119980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_3119980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119980 prefixEnd_3119980 := by exact prefixLift 3119980
  have htrace : WordTrace (prefixWord ++ tailWord_3119980) baseStart_3119980 baseEnd_3119980 := by
    simpa [prefixWord, tailWord_3119980, baseEnd_3119980] using wordTrace_append hprefix tailTrace_3119980
  have hstable : (prefixWord ++ tailWord_3119980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119980).length < 2 ^ (prefixWord ++ tailWord_3119980).sum := by decide
  have hdescent : baseEnd_3119980 < baseStart_3119980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119997 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_3119997 : Nat := 118140960795 + 3119997 * 2 ^ 59
def prefixEnd_3119997 : Nat := 4983230072969 + 3 ^ 40 * 3119997 * 2
def baseEnd_3119997 : Nat := 1602058101585934731088901

theorem tailTrace_3119997 : CollatzResearch.WordTrace tailWord_3119997 prefixEnd_3119997 1602058101585934731088901 := by
  unfold tailWord_3119997
  simp only [CollatzResearch.WordTrace]
  refine ⟨113795639277791196910110245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75863759518527464606740163 113795639277791196910110245)
  ·
    refine ⟨21336682364585849420645671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113795639277791196910110245 21336682364585849420645671)
    ·
      refine ⟨32005023546878774130968507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21336682364585849420645671 32005023546878774130968507)
      ·
        refine ⟨48007535320318161196452761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32005023546878774130968507 48007535320318161196452761)
        ·
          refine ⟨36005651490238620897339571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48007535320318161196452761 36005651490238620897339571)
          ·
            refine ⟨54008477235357931346009357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36005651490238620897339571 54008477235357931346009357)
            ·
              refine ⟨20253178963259224254753509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54008477235357931346009357 20253178963259224254753509)
              ·
                refine ⟨3797471055611104547766283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20253178963259224254753509 3797471055611104547766283)
                ·
                  refine ⟨5696206583416656821649425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797471055611104547766283 5696206583416656821649425)
                  ·
                    refine ⟨4272154937562492616237069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5696206583416656821649425 4272154937562492616237069)
                    ·
                      refine ⟨1602058101585934731088901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4272154937562492616237069 1602058101585934731088901)
                      ·
                        rfl

theorem cell23_3119997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_3119997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3119997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3119997 prefixEnd_3119997 := by exact prefixLift 3119997
  have htrace : WordTrace (prefixWord ++ tailWord_3119997) baseStart_3119997 baseEnd_3119997 := by
    simpa [prefixWord, tailWord_3119997, baseEnd_3119997] using wordTrace_append hprefix tailTrace_3119997
  have hstable : (prefixWord ++ tailWord_3119997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119997).length < 2 ^ (prefixWord ++ tailWord_3119997).sum := by decide
  have hdescent : baseEnd_3119997 < baseStart_3119997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120011 : List Nat := [1, 1, 1, 1, 4, 2, 5, 3, 1, 2, 2]
def baseStart_3120011 : Nat := 118140960795 + 3120011 * 2 ^ 59
def prefixEnd_3120011 : Nat := 4983230072969 + 3 ^ 40 * 3120011 * 2
def baseEnd_3120011 : Nat := 1602065290315097676313837

theorem tailTrace_3120011 : CollatzResearch.WordTrace tailWord_3120011 prefixEnd_3120011 1602065290315097676313837 := by
  unfold tailWord_3120011
  simp only [CollatzResearch.WordTrace]
  refine ⟨113796149899740477301119887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75864099933160318200746591 113796149899740477301119887)
  ·
    refine ⟨170694224849610715951679831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113796149899740477301119887 170694224849610715951679831)
    ·
      refine ⟨256041337274416073927519747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170694224849610715951679831 256041337274416073927519747)
      ·
        refine ⟨384062005911624110891279621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256041337274416073927519747 384062005911624110891279621)
        ·
          refine ⟨72011626108429520792114929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384062005911624110891279621 72011626108429520792114929)
          ·
            refine ⟨54008719581322140594086197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72011626108429520792114929 54008719581322140594086197)
            ·
              refine ⟨5063317460748950680695581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54008719581322140594086197 5063317460748950680695581)
              ·
                refine ⟨1898744047780856505260843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063317460748950680695581 1898744047780856505260843)
                ·
                  refine ⟨2848116071671284757891265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898744047780856505260843 2848116071671284757891265)
                  ·
                    refine ⟨2136087053753463568418449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2848116071671284757891265 2136087053753463568418449)
                    ·
                      refine ⟨1602065290315097676313837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136087053753463568418449 1602065290315097676313837)
                      ·
                        rfl

theorem cell23_3120011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 1, 2, 2].length) (baseStart_3120011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120011 prefixEnd_3120011 := by exact prefixLift 3120011
  have htrace : WordTrace (prefixWord ++ tailWord_3120011) baseStart_3120011 baseEnd_3120011 := by
    simpa [prefixWord, tailWord_3120011, baseEnd_3120011] using wordTrace_append hprefix tailTrace_3120011
  have hstable : (prefixWord ++ tailWord_3120011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120011).length < 2 ^ (prefixWord ++ tailWord_3120011).sum := by decide
  have hdescent : baseEnd_3120011 < baseStart_3120011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120022 : List Nat := [5, 3, 1, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3120022 : Nat := 118140960795 + 3120022 * 2 ^ 59
def prefixEnd_3120022 : Nat := 4983230072969 + 3 ^ 40 * 3120022 * 2
def baseEnd_3120022 : Nat := 1602070938602297133276287

theorem tailTrace_3120022 : CollatzResearch.WordTrace tailWord_3120022 prefixEnd_3120022 1602070938602297133276287 := by
  unfold tailWord_3120022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7112284443918789136235645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75864367401800417453180213 7112284443918789136235645)
  ·
    refine ⟨2667106666469545926088367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7112284443918789136235645 2667106666469545926088367)
    ·
      refine ⟨4000659999704318889132551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2667106666469545926088367 4000659999704318889132551)
      ·
        refine ⟨6000989999556478333698827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4000659999704318889132551 6000989999556478333698827)
        ·
          refine ⟨9001484999334717500548241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6000989999556478333698827 9001484999334717500548241)
          ·
            refine ⟨6751113749501038125411181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9001484999334717500548241 6751113749501038125411181)
            ·
              refine ⟨2531667656062889297029193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6751113749501038125411181 2531667656062889297029193)
              ·
                refine ⟨1898750742047166972771895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2531667656062889297029193 1898750742047166972771895)
                ·
                  refine ⟨2848126113070750459157843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898750742047166972771895 2848126113070750459157843)
                  ·
                    refine ⟨4272189169606125688736765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2848126113070750459157843 4272189169606125688736765)
                    ·
                      refine ⟨1602070938602297133276287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4272189169606125688736765 1602070938602297133276287)
                      ·
                        rfl

theorem cell23_3120022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3120022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120022 prefixEnd_3120022 := by exact prefixLift 3120022
  have htrace : WordTrace (prefixWord ++ tailWord_3120022) baseStart_3120022 baseEnd_3120022 := by
    simpa [prefixWord, tailWord_3120022, baseEnd_3120022] using wordTrace_append hprefix tailTrace_3120022
  have hstable : (prefixWord ++ tailWord_3120022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120022).length < 2 ^ (prefixWord ++ tailWord_3120022).sum := by decide
  have hdescent : baseEnd_3120022 < baseStart_3120022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120028 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_3120028 : Nat := 118140960795 + 3120028 * 2 ^ 59
def prefixEnd_3120028 : Nat := 4983230072969 + 3 ^ 40 * 3120028 * 2
def baseEnd_3120028 : Nat := 1602074019486224109801259

theorem tailTrace_3120028 : CollatzResearch.WordTrace tailWord_3120028 prefixEnd_3120028 1602074019486224109801259 := by
  unfold tailWord_3120028
  simp only [CollatzResearch.WordTrace]
  refine ⟨56898384970339444602244369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75864513293785926136325825 56898384970339444602244369)
  ·
    refine ⟨42673788727754583451683277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56898384970339444602244369 42673788727754583451683277)
    ·
      refine ⟨16002670772907968794381229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42673788727754583451683277 16002670772907968794381229)
      ·
        refine ⟨6001001539840488297892961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16002670772907968794381229 6001001539840488297892961)
        ·
          refine ⟨4500751154880366223419721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6001001539840488297892961 4500751154880366223419721)
          ·
            refine ⟨3375563366160274667564791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4500751154880366223419721 3375563366160274667564791)
            ·
              refine ⟨5063345049240412001347187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375563366160274667564791 5063345049240412001347187)
              ·
                refine ⟨7595017573860618002020781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5063345049240412001347187 7595017573860618002020781)
                ·
                  refine ⟨2848131590197731750757793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7595017573860618002020781 2848131590197731750757793)
                  ·
                    refine ⟨2136098692648298813068345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2848131590197731750757793 2136098692648298813068345)
                    ·
                      refine ⟨1602074019486224109801259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136098692648298813068345 1602074019486224109801259)
                      ·
                        rfl

theorem cell23_3120028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_3120028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120028 prefixEnd_3120028 := by exact prefixLift 3120028
  have htrace : WordTrace (prefixWord ++ tailWord_3120028) baseStart_3120028 baseEnd_3120028 := by
    simpa [prefixWord, tailWord_3120028, baseEnd_3120028] using wordTrace_append hprefix tailTrace_3120028
  have hstable : (prefixWord ++ tailWord_3120028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120028).length < 2 ^ (prefixWord ++ tailWord_3120028).sum := by decide
  have hdescent : baseEnd_3120028 < baseStart_3120028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120067 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 1, 4, 2]
def baseStart_3120067 : Nat := 118140960795 + 3120067 * 2 ^ 59
def prefixEnd_3120067 : Nat := 4983230072969 + 3 ^ 40 * 3120067 * 2
def baseEnd_3120067 : Nat := 1602094045231749457213579

theorem tailTrace_3120067 : CollatzResearch.WordTrace tailWord_3120067 prefixEnd_3120067 1602094045231749457213579 := by
  unfold tailWord_3120067
  simp only [CollatzResearch.WordTrace]
  refine ⟨113798192387537598865158455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75865461591691732576772303 113798192387537598865158455)
  ·
    refine ⟨170697288581306398297737683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113798192387537598865158455 170697288581306398297737683)
    ·
      refine ⟨256045932871959597446606525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170697288581306398297737683 256045932871959597446606525)
      ·
        refine ⟨96017224826984849042477447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256045932871959597446606525 96017224826984849042477447)
        ·
          refine ⟨144025837240477273563716171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96017224826984849042477447 144025837240477273563716171)
          ·
            refine ⟨216038755860715910345574257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144025837240477273563716171 216038755860715910345574257)
            ·
              refine ⟨162029066895536932759180693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216038755860715910345574257 162029066895536932759180693)
              ·
                refine ⟨7595112510728293723086595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162029066895536932759180693 7595112510728293723086595)
                ·
                  refine ⟨11392668766092440584629893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7595112510728293723086595 11392668766092440584629893)
                  ·
                    refine ⟨2136125393642332609618105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11392668766092440584629893 2136125393642332609618105)
                    ·
                      refine ⟨1602094045231749457213579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136125393642332609618105 1602094045231749457213579)
                      ·
                        rfl

theorem cell23_3120067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_3120067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120067 prefixEnd_3120067 := by exact prefixLift 3120067
  have htrace : WordTrace (prefixWord ++ tailWord_3120067) baseStart_3120067 baseEnd_3120067 := by
    simpa [prefixWord, tailWord_3120067, baseEnd_3120067] using wordTrace_append hprefix tailTrace_3120067
  have hstable : (prefixWord ++ tailWord_3120067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120067).length < 2 ^ (prefixWord ++ tailWord_3120067).sum := by decide
  have hdescent : baseEnd_3120067 < baseStart_3120067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120080 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_3120080 : Nat := 118140960795 + 3120080 * 2 ^ 59
def prefixEnd_3120080 : Nat := 4983230072969 + 3 ^ 40 * 3120080 * 2
def baseEnd_3120080 : Nat := 1602100720480257906351019

theorem tailTrace_3120080 : CollatzResearch.WordTrace tailWord_3120080 prefixEnd_3120080 1602100720480257906351019 := by
  unfold tailWord_3120080
  simp only [CollatzResearch.WordTrace]
  refine ⟨56899333268245251042690847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75865777690993668056921129 56899333268245251042690847)
  ·
    refine ⟨85348999902367876564036271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56899333268245251042690847 85348999902367876564036271)
    ·
      refine ⟨128023499853551814846054407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85348999902367876564036271 128023499853551814846054407)
      ·
        refine ⟨192035249780327722269081611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128023499853551814846054407 192035249780327722269081611)
        ·
          refine ⟨288052874670491583403622417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192035249780327722269081611 288052874670491583403622417)
          ·
            refine ⟨216039656002868687552716813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288052874670491583403622417 216039656002868687552716813)
            ·
              refine ⟨81014871001075757832268805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216039656002868687552716813 81014871001075757832268805)
              ·
                refine ⟨15190288312701704593550401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81014871001075757832268805 15190288312701704593550401)
                ·
                  refine ⟨11392716234526278445162801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15190288312701704593550401 11392716234526278445162801)
                  ·
                    refine ⟨8544537175894708833872101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11392716234526278445162801 8544537175894708833872101)
                    ·
                      refine ⟨1602100720480257906351019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8544537175894708833872101 1602100720480257906351019)
                      ·
                        rfl

theorem cell23_3120080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_3120080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120080 prefixEnd_3120080 := by exact prefixLift 3120080
  have htrace : WordTrace (prefixWord ++ tailWord_3120080) baseStart_3120080 baseEnd_3120080 := by
    simpa [prefixWord, tailWord_3120080, baseEnd_3120080] using wordTrace_append hprefix tailTrace_3120080
  have hstable : (prefixWord ++ tailWord_3120080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120080).length < 2 ^ (prefixWord ++ tailWord_3120080).sum := by decide
  have hdescent : baseEnd_3120080 < baseStart_3120080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120124 : List Nat := [2, 2, 2, 1, 2, 4, 2, 3, 5]
def baseStart_3120124 : Nat := 118140960795 + 3120124 * 2 ^ 59
def prefixEnd_3120124 : Nat := 4983230072969 + 3 ^ 40 * 3120124 * 2
def baseEnd_3120124 : Nat := 178013701514339526022313

theorem tailTrace_3120124 : CollatzResearch.WordTrace tailWord_3120124 prefixEnd_3120124 178013701514339526022313 := by
  unfold tailWord_3120124
  simp only [CollatzResearch.WordTrace]
  refine ⟨56900135674165548799991713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75866847565554065066655617 56900135674165548799991713)
  ·
    refine ⟨42675101755624161599993785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56900135674165548799991713 42675101755624161599993785)
    ·
      refine ⟨32006326316718121199995339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42675101755624161599993785 32006326316718121199995339)
      ·
        refine ⟨48009489475077181799993009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32006326316718121199995339 48009489475077181799993009)
        ·
          refine ⟨36007117106307886349994757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48009489475077181799993009 36007117106307886349994757)
          ·
            refine ⟨6751334457432728690624017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36007117106307886349994757 6751334457432728690624017)
            ·
              refine ⟨5063500843074546517968013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6751334457432728690624017 5063500843074546517968013)
              ·
                refine ⟨1898812816152954944238005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063500843074546517968013 1898812816152954944238005)
                ·
                  refine ⟨178013701514339526022313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1898812816152954944238005 178013701514339526022313)
                  ·
                    rfl

theorem cell23_3120124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_3120124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120124 prefixEnd_3120124 := by exact prefixLift 3120124
  have htrace : WordTrace (prefixWord ++ tailWord_3120124) baseStart_3120124 baseEnd_3120124 := by
    simpa [prefixWord, tailWord_3120124, baseEnd_3120124] using wordTrace_append hprefix tailTrace_3120124
  have hstable : (prefixWord ++ tailWord_3120124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120124).length < 2 ^ (prefixWord ++ tailWord_3120124).sum := by decide
  have hdescent : baseEnd_3120124 < baseStart_3120124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120174 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3120174 : Nat := 118140960795 + 3120174 * 2 ^ 59
def prefixEnd_3120174 : Nat := 4983230072969 + 3 ^ 40 * 3120174 * 2
def baseEnd_3120174 : Nat := 1602148987661780538575587

theorem tailTrace_3120174 : CollatzResearch.WordTrace tailWord_3120174 prefixEnd_3120174 1602148987661780538575587 := by
  unfold tailWord_3120174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14225261874768744517412947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75868063332099970759535717 14225261874768744517412947)
  ·
    refine ⟨21337892812153116776119421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14225261874768744517412947 21337892812153116776119421)
    ·
      refine ⟨8001709804557418791044783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21337892812153116776119421 8001709804557418791044783)
      ·
        refine ⟨12002564706836128186567175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8001709804557418791044783 12002564706836128186567175)
        ·
          refine ⟨18003847060254192279850763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12002564706836128186567175 18003847060254192279850763)
          ·
            refine ⟨27005770590381288419776145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18003847060254192279850763 27005770590381288419776145)
            ·
              refine ⟨20254327942785966314832109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27005770590381288419776145 20254327942785966314832109)
              ·
                refine ⟨7595372978544737368062041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20254327942785966314832109 7595372978544737368062041)
                ·
                  refine ⟨5696529733908553026046531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7595372978544737368062041 5696529733908553026046531)
                  ·
                    refine ⟨8544794600862829539069797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5696529733908553026046531 8544794600862829539069797)
                    ·
                      refine ⟨1602148987661780538575587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8544794600862829539069797 1602148987661780538575587)
                      ·
                        rfl

theorem cell23_3120174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3120174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120174 prefixEnd_3120174 := by exact prefixLift 3120174
  have htrace : WordTrace (prefixWord ++ tailWord_3120174) baseStart_3120174 baseEnd_3120174 := by
    simpa [prefixWord, tailWord_3120174, baseEnd_3120174] using wordTrace_append hprefix tailTrace_3120174
  have hstable : (prefixWord ++ tailWord_3120174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120174).length < 2 ^ (prefixWord ++ tailWord_3120174).sum := by decide
  have hdescent : baseEnd_3120174 < baseStart_3120174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120177 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 1, 4, 3]
def baseStart_3120177 : Nat := 118140960795 + 3120177 * 2 ^ 59
def prefixEnd_3120177 : Nat := 4983230072969 + 3 ^ 40 * 3120177 * 2
def baseEnd_3120177 : Nat := 1602150528103744026838073

theorem tailTrace_3120177 : CollatzResearch.WordTrace tailWord_3120177 prefixEnd_3120177 1602150528103744026838073 := by
  unfold tailWord_3120177
  simp only [CollatzResearch.WordTrace]
  refine ⟨113802204417139087651662785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75868136278092725101108523 113802204417139087651662785)
  ·
    refine ⟨85351653312854315738747089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113802204417139087651662785 85351653312854315738747089)
    ·
      refine ⟨64013739984640736804060317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85351653312854315738747089 64013739984640736804060317)
      ·
        refine ⟨24005152494240276301522619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64013739984640736804060317 24005152494240276301522619)
        ·
          refine ⟨36007728741360414452283929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24005152494240276301522619 36007728741360414452283929)
          ·
            refine ⟨27005796556020310839212947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36007728741360414452283929 27005796556020310839212947)
            ·
              refine ⟨40508694834030466258819421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27005796556020310839212947 40508694834030466258819421)
              ·
                refine ⟨15190760562761424847057283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40508694834030466258819421 15190760562761424847057283)
                ·
                  refine ⟨22786140844142137270585925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15190760562761424847057283 22786140844142137270585925)
                  ·
                    refine ⟨4272401408276650738234861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22786140844142137270585925 4272401408276650738234861)
                    ·
                      refine ⟨1602150528103744026838073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4272401408276650738234861 1602150528103744026838073)
                      ·
                        rfl

theorem cell23_3120177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_3120177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120177 prefixEnd_3120177 := by exact prefixLift 3120177
  have htrace : WordTrace (prefixWord ++ tailWord_3120177) baseStart_3120177 baseEnd_3120177 := by
    simpa [prefixWord, tailWord_3120177, baseEnd_3120177] using wordTrace_append hprefix tailTrace_3120177
  have hstable : (prefixWord ++ tailWord_3120177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120177).length < 2 ^ (prefixWord ++ tailWord_3120177).sum := by decide
  have hdescent : baseEnd_3120177 < baseStart_3120177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120224 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 5, 1, 3]
def baseStart_3120224 : Nat := 118140960795 + 3120224 * 2 ^ 59
def prefixEnd_3120224 : Nat := 4983230072969 + 3 ^ 40 * 3120224 * 2
def baseEnd_3120224 : Nat := 1602174661694505342950357

theorem tailTrace_3120224 : CollatzResearch.WordTrace tailWord_3120224 prefixEnd_3120224 1602174661694505342950357 := by
  unfold tailWord_3120224
  simp only [CollatzResearch.WordTrace]
  refine ⟨56901959323984407339311863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75869279098645876452415817 56901959323984407339311863)
  ·
    refine ⟨85352938985976611008967795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56901959323984407339311863 85352938985976611008967795)
    ·
      refine ⟨128029408478964916513451693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85352938985976611008967795 128029408478964916513451693)
      ·
        refine ⟨48011028179611843692544385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128029408478964916513451693 48011028179611843692544385)
        ·
          refine ⟨36008271134708882769408289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48011028179611843692544385 36008271134708882769408289)
          ·
            refine ⟨27006203351031662077056217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36008271134708882769408289 27006203351031662077056217)
            ·
              refine ⟨20254652513273746557792163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27006203351031662077056217 20254652513273746557792163)
              ·
                refine ⟨30381978769910619836688245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20254652513273746557792163 30381978769910619836688245)
                ·
                  refine ⟨2848310509679120609689523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30381978769910619836688245 2848310509679120609689523)
                  ·
                    refine ⟨4272465764518680914534285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2848310509679120609689523 4272465764518680914534285)
                    ·
                      refine ⟨1602174661694505342950357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4272465764518680914534285 1602174661694505342950357)
                      ·
                        rfl

theorem cell23_3120224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_3120224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120224 prefixEnd_3120224 := by exact prefixLift 3120224
  have htrace : WordTrace (prefixWord ++ tailWord_3120224) baseStart_3120224 baseEnd_3120224 := by
    simpa [prefixWord, tailWord_3120224, baseEnd_3120224] using wordTrace_append hprefix tailTrace_3120224
  have hstable : (prefixWord ++ tailWord_3120224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120224).length < 2 ^ (prefixWord ++ tailWord_3120224).sum := by decide
  have hdescent : baseEnd_3120224 < baseStart_3120224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120267 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 5]
def baseStart_3120267 : Nat := 118140960795 + 3120267 * 2 ^ 59
def prefixEnd_3120267 : Nat := 4983230072969 + 3 ^ 40 * 3120267 * 2
def baseEnd_3120267 : Nat := 1602196741362648674712659

theorem tailTrace_3120267 : CollatzResearch.WordTrace tailWord_3120267 prefixEnd_3120267 1602196741362648674712659 := by
  unfold tailWord_3120267
  simp only [CollatzResearch.WordTrace]
  refine ⟨113805486986813033022439055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75870324657875355348292703 113805486986813033022439055)
  ·
    refine ⟨170708230480219549533658583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113805486986813033022439055 170708230480219549533658583)
    ·
      refine ⟨256062345720329324300487875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170708230480219549533658583 256062345720329324300487875)
      ·
        refine ⟨384093518580493986450731813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256062345720329324300487875 384093518580493986450731813)
        ·
          refine ⟨72017534733842622459512215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384093518580493986450731813 72017534733842622459512215)
          ·
            refine ⟨108026302100763933689268323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72017534733842622459512215 108026302100763933689268323)
            ·
              refine ⟨162039453151145900533902485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108026302100763933689268323 162039453151145900533902485)
              ·
                refine ⟨7595599366459964087526679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162039453151145900533902485 7595599366459964087526679)
                ·
                  refine ⟨11393399049689946131290019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7595599366459964087526679 11393399049689946131290019)
                  ·
                    refine ⟨17090098574534919196935029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11393399049689946131290019 17090098574534919196935029)
                    ·
                      refine ⟨1602196741362648674712659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17090098574534919196935029 1602196741362648674712659)
                      ·
                        rfl

theorem cell23_3120267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 5].length) (baseStart_3120267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120267 prefixEnd_3120267 := by exact prefixLift 3120267
  have htrace : WordTrace (prefixWord ++ tailWord_3120267) baseStart_3120267 baseEnd_3120267 := by
    simpa [prefixWord, tailWord_3120267, baseEnd_3120267] using wordTrace_append hprefix tailTrace_3120267
  have hstable : (prefixWord ++ tailWord_3120267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120267).length < 2 ^ (prefixWord ++ tailWord_3120267).sum := by decide
  have hdescent : baseEnd_3120267 < baseStart_3120267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120274 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3120274 : Nat := 118140960795 + 3120274 * 2 ^ 59
def prefixEnd_3120274 : Nat := 4983230072969 + 3 ^ 40 * 3120274 * 2
def baseEnd_3120274 : Nat := 534066778575743382441709

theorem tailTrace_3120274 : CollatzResearch.WordTrace tailWord_3120274 prefixEnd_3120274 534066778575743382441709 := by
  unfold tailWord_3120274
  simp only [CollatzResearch.WordTrace]
  refine ⟨28451435574446918304485969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75870494865191782145295917 28451435574446918304485969)
  ·
    refine ⟨21338576680835188728364477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28451435574446918304485969 21338576680835188728364477)
    ·
      refine ⟨8001966255313195773136679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21338576680835188728364477 8001966255313195773136679)
      ·
        refine ⟨12002949382969793659705019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8001966255313195773136679 12002949382969793659705019)
        ·
          refine ⟨18004424074454690489557529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12002949382969793659705019 18004424074454690489557529)
          ·
            refine ⟨13503318055841017867168147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18004424074454690489557529 13503318055841017867168147)
            ·
              refine ⟨20254977083761526800752221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13503318055841017867168147 20254977083761526800752221)
              ·
                refine ⟨7595616406410572550282083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20254977083761526800752221 7595616406410572550282083)
                ·
                  refine ⟨11393424609615858825423125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7595616406410572550282083 11393424609615858825423125)
                  ·
                    refine ⟨534066778575743382441709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11393424609615858825423125 534066778575743382441709)
                    ·
                      rfl

theorem cell23_3120274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3120274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120274 prefixEnd_3120274 := by exact prefixLift 3120274
  have htrace : WordTrace (prefixWord ++ tailWord_3120274) baseStart_3120274 baseEnd_3120274 := by
    simpa [prefixWord, tailWord_3120274, baseEnd_3120274] using wordTrace_append hprefix tailTrace_3120274
  have hstable : (prefixWord ++ tailWord_3120274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120274).length < 2 ^ (prefixWord ++ tailWord_3120274).sum := by decide
  have hdescent : baseEnd_3120274 < baseStart_3120274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120298 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3120298 : Nat := 118140960795 + 3120298 * 2 ^ 59
def prefixEnd_3120298 : Nat := 4983230072969 + 3 ^ 40 * 3120298 * 2
def baseEnd_3120298 : Nat := 1602212659262938053425017

theorem tailTrace_3120298 : CollatzResearch.WordTrace tailWord_3120298 prefixEnd_3120298 1602212659262938053425017 := by
  unfold tailWord_3120298
  simp only [CollatzResearch.WordTrace]
  refine ⟨28451654412425181329204387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75871078433133816877878365 28451654412425181329204387)
  ·
    refine ⟨42677481618637771993806581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28451654412425181329204387 42677481618637771993806581)
    ·
      refine ⟨4001013901747291124419367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42677481618637771993806581 4001013901747291124419367)
      ·
        refine ⟨6001520852620936686629051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001013901747291124419367 6001520852620936686629051)
        ·
          refine ⟨9002281278931405029943577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6001520852620936686629051 9002281278931405029943577)
          ·
            refine ⟨6751710959198553772457683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9002281278931405029943577 6751710959198553772457683)
            ·
              refine ⟨10127566438797830658686525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6751710959198553772457683 10127566438797830658686525)
              ·
                refine ⟨3797837414549186497007447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10127566438797830658686525 3797837414549186497007447)
                ·
                  refine ⟨5696756121823779745511171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797837414549186497007447 5696756121823779745511171)
                  ·
                    refine ⟨8545134182735669618266757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5696756121823779745511171 8545134182735669618266757)
                    ·
                      refine ⟨1602212659262938053425017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8545134182735669618266757 1602212659262938053425017)
                      ·
                        rfl

theorem cell23_3120298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3120298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120298 prefixEnd_3120298 := by exact prefixLift 3120298
  have htrace : WordTrace (prefixWord ++ tailWord_3120298) baseStart_3120298 baseEnd_3120298 := by
    simpa [prefixWord, tailWord_3120298, baseEnd_3120298] using wordTrace_append hprefix tailTrace_3120298
  have hstable : (prefixWord ++ tailWord_3120298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120298).length < 2 ^ (prefixWord ++ tailWord_3120298).sum := by decide
  have hdescent : baseEnd_3120298 < baseStart_3120298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120317 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_3120317 : Nat := 118140960795 + 3120317 * 2 ^ 59
def prefixEnd_3120317 : Nat := 4983230072969 + 3 ^ 40 * 3120317 * 2
def baseEnd_3120317 : Nat := 534074138465124493029143

theorem tailTrace_3120317 : CollatzResearch.WordTrace tailWord_3120317 prefixEnd_3120317 534074138465124493029143 := by
  unfold tailWord_3120317
  simp only [CollatzResearch.WordTrace]
  refine ⟨113807310636631891561759205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75871540424421261041172803 113807310636631891561759205)
  ·
    refine ⟨21338870744368479667829851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113807310636631891561759205 21338870744368479667829851)
    ·
      refine ⟨32008306116552719501744777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21338870744368479667829851 32008306116552719501744777)
      ·
        refine ⟨24006229587414539626308583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32008306116552719501744777 24006229587414539626308583)
        ·
          refine ⟨36009344381121809439462875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24006229587414539626308583 36009344381121809439462875)
          ·
            refine ⟨54014016571682714159194313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36009344381121809439462875 54014016571682714159194313)
            ·
              refine ⟨40510512428762035619395735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54014016571682714159194313 40510512428762035619395735)
              ·
                refine ⟨60765768643143053429093603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40510512428762035619395735 60765768643143053429093603)
                ·
                  refine ⟨91148652964714580143640405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60765768643143053429093603 91148652964714580143640405)
                  ·
                    refine ⟨534074138465124493029143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 91148652964714580143640405 534074138465124493029143)
                    ·
                      rfl

theorem cell23_3120317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_3120317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120317 prefixEnd_3120317 := by exact prefixLift 3120317
  have htrace : WordTrace (prefixWord ++ tailWord_3120317) baseStart_3120317 baseEnd_3120317 := by
    simpa [prefixWord, tailWord_3120317, baseEnd_3120317] using wordTrace_append hprefix tailTrace_3120317
  have hstable : (prefixWord ++ tailWord_3120317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120317).length < 2 ^ (prefixWord ++ tailWord_3120317).sum := by decide
  have hdescent : baseEnd_3120317 < baseStart_3120317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120327 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_3120327 : Nat := 118140960795 + 3120327 * 2 ^ 59
def prefixEnd_3120327 : Nat := 4983230072969 + 3 ^ 40 * 3120327 * 2
def baseEnd_3120327 : Nat := 1602227550201918439962383

theorem tailTrace_3120327 : CollatzResearch.WordTrace tailWord_3120327 prefixEnd_3120327 1602227550201918439962383 := by
  unfold tailWord_3120327
  simp only [CollatzResearch.WordTrace]
  refine ⟨113807675366595663269623235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75871783577730442179748823 113807675366595663269623235)
  ·
    refine ⟨170711513049893494904434853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113807675366595663269623235 170711513049893494904434853)
    ·
      refine ⟨32008408696855030294581535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170711513049893494904434853 32008408696855030294581535)
      ·
        refine ⟨48012613045282545441872303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32008408696855030294581535 48012613045282545441872303)
        ·
          refine ⟨72018919567923818162808455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48012613045282545441872303 72018919567923818162808455)
          ·
            refine ⟨108028379351885727244212683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72018919567923818162808455 108028379351885727244212683)
            ·
              refine ⟨162042569027828590866319025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108028379351885727244212683 162042569027828590866319025)
              ·
                refine ⟨121531926770871443149739269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162042569027828590866319025 121531926770871443149739269)
                ·
                  refine ⟨22787236269538395590576113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121531926770871443149739269 22787236269538395590576113)
                  ·
                    refine ⟨17090427202153796692932085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22787236269538395590576113 17090427202153796692932085)
                    ·
                      refine ⟨1602227550201918439962383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17090427202153796692932085 1602227550201918439962383)
                      ·
                        rfl

theorem cell23_3120327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_3120327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120327 prefixEnd_3120327 := by exact prefixLift 3120327
  have htrace : WordTrace (prefixWord ++ tailWord_3120327) baseStart_3120327 baseEnd_3120327 := by
    simpa [prefixWord, tailWord_3120327, baseEnd_3120327] using wordTrace_append hprefix tailTrace_3120327
  have hstable : (prefixWord ++ tailWord_3120327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120327).length < 2 ^ (prefixWord ++ tailWord_3120327).sum := by decide
  have hdescent : baseEnd_3120327 < baseStart_3120327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120349 : List Nat := [1, 4, 3, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_3120349 : Nat := 118140960795 + 3120349 * 2 ^ 59
def prefixEnd_3120349 : Nat := 4983230072969 + 3 ^ 40 * 3120349 * 2
def baseEnd_3120349 : Nat := 1602238846776317353887283

theorem tailTrace_3120349 : CollatzResearch.WordTrace tailWord_3120349 prefixEnd_3120349 1602238846776317353887283 := by
  unfold tailWord_3120349
  simp only [CollatzResearch.WordTrace]
  refine ⟨113808477772515961026924101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75872318515010640684616067 113808477772515961026924101)
  ·
    refine ⟨21339089582346742692548269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113808477772515961026924101 21339089582346742692548269)
    ·
      refine ⟨8002158593380028509705601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21339089582346742692548269 8002158593380028509705601)
      ·
        refine ⟨6001618945035021382279201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8002158593380028509705601 6001618945035021382279201)
        ·
          refine ⟨4501214208776266036709401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6001618945035021382279201 4501214208776266036709401)
          ·
            refine ⟨3375910656582199527532051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4501214208776266036709401 3375910656582199527532051)
            ·
              refine ⟨5063865984873299291298077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375910656582199527532051 5063865984873299291298077)
              ·
                refine ⟨1898949744327487234236779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063865984873299291298077 1898949744327487234236779)
                ·
                  refine ⟨2848424616491230851355169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898949744327487234236779 2848424616491230851355169)
                  ·
                    refine ⟨2136318462368423138516377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2848424616491230851355169 2136318462368423138516377)
                    ·
                      refine ⟨1602238846776317353887283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136318462368423138516377 1602238846776317353887283)
                      ·
                        rfl

theorem cell23_3120349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_3120349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120349 prefixEnd_3120349 := by exact prefixLift 3120349
  have htrace : WordTrace (prefixWord ++ tailWord_3120349) baseStart_3120349 baseEnd_3120349 := by
    simpa [prefixWord, tailWord_3120349, baseEnd_3120349] using wordTrace_append hprefix tailTrace_3120349
  have hstable : (prefixWord ++ tailWord_3120349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120349).length < 2 ^ (prefixWord ++ tailWord_3120349).sum := by decide
  have hdescent : baseEnd_3120349 < baseStart_3120349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120374 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3120374 : Nat := 118140960795 + 3120374 * 2 ^ 59
def prefixEnd_3120374 : Nat := 4983230072969 + 3 ^ 40 * 3120374 * 2
def baseEnd_3120374 : Nat := 1602251683792679756074667

theorem tailTrace_3120374 : CollatzResearch.WordTrace tailWord_3120374 prefixEnd_3120374 1602251683792679756074667 := by
  unfold tailWord_3120374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113086849839086893536511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75872926398283593531056117 7113086849839086893536511)
  ·
    refine ⟨10669630274758630340304767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7113086849839086893536511 10669630274758630340304767)
    ·
      refine ⟨16004445412137945510457151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10669630274758630340304767 16004445412137945510457151)
      ·
        refine ⟨24006668118206918265685727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16004445412137945510457151 24006668118206918265685727)
        ·
          refine ⟨36010002177310377398528591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24006668118206918265685727 36010002177310377398528591)
          ·
            refine ⟨54015003265965566097792887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36010002177310377398528591 54015003265965566097792887)
            ·
              refine ⟨81022504898948349146689331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54015003265965566097792887 81022504898948349146689331)
              ·
                refine ⟨121533757348422523720033997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81022504898948349146689331 121533757348422523720033997)
                ·
                  refine ⟨45575159005658446395012749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121533757348422523720033997 45575159005658446395012749)
                  ·
                    refine ⟨17090684627121917398129781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45575159005658446395012749 17090684627121917398129781)
                    ·
                      refine ⟨1602251683792679756074667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17090684627121917398129781 1602251683792679756074667)
                      ·
                        rfl

theorem cell23_3120374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3120374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120374 prefixEnd_3120374 := by exact prefixLift 3120374
  have htrace : WordTrace (prefixWord ++ tailWord_3120374) baseStart_3120374 baseEnd_3120374 := by
    simpa [prefixWord, tailWord_3120374, baseEnd_3120374] using wordTrace_append hprefix tailTrace_3120374
  have hstable : (prefixWord ++ tailWord_3120374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120374).length < 2 ^ (prefixWord ++ tailWord_3120374).sum := by decide
  have hdescent : baseEnd_3120374 < baseStart_3120374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120382 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_3120382 : Nat := 118140960795 + 3120382 * 2 ^ 59
def prefixEnd_3120382 : Nat := 4983230072969 + 3 ^ 40 * 3120382 * 2
def baseEnd_3120382 : Nat := 1602255791637915724774631

theorem tailTrace_3120382 : CollatzResearch.WordTrace tailWord_3120382 prefixEnd_3120382 1602255791637915724774631 := by
  unfold tailWord_3120382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14226210172674550957859425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75873120920930938441916933 14226210172674550957859425)
  ·
    refine ⟨10669657629505913218394569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14226210172674550957859425 10669657629505913218394569)
    ·
      refine ⟨8002243222129434913795927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10669657629505913218394569 8002243222129434913795927)
      ·
        refine ⟨12003364833194152370693891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8002243222129434913795927 12003364833194152370693891)
        ·
          refine ⟨18005047249791228556040837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12003364833194152370693891 18005047249791228556040837)
          ·
            refine ⟨3375946359335855354257657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18005047249791228556040837 3375946359335855354257657)
            ·
              refine ⟨2531959769501891515693243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3375946359335855354257657 2531959769501891515693243)
              ·
                refine ⟨3797939654252837273539865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2531959769501891515693243 3797939654252837273539865)
                ·
                  refine ⟨2848454740689627955154899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3797939654252837273539865 2848454740689627955154899)
                  ·
                    refine ⟨4272682111034441932732349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2848454740689627955154899 4272682111034441932732349)
                    ·
                      refine ⟨1602255791637915724774631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4272682111034441932732349 1602255791637915724774631)
                      ·
                        rfl

theorem cell23_3120382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_3120382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120382 prefixEnd_3120382 := by exact prefixLift 3120382
  have htrace : WordTrace (prefixWord ++ tailWord_3120382) baseStart_3120382 baseEnd_3120382 := by
    simpa [prefixWord, tailWord_3120382, baseEnd_3120382] using wordTrace_append hprefix tailTrace_3120382
  have hstable : (prefixWord ++ tailWord_3120382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120382).length < 2 ^ (prefixWord ++ tailWord_3120382).sum := by decide
  have hdescent : baseEnd_3120382 < baseStart_3120382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120392 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 1, 3, 2]
def baseStart_3120392 : Nat := 118140960795 + 3120392 * 2 ^ 59
def prefixEnd_3120392 : Nat := 4983230072969 + 3 ^ 40 * 3120392 * 2
def baseEnd_3120392 : Nat := 1602260926444460685649585

theorem tailTrace_3120392 : CollatzResearch.WordTrace tailWord_3120392 prefixEnd_3120392 1602260926444460685649585 := by
  unfold tailWord_3120392
  simp only [CollatzResearch.WordTrace]
  refine ⟨56905023055680089685369715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75873364074240119580492953 56905023055680089685369715)
  ·
    refine ⟨85357534583520134528054573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56905023055680089685369715 85357534583520134528054573)
    ·
      refine ⟨32009075468820050448020465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85357534583520134528054573 32009075468820050448020465)
      ·
        refine ⟨24006806601615037836015349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32009075468820050448020465 24006806601615037836015349)
        ·
          refine ⟨2250638118901409797126439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24006806601615037836015349 2250638118901409797126439)
          ·
            refine ⟨3375957178352114695689659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250638118901409797126439 3375957178352114695689659)
            ·
              refine ⟨5063935767528172043534489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375957178352114695689659 5063935767528172043534489)
              ·
                refine ⟨3797951825646129032650867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5063935767528172043534489 3797951825646129032650867)
                ·
                  refine ⟨5696927738469193548976301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797951825646129032650867 5696927738469193548976301)
                  ·
                    refine ⟨2136347901925947580866113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5696927738469193548976301 2136347901925947580866113)
                    ·
                      refine ⟨1602260926444460685649585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136347901925947580866113 1602260926444460685649585)
                      ·
                        rfl

theorem cell23_3120392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_3120392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120392 prefixEnd_3120392 := by exact prefixLift 3120392
  have htrace : WordTrace (prefixWord ++ tailWord_3120392) baseStart_3120392 baseEnd_3120392 := by
    simpa [prefixWord, tailWord_3120392, baseEnd_3120392] using wordTrace_append hprefix tailTrace_3120392
  have hstable : (prefixWord ++ tailWord_3120392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120392).length < 2 ^ (prefixWord ++ tailWord_3120392).sum := by decide
  have hdescent : baseEnd_3120392 < baseStart_3120392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120474 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_3120474 : Nat := 118140960795 + 3120474 * 2 ^ 59
def prefixEnd_3120474 : Nat := 4983230072969 + 3 ^ 40 * 3120474 * 2
def baseEnd_3120474 : Nat := 1602303031858129364824207

theorem tailTrace_3120474 : CollatzResearch.WordTrace tailWord_3120474 prefixEnd_3120474 1602303031858129364824207 := by
  unfold tailWord_3120474
  simp only [CollatzResearch.WordTrace]
  refine ⟨28453259224265776843806119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75875357931375404916816317 28453259224265776843806119)
  ·
    refine ⟨42679888836398665265709179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28453259224265776843806119 42679888836398665265709179)
    ·
      refine ⟨64019833254597997898563769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42679888836398665265709179 64019833254597997898563769)
      ·
        refine ⟨48014874940948498423922827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64019833254597997898563769 48014874940948498423922827)
        ·
          refine ⟨72022312411422747635884241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48014874940948498423922827 72022312411422747635884241)
          ·
            refine ⟨54016734308567060726913181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72022312411422747635884241 54016734308567060726913181)
            ·
              refine ⟨20256275365712647772592443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54016734308567060726913181 20256275365712647772592443)
              ·
                refine ⟨30384413048568971658888665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20256275365712647772592443 30384413048568971658888665)
                ·
                  refine ⟨22788309786426728744166499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30384413048568971658888665 22788309786426728744166499)
                  ·
                    refine ⟨34182464679640093116249749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22788309786426728744166499 34182464679640093116249749)
                    ·
                      refine ⟨1602303031858129364824207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34182464679640093116249749 1602303031858129364824207)
                      ·
                        rfl

theorem cell23_3120474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_3120474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120474 prefixEnd_3120474 := by exact prefixLift 3120474
  have htrace : WordTrace (prefixWord ++ tailWord_3120474) baseStart_3120474 baseEnd_3120474 := by
    simpa [prefixWord, tailWord_3120474, baseEnd_3120474] using wordTrace_append hprefix tailTrace_3120474
  have hstable : (prefixWord ++ tailWord_3120474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120474).length < 2 ^ (prefixWord ++ tailWord_3120474).sum := by decide
  have hdescent : baseEnd_3120474 < baseStart_3120474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120481 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_3120481 : Nat := 118140960795 + 3120481 * 2 ^ 59
def prefixEnd_3120481 : Nat := 4983230072969 + 3 ^ 40 * 3120481 * 2
def baseEnd_3120481 : Nat := 1602306626222710837436675

theorem tailTrace_3120481 : CollatzResearch.WordTrace tailWord_3120481 prefixEnd_3120481 1602306626222710837436675 := by
  unfold tailWord_3120481
  simp only [CollatzResearch.WordTrace]
  refine ⟨113813292208037747570729297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75875528138691831713819531 113813292208037747570729297)
  ·
    refine ⟨85359969156028310678046973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113813292208037747570729297 85359969156028310678046973)
    ·
      refine ⟨32009988433510616504267615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85359969156028310678046973 32009988433510616504267615)
      ·
        refine ⟨48014982650265924756401423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32009988433510616504267615 48014982650265924756401423)
        ·
          refine ⟨72022473975398887134602135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48014982650265924756401423 72022473975398887134602135)
          ·
            refine ⟨108033710963098330701903203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72022473975398887134602135 108033710963098330701903203)
            ·
              refine ⟨162050566444647496052854805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108033710963098330701903203 162050566444647496052854805)
              ·
                refine ⟨7596120302092851377477569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162050566444647496052854805 7596120302092851377477569)
                ·
                  refine ⟨5697090226569638533108177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7596120302092851377477569 5697090226569638533108177)
                  ·
                    refine ⟨4272817669927228899831133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5697090226569638533108177 4272817669927228899831133)
                    ·
                      refine ⟨1602306626222710837436675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4272817669927228899831133 1602306626222710837436675)
                      ·
                        rfl

theorem cell23_3120481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_3120481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120481 prefixEnd_3120481 := by exact prefixLift 3120481
  have htrace : WordTrace (prefixWord ++ tailWord_3120481) baseStart_3120481 baseEnd_3120481 := by
    simpa [prefixWord, tailWord_3120481, baseEnd_3120481] using wordTrace_append hprefix tailTrace_3120481
  have hstable : (prefixWord ++ tailWord_3120481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120481).length < 2 ^ (prefixWord ++ tailWord_3120481).sum := by decide
  have hdescent : baseEnd_3120481 < baseStart_3120481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120552 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 6]
def baseStart_3120552 : Nat := 118140960795 + 3120552 * 2 ^ 59
def prefixEnd_3120552 : Nat := 4983230072969 + 3 ^ 40 * 3120552 * 2
def baseEnd_3120552 : Nat := 178038120372131117738761

theorem tailTrace_3120552 : CollatzResearch.WordTrace tailWord_3120552 prefixEnd_3120552 178038120372131117738761 := by
  unfold tailWord_3120552
  simp only [CollatzResearch.WordTrace]
  refine ⟨56907940895390263348281955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75877254527187017797709273 56907940895390263348281955)
  ·
    refine ⟨85361911343085395022422933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56907940895390263348281955 85361911343085395022422933)
    ·
      refine ⟨4001339594207127891676075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85361911343085395022422933 4001339594207127891676075)
      ·
        refine ⟨6002009391310691837514113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001339594207127891676075 6002009391310691837514113)
        ·
          refine ⟨4501507043483018878135585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6002009391310691837514113 4501507043483018878135585)
          ·
            refine ⟨3376130282612264158601689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4501507043483018878135585 3376130282612264158601689)
            ·
              refine ⟨2532097711959198118951267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376130282612264158601689 2532097711959198118951267)
              ·
                refine ⟨3798146567938797178426901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532097711959198118951267 3798146567938797178426901)
                ·
                  refine ⟨178038120372131117738761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3798146567938797178426901 178038120372131117738761)
                  ·
                    rfl

theorem cell23_3120552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 6].length) (baseStart_3120552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120552 prefixEnd_3120552 := by exact prefixLift 3120552
  have htrace : WordTrace (prefixWord ++ tailWord_3120552) baseStart_3120552 baseEnd_3120552 := by
    simpa [prefixWord, tailWord_3120552, baseEnd_3120552] using wordTrace_append hprefix tailTrace_3120552
  have hstable : (prefixWord ++ tailWord_3120552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120552).length < 2 ^ (prefixWord ++ tailWord_3120552).sum := by decide
  have hdescent : baseEnd_3120552 < baseStart_3120552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120561 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 1, 6]
def baseStart_3120561 : Nat := 118140960795 + 3120561 * 2 ^ 59
def prefixEnd_3120561 : Nat := 4983230072969 + 3 ^ 40 * 3120561 * 2
def baseEnd_3120561 : Nat := 534115901558356841478769

theorem tailTrace_3120561 : CollatzResearch.WordTrace tailWord_3120561 prefixEnd_3120561 534115901558356841478769 := by
  unfold tailWord_3120561
  simp only [CollatzResearch.WordTrace]
  refine ⟨113816210047747921233641537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75877473365165280822427691 113816210047747921233641537)
  ·
    refine ⟨85362157535810940925231153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113816210047747921233641537 85362157535810940925231153)
    ·
      refine ⟨64021618151858205693923365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85362157535810940925231153 64021618151858205693923365)
      ·
        refine ⟨12004053403473413567610631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64021618151858205693923365 12004053403473413567610631)
        ·
          refine ⟨18006080105210120351415947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12004053403473413567610631 18006080105210120351415947)
          ·
            refine ⟨27009120157815180527123921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18006080105210120351415947 27009120157815180527123921)
            ·
              refine ⟨20256840118361385395342941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27009120157815180527123921 20256840118361385395342941)
              ·
                refine ⟨7596315044385519523253603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20256840118361385395342941 7596315044385519523253603)
                ·
                  refine ⟨11394472566578279284880405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7596315044385519523253603 11394472566578279284880405)
                  ·
                    refine ⟨534115901558356841478769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11394472566578279284880405 534115901558356841478769)
                    ·
                      rfl

theorem cell23_3120561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_3120561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120561 prefixEnd_3120561 := by exact prefixLift 3120561
  have htrace : WordTrace (prefixWord ++ tailWord_3120561) baseStart_3120561 baseEnd_3120561 := by
    simpa [prefixWord, tailWord_3120561, baseEnd_3120561] using wordTrace_append hprefix tailTrace_3120561
  have hstable : (prefixWord ++ tailWord_3120561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120561).length < 2 ^ (prefixWord ++ tailWord_3120561).sum := by decide
  have hdescent : baseEnd_3120561 < baseStart_3120561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120565 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_3120565 : Nat := 118140960795 + 3120565 * 2 ^ 59
def prefixEnd_3120565 : Nat := 4983230072969 + 3 ^ 40 * 3120565 * 2
def baseEnd_3120565 : Nat := 534116586199229502928763

theorem tailTrace_3120565 : CollatzResearch.WordTrace tailWord_3120565 prefixEnd_3120565 534116586199229502928763 := by
  unfold tailWord_3120565
  simp only [CollatzResearch.WordTrace]
  refine ⟨113816355939733429916787149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75877570626488953277858099 113816355939733429916787149)
  ·
    refine ⟨42681133477400036218795181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113816355939733429916787149 42681133477400036218795181)
    ·
      refine ⟨16005425054025013582048193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42681133477400036218795181 16005425054025013582048193)
      ·
        refine ⟨12004068790518760186536145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16005425054025013582048193 12004068790518760186536145)
        ·
          refine ⟨9003051592889070139902109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12004068790518760186536145 9003051592889070139902109)
          ·
            refine ⟨3376144347333401302463291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9003051592889070139902109 3376144347333401302463291)
            ·
              refine ⟨5064216521000101953694937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376144347333401302463291 5064216521000101953694937)
              ·
                refine ⟨3798162390750076465271203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5064216521000101953694937 3798162390750076465271203)
                ·
                  refine ⟨5697243586125114697906805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798162390750076465271203 5697243586125114697906805)
                  ·
                    refine ⟨534116586199229502928763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5697243586125114697906805 534116586199229502928763)
                    ·
                      rfl

theorem cell23_3120565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_3120565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120565 prefixEnd_3120565 := by exact prefixLift 3120565
  have htrace : WordTrace (prefixWord ++ tailWord_3120565) baseStart_3120565 baseEnd_3120565 := by
    simpa [prefixWord, tailWord_3120565, baseEnd_3120565] using wordTrace_append hprefix tailTrace_3120565
  have hstable : (prefixWord ++ tailWord_3120565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120565).length < 2 ^ (prefixWord ++ tailWord_3120565).sum := by decide
  have hdescent : baseEnd_3120565 < baseStart_3120565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120568 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 1, 1, 4]
def baseStart_3120568 : Nat := 118140960795 + 3120568 * 2 ^ 59
def prefixEnd_3120568 : Nat := 4983230072969 + 3 ^ 40 * 3120568 * 2
def baseEnd_3120568 : Nat := 1602351299039651997048775

theorem tailTrace_3120568 : CollatzResearch.WordTrace tailWord_3120568 prefixEnd_3120568 1602351299039651997048775 := by
  unfold tailWord_3120568
  simp only [CollatzResearch.WordTrace]
  refine ⟨56908232679361280714573179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75877643572481707619430905 56908232679361280714573179)
  ·
    refine ⟨85362349019041921071859769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56908232679361280714573179 85362349019041921071859769)
    ·
      refine ⟨64021761764281440803894827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85362349019041921071859769 64021761764281440803894827)
      ·
        refine ⟨96032642646422161205842241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64021761764281440803894827 96032642646422161205842241)
        ·
          refine ⟨72024481984816620904381681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96032642646422161205842241 72024481984816620904381681)
          ·
            refine ⟨54018361488612465678286261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72024481984816620904381681 54018361488612465678286261)
            ·
              refine ⟨5064221389557418657339337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54018361488612465678286261 5064221389557418657339337)
              ·
                refine ⟨3798166042168063993004503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5064221389557418657339337 3798166042168063993004503)
                ·
                  refine ⟨5697249063252095989506755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798166042168063993004503 5697249063252095989506755)
                  ·
                    refine ⟨8545873594878143984260133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5697249063252095989506755 8545873594878143984260133)
                    ·
                      refine ⟨1602351299039651997048775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8545873594878143984260133 1602351299039651997048775)
                      ·
                        rfl

theorem cell23_3120568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_3120568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120568 prefixEnd_3120568 := by exact prefixLift 3120568
  have htrace : WordTrace (prefixWord ++ tailWord_3120568) baseStart_3120568 baseEnd_3120568 := by
    simpa [prefixWord, tailWord_3120568, baseEnd_3120568] using wordTrace_append hprefix tailTrace_3120568
  have hstable : (prefixWord ++ tailWord_3120568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120568).length < 2 ^ (prefixWord ++ tailWord_3120568).sum := by decide
  have hdescent : baseEnd_3120568 < baseStart_3120568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120572 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 2, 3, 2]
def baseStart_3120572 : Nat := 118140960795 + 3120572 * 2 ^ 59
def prefixEnd_3120572 : Nat := 4983230072969 + 3 ^ 40 * 3120572 * 2
def baseEnd_3120572 : Nat := 1602353352962269981398757

theorem tailTrace_3120572 : CollatzResearch.WordTrace tailWord_3120572 prefixEnd_3120572 1602353352962269981398757 := by
  unfold tailWord_3120572
  simp only [CollatzResearch.WordTrace]
  refine ⟨56908305625354035056145985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75877740833805380074861313 56908305625354035056145985)
  ·
    refine ⟨42681229219015526292109489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56908305625354035056145985 42681229219015526292109489)
    ·
      refine ⟨32010921914261644719082117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42681229219015526292109489 32010921914261644719082117)
      ·
        refine ⟨6002047858924058384827897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32010921914261644719082117 6002047858924058384827897)
        ·
          refine ⟨4501535894193043788620923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6002047858924058384827897 4501535894193043788620923)
          ·
            refine ⟨6752303841289565682931385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4501535894193043788620923 6752303841289565682931385)
            ·
              refine ⟨5064227880967174262198539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6752303841289565682931385 5064227880967174262198539)
              ·
                refine ⟨7596341821450761393297809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064227880967174262198539 7596341821450761393297809)
                ·
                  refine ⟨5697256366088071044973357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7596341821450761393297809 5697256366088071044973357)
                  ·
                    refine ⟨2136471137283026641865009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5697256366088071044973357 2136471137283026641865009)
                    ·
                      refine ⟨1602353352962269981398757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136471137283026641865009 1602353352962269981398757)
                      ·
                        rfl

theorem cell23_3120572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_3120572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120572 prefixEnd_3120572 := by exact prefixLift 3120572
  have htrace : WordTrace (prefixWord ++ tailWord_3120572) baseStart_3120572 baseEnd_3120572 := by
    simpa [prefixWord, tailWord_3120572, baseEnd_3120572] using wordTrace_append hprefix tailTrace_3120572
  have hstable : (prefixWord ++ tailWord_3120572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120572).length < 2 ^ (prefixWord ++ tailWord_3120572).sum := by decide
  have hdescent : baseEnd_3120572 < baseStart_3120572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120588 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3120588 : Nat := 118140960795 + 3120588 * 2 ^ 59
def prefixEnd_3120588 : Nat := 4983230072969 + 3 ^ 40 * 3120588 * 2
def baseEnd_3120588 : Nat := 1602361568652741918798683

theorem tailTrace_3120588 : CollatzResearch.WordTrace tailWord_3120588 prefixEnd_3120588 1602361568652741918798683 := by
  unfold tailWord_3120588
  simp only [CollatzResearch.WordTrace]
  refine ⟨56908597409325052422437209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75878129879100069896582945 56908597409325052422437209)
  ·
    refine ⟨42681448056993789316827907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56908597409325052422437209 42681448056993789316827907)
    ·
      refine ⟨64022172085490683975241861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42681448056993789316827907 64022172085490683975241861)
      ·
        refine ⟨12004157266029503245357849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64022172085490683975241861 12004157266029503245357849)
        ·
          refine ⟨9003117949522127434018387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12004157266029503245357849 9003117949522127434018387)
          ·
            refine ⟨13504676924283191151027581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9003117949522127434018387 13504676924283191151027581)
            ·
              refine ⟨5064253846606196681635343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13504676924283191151027581 5064253846606196681635343)
              ·
                refine ⟨7596380769909295022453015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064253846606196681635343 7596380769909295022453015)
                ·
                  refine ⟨11394571154863942533679523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7596380769909295022453015 11394571154863942533679523)
                  ·
                    refine ⟨17091856732295913800519285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11394571154863942533679523 17091856732295913800519285)
                    ·
                      refine ⟨1602361568652741918798683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17091856732295913800519285 1602361568652741918798683)
                      ·
                        rfl

theorem cell23_3120588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3120588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120588 prefixEnd_3120588 := by exact prefixLift 3120588
  have htrace : WordTrace (prefixWord ++ tailWord_3120588) baseStart_3120588 baseEnd_3120588 := by
    simpa [prefixWord, tailWord_3120588, baseEnd_3120588] using wordTrace_append hprefix tailTrace_3120588
  have hstable : (prefixWord ++ tailWord_3120588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120588).length < 2 ^ (prefixWord ++ tailWord_3120588).sum := by decide
  have hdescent : baseEnd_3120588 < baseStart_3120588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120596 : List Nat := [2, 4, 1, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_3120596 : Nat := 118140960795 + 3120596 * 2 ^ 59
def prefixEnd_3120596 : Nat := 4983230072969 + 3 ^ 40 * 3120596 * 2
def baseEnd_3120596 : Nat := 1602365676497977887498647

theorem tailTrace_3120596 : CollatzResearch.WordTrace tailWord_3120596 prefixEnd_3120596 1602365676497977887498647 := by
  unfold tailWord_3120596
  simp only [CollatzResearch.WordTrace]
  refine ⟨56908743301310561105582821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75878324401747414807443761 56908743301310561105582821)
  ·
    refine ⟨10670389368995730207296779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56908743301310561105582821 10670389368995730207296779)
    ·
      refine ⟨16005584053493595310945169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10670389368995730207296779 16005584053493595310945169)
      ·
        refine ⟨12004188040120196483208877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16005584053493595310945169 12004188040120196483208877)
        ·
          refine ⟨4501570515045073681203329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12004188040120196483208877 4501570515045073681203329)
          ·
            refine ⟨3376177886283805260902497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4501570515045073681203329 3376177886283805260902497)
            ·
              refine ⟨2532133414712853945676873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376177886283805260902497 2532133414712853945676873)
              ·
                refine ⟨1899100061034640459257655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2532133414712853945676873 1899100061034640459257655)
                ·
                  refine ⟨2848650091551960688886483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899100061034640459257655 2848650091551960688886483)
                  ·
                    refine ⟨4272975137327941033329725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2848650091551960688886483 4272975137327941033329725)
                    ·
                      refine ⟨1602365676497977887498647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4272975137327941033329725 1602365676497977887498647)
                      ·
                        rfl

theorem cell23_3120596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_3120596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120596 prefixEnd_3120596 := by exact prefixLift 3120596
  have htrace : WordTrace (prefixWord ++ tailWord_3120596) baseStart_3120596 baseEnd_3120596 := by
    simpa [prefixWord, tailWord_3120596, baseEnd_3120596] using wordTrace_append hprefix tailTrace_3120596
  have hstable : (prefixWord ++ tailWord_3120596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120596).length < 2 ^ (prefixWord ++ tailWord_3120596).sum := by decide
  have hdescent : baseEnd_3120596 < baseStart_3120596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120765 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_3120765 : Nat := 118140960795 + 3120765 * 2 ^ 59
def prefixEnd_3120765 : Nat := 4983230072969 + 3 ^ 40 * 3120765 * 2
def baseEnd_3120765 : Nat := 1602452454728587726285369

theorem tailTrace_3120765 : CollatzResearch.WordTrace tailWord_3120765 prefixEnd_3120765 1602452454728587726285369 := by
  unfold tailWord_3120765
  simp only [CollatzResearch.WordTrace]
  refine ⟨113823650539008864074067749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75882433692672576049378499 113823650539008864074067749)
  ·
    refine ⟨21341934476064162013887703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113823650539008864074067749 21341934476064162013887703)
    ·
      refine ⟨32012901714096243020831555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21341934476064162013887703 32012901714096243020831555)
      ·
        refine ⟨48019352571144364531247333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32012901714096243020831555 48019352571144364531247333)
        ·
          refine ⟨9003628607089568349608875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48019352571144364531247333 9003628607089568349608875)
          ·
            refine ⟨13505442910634352524413313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9003628607089568349608875 13505442910634352524413313)
            ·
              refine ⟨10129082182975764393309985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13505442910634352524413313 10129082182975764393309985)
              ·
                refine ⟨7596811637231823294982489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10129082182975764393309985 7596811637231823294982489)
                ·
                  refine ⟨5697608727923867471236867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7596811637231823294982489 5697608727923867471236867)
                  ·
                    refine ⟨8546413091885801206855301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5697608727923867471236867 8546413091885801206855301)
                    ·
                      refine ⟨1602452454728587726285369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8546413091885801206855301 1602452454728587726285369)
                      ·
                        rfl

theorem cell23_3120765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_3120765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120765 prefixEnd_3120765 := by exact prefixLift 3120765
  have htrace : WordTrace (prefixWord ++ tailWord_3120765) baseStart_3120765 baseEnd_3120765 := by
    simpa [prefixWord, tailWord_3120765, baseEnd_3120765] using wordTrace_append hprefix tailTrace_3120765
  have hstable : (prefixWord ++ tailWord_3120765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120765).length < 2 ^ (prefixWord ++ tailWord_3120765).sum := by decide
  have hdescent : baseEnd_3120765 < baseStart_3120765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120782 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2]
def baseStart_3120782 : Nat := 118140960795 + 3120782 * 2 ^ 59
def prefixEnd_3120782 : Nat := 4983230072969 + 3 ^ 40 * 3120782 * 2
def baseEnd_3120782 : Nat := 1602461183899714159772791

theorem tailTrace_3120782 : CollatzResearch.WordTrace tailWord_3120782 prefixEnd_3120782 1602461183899714159772791 := by
  unfold tailWord_3120782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14228033822493409497179575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75882847053298183984957733 14228033822493409497179575)
  ·
    refine ⟨21342050733740114245769363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14228033822493409497179575 21342050733740114245769363)
    ·
      refine ⟨32013076100610171368654045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21342050733740114245769363 32013076100610171368654045)
      ·
        refine ⟨12004903537728814263245267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32013076100610171368654045 12004903537728814263245267)
        ·
          refine ⟨18007355306593221394867901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12004903537728814263245267 18007355306593221394867901)
          ·
            refine ⟨6752758239972458023075463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18007355306593221394867901 6752758239972458023075463)
            ·
              refine ⟨10129137359958687034613195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752758239972458023075463 10129137359958687034613195)
              ·
                refine ⟨15193706039938030551919793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129137359958687034613195 15193706039938030551919793)
                ·
                  refine ⟨11395279529953522913939845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15193706039938030551919793 11395279529953522913939845)
                  ·
                    refine ⟨2136614911866285546363721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11395279529953522913939845 2136614911866285546363721)
                    ·
                      refine ⟨1602461183899714159772791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136614911866285546363721 1602461183899714159772791)
                      ·
                        rfl

theorem cell23_3120782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_3120782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120782 prefixEnd_3120782 := by exact prefixLift 3120782
  have htrace : WordTrace (prefixWord ++ tailWord_3120782) baseStart_3120782 baseEnd_3120782 := by
    simpa [prefixWord, tailWord_3120782, baseEnd_3120782] using wordTrace_append hprefix tailTrace_3120782
  have hstable : (prefixWord ++ tailWord_3120782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120782).length < 2 ^ (prefixWord ++ tailWord_3120782).sum := by decide
  have hdescent : baseEnd_3120782 < baseStart_3120782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120799 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3120799 : Nat := 118140960795 + 3120799 * 2 ^ 59
def prefixEnd_3120799 : Nat := 4983230072969 + 3 ^ 40 * 3120799 * 2
def baseEnd_3120799 : Nat := 1602469913070840593260213

theorem tailTrace_3120799 : CollatzResearch.WordTrace tailWord_3120799 prefixEnd_3120799 1602469913070840593260213 := by
  unfold tailWord_3120799
  simp only [CollatzResearch.WordTrace]
  refine ⟨113824890620885687880805451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75883260413923791920536967 113824890620885687880805451)
  ·
    refine ⟨170737335931328531821208177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113824890620885687880805451 170737335931328531821208177)
    ·
      refine ⟨128053001948496398865906133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170737335931328531821208177 128053001948496398865906133)
      ·
        refine ⟨3001242233167884348419675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 128053001948496398865906133 3001242233167884348419675)
        ·
          refine ⟨4501863349751826522629513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3001242233167884348419675 4501863349751826522629513)
          ·
            refine ⟨3376397512313869891972135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4501863349751826522629513 3376397512313869891972135)
            ·
              refine ⟨5064596268470804837958203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376397512313869891972135 5064596268470804837958203)
              ·
                refine ⟨7596894402706207256937305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064596268470804837958203 7596894402706207256937305)
                ·
                  refine ⟨5697670802029655442702979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7596894402706207256937305 5697670802029655442702979)
                  ·
                    refine ⟨8546506203044483164054469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5697670802029655442702979 8546506203044483164054469)
                    ·
                      refine ⟨1602469913070840593260213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8546506203044483164054469 1602469913070840593260213)
                      ·
                        rfl

theorem cell23_3120799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3120799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120799 prefixEnd_3120799 := by exact prefixLift 3120799
  have htrace : WordTrace (prefixWord ++ tailWord_3120799) baseStart_3120799 baseEnd_3120799 := by
    simpa [prefixWord, tailWord_3120799, baseEnd_3120799] using wordTrace_append hprefix tailTrace_3120799
  have hstable : (prefixWord ++ tailWord_3120799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120799).length < 2 ^ (prefixWord ++ tailWord_3120799).sum := by decide
  have hdescent : baseEnd_3120799 < baseStart_3120799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120815 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 5, 1, 3]
def baseStart_3120815 : Nat := 118140960795 + 3120815 * 2 ^ 59
def prefixEnd_3120815 : Nat := 4983230072969 + 3 ^ 40 * 3120815 * 2
def baseEnd_3120815 : Nat := 1602478128761312530660139

theorem tailTrace_3120815 : CollatzResearch.WordTrace tailWord_3120815 prefixEnd_3120815 1602478128761312530660139 := by
  unfold tailWord_3120815
  simp only [CollatzResearch.WordTrace]
  refine ⟨113825474188827722613387899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75883649459218481742258599 113825474188827722613387899)
  ·
    refine ⟨170738211283241583920081849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113825474188827722613387899 170738211283241583920081849)
    ·
      refine ⟨128053658462431187940061387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170738211283241583920081849 128053658462431187940061387)
      ·
        refine ⟨192080487693646781910092081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128053658462431187940061387 192080487693646781910092081)
        ·
          refine ⟨144060365770235086432569061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192080487693646781910092081 144060365770235086432569061)
          ·
            refine ⟨27011318581919078706106699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144060365770235086432569061 27011318581919078706106699)
            ·
              refine ⟨40516977872878618059160049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27011318581919078706106699 40516977872878618059160049)
              ·
                refine ⟨30387733404658963544370037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40516977872878618059160049 30387733404658963544370037)
                ·
                  refine ⟨2848850006686777832284691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30387733404658963544370037 2848850006686777832284691)
                  ·
                    refine ⟨4273275010030166748427037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2848850006686777832284691 4273275010030166748427037)
                    ·
                      refine ⟨1602478128761312530660139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4273275010030166748427037 1602478128761312530660139)
                      ·
                        rfl

theorem cell23_3120815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 1, 3].length) (baseStart_3120815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120815 prefixEnd_3120815 := by exact prefixLift 3120815
  have htrace : WordTrace (prefixWord ++ tailWord_3120815) baseStart_3120815 baseEnd_3120815 := by
    simpa [prefixWord, tailWord_3120815, baseEnd_3120815] using wordTrace_append hprefix tailTrace_3120815
  have hstable : (prefixWord ++ tailWord_3120815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120815).length < 2 ^ (prefixWord ++ tailWord_3120815).sum := by decide
  have hdescent : baseEnd_3120815 < baseStart_3120815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120822 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_3120822 : Nat := 118140960795 + 3120822 * 2 ^ 59
def prefixEnd_3120822 : Nat := 4983230072969 + 3 ^ 40 * 3120822 * 2
def baseEnd_3120822 : Nat := 178053524791766000363623

theorem tailTrace_3120822 : CollatzResearch.WordTrace tailWord_3120822 prefixEnd_3120822 178053524791766000363623 := by
  unfold tailWord_3120822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7114108093737647675555795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75883819666534908539261813 7114108093737647675555795)
  ·
    refine ⟨10671162140606471513333693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7114108093737647675555795 10671162140606471513333693)
    ·
      refine ⟨4001685802727426817500135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10671162140606471513333693 4001685802727426817500135)
      ·
        refine ⟨6002528704091140226250203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001685802727426817500135 6002528704091140226250203)
        ·
          refine ⟨9003793056136710339375305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002528704091140226250203 9003793056136710339375305)
          ·
            refine ⟨6752844792102532754531479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9003793056136710339375305 6752844792102532754531479)
            ·
              refine ⟨10129267188153799131797219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752844792102532754531479 10129267188153799131797219)
              ·
                refine ⟨15193900782230698697695829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129267188153799131797219 15193900782230698697695829)
                ·
                  refine ⟨178053524791766000363623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15193900782230698697695829 178053524791766000363623)
                  ·
                    rfl

theorem cell23_3120822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_3120822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120822 prefixEnd_3120822 := by exact prefixLift 3120822
  have htrace : WordTrace (prefixWord ++ tailWord_3120822) baseStart_3120822 baseEnd_3120822 := by
    simpa [prefixWord, tailWord_3120822, baseEnd_3120822] using wordTrace_append hprefix tailTrace_3120822
  have hstable : (prefixWord ++ tailWord_3120822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120822).length < 2 ^ (prefixWord ++ tailWord_3120822).sum := by decide
  have hdescent : baseEnd_3120822 < baseStart_3120822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120832 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 3, 1, 3]
def baseStart_3120832 : Nat := 118140960795 + 3120832 * 2 ^ 59
def prefixEnd_3120832 : Nat := 4983230072969 + 3 ^ 40 * 3120832 * 2
def baseEnd_3120832 : Nat := 1602486857932438964147561

theorem tailTrace_3120832 : CollatzResearch.WordTrace tailWord_3120832 prefixEnd_3120832 1602486857932438964147561 := by
  unfold tailWord_3120832
  simp only [CollatzResearch.WordTrace]
  refine ⟨56913047114883067258378375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75884062819844089677837833 56913047114883067258378375)
  ·
    refine ⟨85369570672324600887567563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56913047114883067258378375 85369570672324600887567563)
    ·
      refine ⟨128054356008486901331351345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85369570672324600887567563 128054356008486901331351345)
      ·
        refine ⟨96040767006365175998513509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128054356008486901331351345 96040767006365175998513509)
        ·
          refine ⟨18007643813693470499721283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96040767006365175998513509 18007643813693470499721283)
          ·
            refine ⟨27011465720540205749581925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18007643813693470499721283 27011465720540205749581925)
            ·
              refine ⟨5064649822601288578046611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27011465720540205749581925 5064649822601288578046611)
              ·
                refine ⟨7596974733901932867069917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064649822601288578046611 7596974733901932867069917)
                ·
                  refine ⟨2848865525213224825151219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7596974733901932867069917 2848865525213224825151219)
                  ·
                    refine ⟨4273298287819837237726829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2848865525213224825151219 4273298287819837237726829)
                    ·
                      refine ⟨1602486857932438964147561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4273298287819837237726829 1602486857932438964147561)
                      ·
                        rfl

theorem cell23_3120832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_3120832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120832 prefixEnd_3120832 := by exact prefixLift 3120832
  have htrace : WordTrace (prefixWord ++ tailWord_3120832) baseStart_3120832 baseEnd_3120832 := by
    simpa [prefixWord, tailWord_3120832, baseEnd_3120832] using wordTrace_append hprefix tailTrace_3120832
  have hstable : (prefixWord ++ tailWord_3120832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120832).length < 2 ^ (prefixWord ++ tailWord_3120832).sum := by decide
  have hdescent : baseEnd_3120832 < baseStart_3120832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120848 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 1, 6]
def baseStart_3120848 : Nat := 118140960795 + 3120848 * 2 ^ 59
def prefixEnd_3120848 : Nat := 4983230072969 + 3 ^ 40 * 3120848 * 2
def baseEnd_3120848 : Nat := 534165024540970300515829

theorem tailTrace_3120848 : CollatzResearch.WordTrace tailWord_3120848 prefixEnd_3120848 534165024540970300515829 := by
  unfold tailWord_3120848
  simp only [CollatzResearch.WordTrace]
  refine ⟨56913338898854084624669599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75884451865138779499559465 56913338898854084624669599)
  ·
    refine ⟨85370008348281126937004399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56913338898854084624669599 85370008348281126937004399)
    ·
      refine ⟨128055012522421690405506599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85370008348281126937004399 128055012522421690405506599)
      ·
        refine ⟨192082518783632535608259899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128055012522421690405506599 192082518783632535608259899)
        ·
          refine ⟨288123778175448803412389849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192082518783632535608259899 288123778175448803412389849)
          ·
            refine ⟨216092833631586602559292387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288123778175448803412389849 216092833631586602559292387)
            ·
              refine ⟨324139250447379903838938581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216092833631586602559292387 324139250447379903838938581)
              ·
                refine ⟨7597013682360466496225123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 324139250447379903838938581 7597013682360466496225123)
                ·
                  refine ⟨11395520523540699744337685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7597013682360466496225123 11395520523540699744337685)
                  ·
                    refine ⟨534165024540970300515829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11395520523540699744337685 534165024540970300515829)
                    ·
                      rfl

theorem cell23_3120848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_3120848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120848 prefixEnd_3120848 := by exact prefixLift 3120848
  have htrace : WordTrace (prefixWord ++ tailWord_3120848) baseStart_3120848 baseEnd_3120848 := by
    simpa [prefixWord, tailWord_3120848, baseEnd_3120848] using wordTrace_append hprefix tailTrace_3120848
  have hstable : (prefixWord ++ tailWord_3120848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120848).length < 2 ^ (prefixWord ++ tailWord_3120848).sum := by decide
  have hdescent : baseEnd_3120848 < baseStart_3120848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120852 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_3120852 : Nat := 118140960795 + 3120852 * 2 ^ 59
def prefixEnd_3120852 : Nat := 4983230072969 + 3 ^ 40 * 3120852 * 2
def baseEnd_3120852 : Nat := 534165709181842961965823

theorem tailTrace_3120852 : CollatzResearch.WordTrace tailWord_3120852 prefixEnd_3120852 534165709181842961965823 := by
  unfold tailWord_3120852
  simp only [CollatzResearch.WordTrace]
  refine ⟨56913411844846838966242405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75884549126462451954989873 56913411844846838966242405)
  ·
    refine ⟨10671264720908782306170451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56913411844846838966242405 10671264720908782306170451)
    ·
      refine ⟨16006897081363173459255677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10671264720908782306170451 16006897081363173459255677)
      ·
        refine ⟨6002586405511190047220879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16006897081363173459255677 6002586405511190047220879)
        ·
          refine ⟨9003879608266785070831319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002586405511190047220879 9003879608266785070831319)
          ·
            refine ⟨13505819412400177606246979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9003879608266785070831319 13505819412400177606246979)
            ·
              refine ⟨20258729118600266409370469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13505819412400177606246979 20258729118600266409370469)
              ·
                refine ⟨3798511709737549951756963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20258729118600266409370469 3798511709737549951756963)
                ·
                  refine ⟨5697767564606324927635445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798511709737549951756963 5697767564606324927635445)
                  ·
                    refine ⟨534165709181842961965823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5697767564606324927635445 534165709181842961965823)
                    ·
                      rfl

theorem cell23_3120852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_3120852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120852 prefixEnd_3120852 := by exact prefixLift 3120852
  have htrace : WordTrace (prefixWord ++ tailWord_3120852) baseStart_3120852 baseEnd_3120852 := by
    simpa [prefixWord, tailWord_3120852, baseEnd_3120852] using wordTrace_append hprefix tailTrace_3120852
  have hstable : (prefixWord ++ tailWord_3120852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120852).length < 2 ^ (prefixWord ++ tailWord_3120852).sum := by decide
  have hdescent : baseEnd_3120852 < baseStart_3120852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120855 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 2, 6, 2]
def baseStart_3120855 : Nat := 118140960795 + 3120855 * 2 ^ 59
def prefixEnd_3120855 : Nat := 4983230072969 + 3 ^ 40 * 3120855 * 2
def baseEnd_3120855 : Nat := 1602498667987492374159955

theorem tailTrace_3120855 : CollatzResearch.WordTrace tailWord_3120855 prefixEnd_3120855 1602498667987492374159955 := by
  unfold tailWord_3120855
  simp only [CollatzResearch.WordTrace]
  refine ⟨113826933108682809444844019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75884622072455206296562679 113826933108682809444844019)
  ·
    refine ⟨170740399663024214167266029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113826933108682809444844019 170740399663024214167266029)
    ·
      refine ⟨64027649873634080312724761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170740399663024214167266029 64027649873634080312724761)
      ·
        refine ⟨48020737405225560234543571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64027649873634080312724761 48020737405225560234543571)
        ·
          refine ⟨72031106107838340351815357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48020737405225560234543571 72031106107838340351815357)
          ·
            refine ⟨27011664790439377631930759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72031106107838340351815357 27011664790439377631930759)
            ·
              refine ⟨40517497185659066447896139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27011664790439377631930759 40517497185659066447896139)
              ·
                refine ⟨60776245778488599671844209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40517497185659066447896139 60776245778488599671844209)
                ·
                  refine ⟨45582184333866449753883157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60776245778488599671844209 45582184333866449753883157)
                  ·
                    refine ⟨2136664890649989832213273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45582184333866449753883157 2136664890649989832213273)
                    ·
                      refine ⟨1602498667987492374159955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136664890649989832213273 1602498667987492374159955)
                      ·
                        rfl

theorem cell23_3120855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_3120855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120855 prefixEnd_3120855 := by exact prefixLift 3120855
  have htrace : WordTrace (prefixWord ++ tailWord_3120855) baseStart_3120855 baseEnd_3120855 := by
    simpa [prefixWord, tailWord_3120855, baseEnd_3120855] using wordTrace_append hprefix tailTrace_3120855
  have hstable : (prefixWord ++ tailWord_3120855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120855).length < 2 ^ (prefixWord ++ tailWord_3120855).sum := by decide
  have hdescent : baseEnd_3120855 < baseStart_3120855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120872 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_3120872 : Nat := 118140960795 + 3120872 * 2 ^ 59
def prefixEnd_3120872 : Nat := 4983230072969 + 3 ^ 40 * 3120872 * 2
def baseEnd_3120872 : Nat := 1602507397158618807647377

theorem tailTrace_3120872 : CollatzResearch.WordTrace tailWord_3120872 prefixEnd_3120872 1602507397158618807647377 := by
  unfold tailWord_3120872
  simp only [CollatzResearch.WordTrace]
  refine ⟨56913776574810610674106435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75885035433080814232141913 56913776574810610674106435)
  ·
    refine ⟨85370664862215916011159653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56913776574810610674106435 85370664862215916011159653)
    ·
      refine ⟨16006999661665484252092435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85370664862215916011159653 16006999661665484252092435)
      ·
        refine ⟨24010499492498226378138653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16006999661665484252092435 24010499492498226378138653)
        ·
          refine ⟨9003937309686834891801995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24010499492498226378138653 9003937309686834891801995)
          ·
            refine ⟨13505905964530252337702993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9003937309686834891801995 13505905964530252337702993)
            ·
              refine ⟨10129429473397689253277245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13505905964530252337702993 10129429473397689253277245)
              ·
                refine ⟨3798536052524133469978967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10129429473397689253277245 3798536052524133469978967)
                ·
                  refine ⟨5697804078786200204968451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798536052524133469978967 5697804078786200204968451)
                  ·
                    refine ⟨8546706118179300307452677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5697804078786200204968451 8546706118179300307452677)
                    ·
                      refine ⟨1602507397158618807647377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8546706118179300307452677 1602507397158618807647377)
                      ·
                        rfl

theorem cell23_3120872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_3120872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120872 prefixEnd_3120872 := by exact prefixLift 3120872
  have htrace : WordTrace (prefixWord ++ tailWord_3120872) baseStart_3120872 baseEnd_3120872 := by
    simpa [prefixWord, tailWord_3120872, baseEnd_3120872] using wordTrace_append hprefix tailTrace_3120872
  have hstable : (prefixWord ++ tailWord_3120872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120872).length < 2 ^ (prefixWord ++ tailWord_3120872).sum := by decide
  have hdescent : baseEnd_3120872 < baseStart_3120872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120882 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_3120882 : Nat := 118140960795 + 3120882 * 2 ^ 59
def prefixEnd_3120882 : Nat := 4983230072969 + 3 ^ 40 * 3120882 * 2
def baseEnd_3120882 : Nat := 534170843988387922840777

theorem tailTrace_3120882 : CollatzResearch.WordTrace tailWord_3120882 prefixEnd_3120882 534170843988387922840777 := by
  unfold tailWord_3120882
  simp only [CollatzResearch.WordTrace]
  refine ⟨28456979469896248264019225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75885278586389995370717933 28456979469896248264019225)
  ·
    refine ⟨21342734602422186198014419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28456979469896248264019225 21342734602422186198014419)
    ·
      refine ⟨32014101903633279297021629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21342734602422186198014419 32014101903633279297021629)
      ·
        refine ⟨12005288213862479736383111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32014101903633279297021629 12005288213862479736383111)
        ·
          refine ⟨18007932320793719604574667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12005288213862479736383111 18007932320793719604574667)
          ·
            refine ⟨27011898481190579406862001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18007932320793719604574667 27011898481190579406862001)
            ·
              refine ⟨20258923860892934555146501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27011898481190579406862001 20258923860892934555146501)
              ·
                refine ⟨3798548223917425229089969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20258923860892934555146501 3798548223917425229089969)
                ·
                  refine ⟨2848911167938068921817477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3798548223917425229089969 2848911167938068921817477)
                  ·
                    refine ⟨534170843988387922840777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2848911167938068921817477 534170843988387922840777)
                    ·
                      rfl

theorem cell23_3120882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_3120882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120882 prefixEnd_3120882 := by exact prefixLift 3120882
  have htrace : WordTrace (prefixWord ++ tailWord_3120882) baseStart_3120882 baseEnd_3120882 := by
    simpa [prefixWord, tailWord_3120882, baseEnd_3120882] using wordTrace_append hprefix tailTrace_3120882
  have hstable : (prefixWord ++ tailWord_3120882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120882).length < 2 ^ (prefixWord ++ tailWord_3120882).sum := by decide
  have hdescent : baseEnd_3120882 < baseStart_3120882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120905 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 1, 3, 3]
def baseStart_3120905 : Nat := 118140960795 + 3120905 * 2 ^ 59
def prefixEnd_3120905 : Nat := 4983230072969 + 3 ^ 40 * 3120905 * 2
def baseEnd_3120905 : Nat := 1602524342020217178534725

theorem tailTrace_3120905 : CollatzResearch.WordTrace tailWord_3120905 prefixEnd_3120905 1602524342020217178534725 := by
  unfold tailWord_3120905
  simp only [CollatzResearch.WordTrace]
  refine ⟨113828756758501667984164169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75885837839001111989442779 113828756758501667984164169)
  ·
    refine ⟨85371567568876250988123127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113828756758501667984164169 85371567568876250988123127)
    ·
      refine ⟨128057351353314376482184691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85371567568876250988123127 128057351353314376482184691)
      ·
        refine ⟨192086027029971564723277037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128057351353314376482184691 192086027029971564723277037)
        ·
          refine ⟨72032260136239336771228889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192086027029971564723277037 72032260136239336771228889)
          ·
            refine ⟨54024195102179502578421667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72032260136239336771228889 54024195102179502578421667)
            ·
              refine ⟨81036292653269253867632501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54024195102179502578421667 81036292653269253867632501)
              ·
                refine ⟨7597152436243992550090547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81036292653269253867632501 7597152436243992550090547)
                ·
                  refine ⟨11395728654365988825135821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7597152436243992550090547 11395728654365988825135821)
                  ·
                    refine ⟨4273398245387245809425933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11395728654365988825135821 4273398245387245809425933)
                    ·
                      refine ⟨1602524342020217178534725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4273398245387245809425933 1602524342020217178534725)
                      ·
                        rfl

theorem cell23_3120905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3, 3].length) (baseStart_3120905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120905 prefixEnd_3120905 := by exact prefixLift 3120905
  have htrace : WordTrace (prefixWord ++ tailWord_3120905) baseStart_3120905 baseEnd_3120905 := by
    simpa [prefixWord, tailWord_3120905, baseEnd_3120905] using wordTrace_append hprefix tailTrace_3120905
  have hstable : (prefixWord ++ tailWord_3120905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120905).length < 2 ^ (prefixWord ++ tailWord_3120905).sum := by decide
  have hdescent : baseEnd_3120905 < baseStart_3120905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120916 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3120916 : Nat := 118140960795 + 3120916 * 2 ^ 59
def prefixEnd_3120916 : Nat := 4983230072969 + 3 ^ 40 * 3120916 * 2
def baseEnd_3120916 : Nat := 534176663435805545165725

theorem tailTrace_3120916 : CollatzResearch.WordTrace tailWord_3120916 prefixEnd_3120916 534176663435805545165725 := by
  unfold tailWord_3120916
  simp only [CollatzResearch.WordTrace]
  refine ⟨56914578980730908431407301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75886105307641211241876401 56914578980730908431407301)
  ·
    refine ⟨10671483558887045330888869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56914578980730908431407301 10671483558887045330888869)
    ·
      refine ⟨2000903167291320999541663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10671483558887045330888869 2000903167291320999541663)
      ·
        refine ⟨3001354750936981499312495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2000903167291320999541663 3001354750936981499312495)
        ·
          refine ⟨4502032126405472248968743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3001354750936981499312495 4502032126405472248968743)
          ·
            refine ⟨6753048189608208373453115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4502032126405472248968743 6753048189608208373453115)
            ·
              refine ⟨10129572284412312560179673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6753048189608208373453115 10129572284412312560179673)
              ·
                refine ⟨7597179213309234420134755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10129572284412312560179673 7597179213309234420134755)
                ·
                  refine ⟨11395768819963851630202133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7597179213309234420134755 11395768819963851630202133)
                  ·
                    refine ⟨534176663435805545165725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11395768819963851630202133 534176663435805545165725)
                    ·
                      rfl

theorem cell23_3120916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3120916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120916 prefixEnd_3120916 := by exact prefixLift 3120916
  have htrace : WordTrace (prefixWord ++ tailWord_3120916) baseStart_3120916 baseEnd_3120916 := by
    simpa [prefixWord, tailWord_3120916, baseEnd_3120916] using wordTrace_append hprefix tailTrace_3120916
  have hstable : (prefixWord ++ tailWord_3120916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120916).length < 2 ^ (prefixWord ++ tailWord_3120916).sum := by decide
  have hdescent : baseEnd_3120916 < baseStart_3120916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120922 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3]
def baseStart_3120922 : Nat := 118140960795 + 3120922 * 2 ^ 59
def prefixEnd_3120922 : Nat := 4983230072969 + 3 ^ 40 * 3120922 * 2
def baseEnd_3120922 : Nat := 1602533071191343612022147

theorem tailTrace_3120922 : CollatzResearch.WordTrace tailWord_3120922 prefixEnd_3120922 1602533071191343612022147 := by
  unfold tailWord_3120922
  simp only [CollatzResearch.WordTrace]
  refine ⟨28457344199860019971883255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75886251199626719925022013 28457344199860019971883255)
  ·
    refine ⟨42686016299790029957824883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28457344199860019971883255 42686016299790029957824883)
    ·
      refine ⟨64029024449685044936737325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42686016299790029957824883 64029024449685044936737325)
      ·
        refine ⟨24010884168631891851276497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64029024449685044936737325 24010884168631891851276497)
        ·
          refine ⟨18008163126473918888457373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24010884168631891851276497 18008163126473918888457373)
          ·
            refine ⟨6753061172427719583171515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18008163126473918888457373 6753061172427719583171515)
            ·
              refine ⟨10129591758641579374757273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6753061172427719583171515 10129591758641579374757273)
              ·
                refine ⟨7597193818981184531067955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10129591758641579374757273 7597193818981184531067955)
                ·
                  refine ⟨11395790728471776796601933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7597193818981184531067955 11395790728471776796601933)
                  ·
                    refine ⟨4273421523176916298725725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11395790728471776796601933 4273421523176916298725725)
                    ·
                      refine ⟨1602533071191343612022147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4273421523176916298725725 1602533071191343612022147)
                      ·
                        rfl

theorem cell23_3120922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_3120922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120922 prefixEnd_3120922 := by exact prefixLift 3120922
  have htrace : WordTrace (prefixWord ++ tailWord_3120922) baseStart_3120922 baseEnd_3120922 := by
    simpa [prefixWord, tailWord_3120922, baseEnd_3120922] using wordTrace_append hprefix tailTrace_3120922
  have hstable : (prefixWord ++ tailWord_3120922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120922).length < 2 ^ (prefixWord ++ tailWord_3120922).sum := by decide
  have hdescent : baseEnd_3120922 < baseStart_3120922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120945 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3120945 : Nat := 118140960795 + 3120945 * 2 ^ 59
def prefixEnd_3120945 : Nat := 4983230072969 + 3 ^ 40 * 3120945 * 2
def baseEnd_3120945 : Nat := 1602544881246397022034541

theorem tailTrace_3120945 : CollatzResearch.WordTrace tailWord_3120945 prefixEnd_3120945 1602544881246397022034541 := by
  unfold tailWord_3120945
  simp only [CollatzResearch.WordTrace]
  refine ⟨113830215678356754815620289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75886810452237836543746859 113830215678356754815620289)
  ·
    refine ⟨85372661758767566111715217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113830215678356754815620289 85372661758767566111715217)
    ·
      refine ⟨64029496319075674583786413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85372661758767566111715217 64029496319075674583786413)
      ·
        refine ⟨24011061119653377968919905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64029496319075674583786413 24011061119653377968919905)
        ·
          refine ⟨18008295839740033476689929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24011061119653377968919905 18008295839740033476689929)
          ·
            refine ⟨13506221879805025107517447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18008295839740033476689929 13506221879805025107517447)
            ·
              refine ⟨20259332819707537661276171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13506221879805025107517447 20259332819707537661276171)
              ·
                refine ⟨30388999229561306491914257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20259332819707537661276171 30388999229561306491914257)
                ·
                  refine ⟨22791749422170979868935693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30388999229561306491914257 22791749422170979868935693)
                  ·
                    refine ⟨8546906033314117450850885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22791749422170979868935693 8546906033314117450850885)
                    ·
                      refine ⟨1602544881246397022034541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8546906033314117450850885 1602544881246397022034541)
                      ·
                        rfl

theorem cell23_3120945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3120945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120945 prefixEnd_3120945 := by exact prefixLift 3120945
  have htrace : WordTrace (prefixWord ++ tailWord_3120945) baseStart_3120945 baseEnd_3120945 := by
    simpa [prefixWord, tailWord_3120945, baseEnd_3120945] using wordTrace_append hprefix tailTrace_3120945
  have hstable : (prefixWord ++ tailWord_3120945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120945).length < 2 ^ (prefixWord ++ tailWord_3120945).sum := by decide
  have hdescent : baseEnd_3120945 < baseStart_3120945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120965 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 2, 4, 3]
def baseStart_3120965 : Nat := 118140960795 + 3120965 * 2 ^ 59
def prefixEnd_3120965 : Nat := 4983230072969 + 3 ^ 40 * 3120965 * 2
def baseEnd_3120965 : Nat := 1602555150859486943784449

theorem tailTrace_3120965 : CollatzResearch.WordTrace tailWord_3120965 prefixEnd_3120965 1602555150859486943784449 := by
  unfold tailWord_3120965
  simp only [CollatzResearch.WordTrace]
  refine ⟨113830945138284298231348349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75887296758856198820898899 113830945138284298231348349)
  ·
    refine ⟨42686604426856611836755631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113830945138284298231348349 42686604426856611836755631)
    ·
      refine ⟨64029906640284917755133447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42686604426856611836755631 64029906640284917755133447)
      ·
        refine ⟨96044859960427376632700171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64029906640284917755133447 96044859960427376632700171)
        ·
          refine ⟨144067289940641064949050257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96044859960427376632700171 144067289940641064949050257)
          ·
            refine ⟨108050467455480798711787693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144067289940641064949050257 108050467455480798711787693)
            ·
              refine ⟨40518925295805299516920385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108050467455480798711787693 40518925295805299516920385)
              ·
                refine ⟨30389193971853974637690289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40518925295805299516920385 30389193971853974637690289)
                ·
                  refine ⟨22791895478890480978267717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30389193971853974637690289 22791895478890480978267717)
                  ·
                    refine ⟨4273480402291965183425197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22791895478890480978267717 4273480402291965183425197)
                    ·
                      refine ⟨1602555150859486943784449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4273480402291965183425197 1602555150859486943784449)
                      ·
                        rfl

theorem cell23_3120965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_3120965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120965 prefixEnd_3120965 := by exact prefixLift 3120965
  have htrace : WordTrace (prefixWord ++ tailWord_3120965) baseStart_3120965 baseEnd_3120965 := by
    simpa [prefixWord, tailWord_3120965, baseEnd_3120965] using wordTrace_append hprefix tailTrace_3120965
  have hstable : (prefixWord ++ tailWord_3120965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120965).length < 2 ^ (prefixWord ++ tailWord_3120965).sum := by decide
  have hdescent : baseEnd_3120965 < baseStart_3120965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120983 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 1, 3, 2]
def baseStart_3120983 : Nat := 118140960795 + 3120983 * 2 ^ 59
def prefixEnd_3120983 : Nat := 4983230072969 + 3 ^ 40 * 3120983 * 2
def baseEnd_3120983 : Nat := 1602564393511267873359367

theorem tailTrace_3120983 : CollatzResearch.WordTrace tailWord_3120983 prefixEnd_3120983 1602564393511267873359367 := by
  unfold tailWord_3120983
  simp only [CollatzResearch.WordTrace]
  refine ⟨113831601652219087305503603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75887734434812724870335735 113831601652219087305503603)
  ·
    refine ⟨170747402478328630958255405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113831601652219087305503603 170747402478328630958255405)
    ·
      refine ⟨64030275929373236609345777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170747402478328630958255405 64030275929373236609345777)
      ·
        refine ⟨48022706947029927457009333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64030275929373236609345777 48022706947029927457009333)
        ·
          refine ⟨4502128776284055699094625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48022706947029927457009333 4502128776284055699094625)
          ·
            refine ⟨3376596582213041774320969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4502128776284055699094625 3376596582213041774320969)
            ·
              refine ⟨2532447436659781330740727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376596582213041774320969 2532447436659781330740727)
              ·
                refine ⟨3798671154989671996111091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532447436659781330740727 3798671154989671996111091)
                ·
                  refine ⟨5698006732484507994166637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798671154989671996111091 5698006732484507994166637)
                  ·
                    refine ⟨2136752524681690497812489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5698006732484507994166637 2136752524681690497812489)
                    ·
                      refine ⟨1602564393511267873359367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136752524681690497812489 1602564393511267873359367)
                      ·
                        rfl

theorem cell23_3120983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_3120983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120983 prefixEnd_3120983 := by exact prefixLift 3120983
  have htrace : WordTrace (prefixWord ++ tailWord_3120983) baseStart_3120983 baseEnd_3120983 := by
    simpa [prefixWord, tailWord_3120983, baseEnd_3120983] using wordTrace_append hprefix tailTrace_3120983
  have hstable : (prefixWord ++ tailWord_3120983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120983).length < 2 ^ (prefixWord ++ tailWord_3120983).sum := by decide
  have hdescent : baseEnd_3120983 < baseStart_3120983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120996 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 4, 2, 2]
def baseStart_3120996 : Nat := 118140960795 + 3120996 * 2 ^ 59
def prefixEnd_3120996 : Nat := 4983230072969 + 3 ^ 40 * 3120996 * 2
def baseEnd_3120996 : Nat := 1602571068759776322496807

theorem tailTrace_3120996 : CollatzResearch.WordTrace tailWord_3120996 prefixEnd_3120996 1602571068759776322496807 := by
  unfold tailWord_3120996
  simp only [CollatzResearch.WordTrace]
  refine ⟨56916037900585995262863421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75888050534114660350484561 56916037900585995262863421)
  ·
    refine ⟨21343514212719748223573783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56916037900585995262863421 21343514212719748223573783)
    ·
      refine ⟨32015271319079622335360675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21343514212719748223573783 32015271319079622335360675)
      ·
        refine ⟨48022906978619433503041013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32015271319079622335360675 48022906978619433503041013)
        ·
          refine ⟨4502147529245571890910095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48022906978619433503041013 4502147529245571890910095)
          ·
            refine ⟨6753221293868357836365143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4502147529245571890910095 6753221293868357836365143)
            ·
              refine ⟨10129831940802536754547715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6753221293868357836365143 10129831940802536754547715)
              ·
                refine ⟨15194747911203805131821573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129831940802536754547715 15194747911203805131821573)
                ·
                  refine ⟨2849015233350713462216545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15194747911203805131821573 2849015233350713462216545)
                  ·
                    refine ⟨2136761425013035096662409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2849015233350713462216545 2136761425013035096662409)
                    ·
                      refine ⟨1602571068759776322496807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136761425013035096662409 1602571068759776322496807)
                      ·
                        rfl

theorem cell23_3120996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_3120996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3120996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3120996 prefixEnd_3120996 := by exact prefixLift 3120996
  have htrace : WordTrace (prefixWord ++ tailWord_3120996) baseStart_3120996 baseEnd_3120996 := by
    simpa [prefixWord, tailWord_3120996, baseEnd_3120996] using wordTrace_append hprefix tailTrace_3120996
  have hstable : (prefixWord ++ tailWord_3120996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120996).length < 2 ^ (prefixWord ++ tailWord_3120996).sum := by decide
  have hdescent : baseEnd_3120996 < baseStart_3120996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121013 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_3121013 : Nat := 118140960795 + 3121013 * 2 ^ 59
def prefixEnd_3121013 : Nat := 4983230072969 + 3 ^ 40 * 3121013 * 2
def baseEnd_3121013 : Nat := 1602579797930902755984229

theorem tailTrace_3121013 : CollatzResearch.WordTrace tailWord_3121013 prefixEnd_3121013 1602579797930902755984229 := by
  unfold tailWord_3121013
  simp only [CollatzResearch.WordTrace]
  refine ⟨113832695842110402429095693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75888463894740268286063795 113832695842110402429095693)
  ·
    refine ⟨42687260940791400910910885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113832695842110402429095693 42687260940791400910910885)
    ·
      refine ⟨8003861426398387670795791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42687260940791400910910885 8003861426398387670795791)
      ·
        refine ⟨12005792139597581506193687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8003861426398387670795791 12005792139597581506193687)
        ·
          refine ⟨18008688209396372259290531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12005792139597581506193687 18008688209396372259290531)
          ·
            refine ⟨27013032314094558388935797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18008688209396372259290531 27013032314094558388935797)
            ·
              refine ⟨2532471779446364848962731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27013032314094558388935797 2532471779446364848962731)
              ·
                refine ⟨3798707669169547273444097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532471779446364848962731 3798707669169547273444097)
                ·
                  refine ⟨2849030751877160455083073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3798707669169547273444097 2849030751877160455083073)
                  ·
                    refine ⟨2136773063907870341312305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2849030751877160455083073 2136773063907870341312305)
                    ·
                      refine ⟨1602579797930902755984229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136773063907870341312305 1602579797930902755984229)
                      ·
                        rfl

theorem cell23_3121013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_3121013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121013 prefixEnd_3121013 := by exact prefixLift 3121013
  have htrace : WordTrace (prefixWord ++ tailWord_3121013) baseStart_3121013 baseEnd_3121013 := by
    simpa [prefixWord, tailWord_3121013, baseEnd_3121013] using wordTrace_append hprefix tailTrace_3121013
  have hstable : (prefixWord ++ tailWord_3121013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121013).length < 2 ^ (prefixWord ++ tailWord_3121013).sum := by decide
  have hdescent : baseEnd_3121013 < baseStart_3121013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121064 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3121064 : Nat := 118140960795 + 3121064 * 2 ^ 59
def prefixEnd_3121064 : Nat := 4983230072969 + 3 ^ 40 * 3121064 * 2
def baseEnd_3121064 : Nat := 1602605985444282056446495

theorem tailTrace_3121064 : CollatzResearch.WordTrace tailWord_3121064 prefixEnd_3121064 1602605985444282056446495 := by
  unfold tailWord_3121064
  simp only [CollatzResearch.WordTrace]
  refine ⟨56917277982462819069601123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75889703976617092092801497 56917277982462819069601123)
  ·
    refine ⟨85375916973694228604401685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56917277982462819069601123 85375916973694228604401685)
    ·
      refine ⟨4001996108141916965831329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85375916973694228604401685 4001996108141916965831329)
      ·
        refine ⟨3001497081106437724373497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4001996108141916965831329 3001497081106437724373497)
        ·
          refine ⟨2251122810829828293280123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3001497081106437724373497 2251122810829828293280123)
          ·
            refine ⟨3376684216244742439920185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251122810829828293280123 3376684216244742439920185)
            ·
              refine ⟨2532513162183556829940139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376684216244742439920185 2532513162183556829940139)
              ·
                refine ⟨3798769743275335244910209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532513162183556829940139 3798769743275335244910209)
                ·
                  refine ⟨2849077307456501433682657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3798769743275335244910209 2849077307456501433682657)
                  ·
                    refine ⟨2136807980592376075261993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2849077307456501433682657 2136807980592376075261993)
                    ·
                      refine ⟨1602605985444282056446495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136807980592376075261993 1602605985444282056446495)
                      ·
                        rfl

theorem cell23_3121064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3121064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121064 prefixEnd_3121064 := by exact prefixLift 3121064
  have htrace : WordTrace (prefixWord ++ tailWord_3121064) baseStart_3121064 baseEnd_3121064 := by
    simpa [prefixWord, tailWord_3121064, baseEnd_3121064] using wordTrace_append hprefix tailTrace_3121064
  have hstable : (prefixWord ++ tailWord_3121064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121064).length < 2 ^ (prefixWord ++ tailWord_3121064).sum := by decide
  have hdescent : baseEnd_3121064 < baseStart_3121064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121065 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_3121065 : Nat := 118140960795 + 3121065 * 2 ^ 59
def prefixEnd_3121065 : Nat := 4983230072969 + 3 ^ 40 * 3121065 * 2
def baseEnd_3121065 : Nat := 1602606498924936552533989

theorem tailTrace_3121065 : CollatzResearch.WordTrace tailWord_3121065 prefixEnd_3121065 1602606498924936552533989 := by
  unfold tailWord_3121065
  simp only [CollatzResearch.WordTrace]
  refine ⟨113834592437922015309988649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75889728291948010206659099 113834592437922015309988649)
  ·
    refine ⟨85375944328441511482491487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113834592437922015309988649 85375944328441511482491487)
    ·
      refine ⟨128063916492662267223737231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85375944328441511482491487 128063916492662267223737231)
      ·
        refine ⟨192095874738993400835605847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128063916492662267223737231 192095874738993400835605847)
        ·
          refine ⟨288143812108490101253408771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192095874738993400835605847 288143812108490101253408771)
          ·
            refine ⟨432215718162735151880113157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288143812108490101253408771 432215718162735151880113157)
            ·
              refine ⟨81040447155512840977521217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 432215718162735151880113157 81040447155512840977521217)
              ·
                refine ⟨60780335366634630733140913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81040447155512840977521217 60780335366634630733140913)
                ·
                  refine ⟨45585251524975973049855685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60780335366634630733140913 45585251524975973049855685)
                  ·
                    refine ⟨8547234660932994946847941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45585251524975973049855685 8547234660932994946847941)
                    ·
                      refine ⟨1602606498924936552533989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8547234660932994946847941 1602606498924936552533989)
                      ·
                        rfl

theorem cell23_3121065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_3121065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121065 prefixEnd_3121065 := by exact prefixLift 3121065
  have htrace : WordTrace (prefixWord ++ tailWord_3121065) baseStart_3121065 baseEnd_3121065 := by
    simpa [prefixWord, tailWord_3121065, baseEnd_3121065] using wordTrace_append hprefix tailTrace_3121065
  have hstable : (prefixWord ++ tailWord_3121065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121065).length < 2 ^ (prefixWord ++ tailWord_3121065).sum := by decide
  have hdescent : baseEnd_3121065 < baseStart_3121065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121095 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_3121095 : Nat := 118140960795 + 3121095 * 2 ^ 59
def prefixEnd_3121095 : Nat := 4983230072969 + 3 ^ 40 * 3121095 * 2
def baseEnd_3121095 : Nat := 1602621903344571435158851

theorem tailTrace_3121095 : CollatzResearch.WordTrace tailWord_3121095 prefixEnd_3121095 1602621903344571435158851 := by
  unfold tailWord_3121095
  simp only [CollatzResearch.WordTrace]
  refine ⟨113835686627813330433580739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75890457751875553622387159 113835686627813330433580739)
  ·
    refine ⟨170753529941719995650371109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113835686627813330433580739 170753529941719995650371109)
    ·
      refine ⟨32016286864072499184444583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170753529941719995650371109 32016286864072499184444583)
      ·
        refine ⟨48024430296108748776666875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32016286864072499184444583 48024430296108748776666875)
        ·
          refine ⟨72036645444163123165000313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48024430296108748776666875 72036645444163123165000313)
          ·
            refine ⟨54027484083122342373750235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72036645444163123165000313 54027484083122342373750235)
            ·
              refine ⟨81041226124683513560625353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54027484083122342373750235 81041226124683513560625353)
              ·
                refine ⟨60780919593512635170469015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81041226124683513560625353 60780919593512635170469015)
                ·
                  refine ⟨91171379390268952755703523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60780919593512635170469015 91171379390268952755703523)
                  ·
                    refine ⟨136757069085403429133555285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91171379390268952755703523 136757069085403429133555285)
                    ·
                      refine ⟨1602621903344571435158851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 136757069085403429133555285 1602621903344571435158851)
                      ·
                        rfl

theorem cell23_3121095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_3121095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121095 prefixEnd_3121095 := by exact prefixLift 3121095
  have htrace : WordTrace (prefixWord ++ tailWord_3121095) baseStart_3121095 baseEnd_3121095 := by
    simpa [prefixWord, tailWord_3121095, baseEnd_3121095] using wordTrace_append hprefix tailTrace_3121095
  have hstable : (prefixWord ++ tailWord_3121095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121095).length < 2 ^ (prefixWord ++ tailWord_3121095).sum := by decide
  have hdescent : baseEnd_3121095 < baseStart_3121095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121109 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 6]
def baseStart_3121109 : Nat := 118140960795 + 3121109 * 2 ^ 59
def prefixEnd_3121109 : Nat := 4983230072969 + 3 ^ 40 * 3121109 * 2
def baseEnd_3121109 : Nat := 178069899119303820042643

theorem tailTrace_3121109 : CollatzResearch.WordTrace tailWord_3121109 prefixEnd_3121109 178069899119303820042643 := by
  unfold tailWord_3121109
  simp only [CollatzResearch.WordTrace]
  refine ⟨113836197249762610824590381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75890798166508407216393587 113836197249762610824590381)
  ·
    refine ⟨42688573968660979059221393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113836197249762610824590381 42688573968660979059221393)
    ·
      refine ⟨32016430476495734294416045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42688573968660979059221393 32016430476495734294416045)
      ·
        refine ⟨12006161428685900360406017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32016430476495734294416045 12006161428685900360406017)
        ·
          refine ⟨9004621071514425270304513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12006161428685900360406017 9004621071514425270304513)
          ·
            refine ⟨6753465803635818952728385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9004621071514425270304513 6753465803635818952728385)
            ·
              refine ⟨5065099352726864214546289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6753465803635818952728385 5065099352726864214546289)
              ·
                refine ⟨3798824514545148160909717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5065099352726864214546289 3798824514545148160909717)
                ·
                  refine ⟨178069899119303820042643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3798824514545148160909717 178069899119303820042643)
                  ·
                    rfl

theorem cell23_3121109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_3121109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121109 prefixEnd_3121109 := by exact prefixLift 3121109
  have htrace : WordTrace (prefixWord ++ tailWord_3121109) baseStart_3121109 baseEnd_3121109 := by
    simpa [prefixWord, tailWord_3121109, baseEnd_3121109] using wordTrace_append hprefix tailTrace_3121109
  have hstable : (prefixWord ++ tailWord_3121109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121109).length < 2 ^ (prefixWord ++ tailWord_3121109).sum := by decide
  have hdescent : baseEnd_3121109 < baseStart_3121109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121153 : List Nat := [1, 2, 4, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_3121153 : Nat := 118140960795 + 3121153 * 2 ^ 59
def prefixEnd_3121153 : Nat := 4983230072969 + 3 ^ 40 * 3121153 * 2
def baseEnd_3121153 : Nat := 1602651685222532208233585

theorem tailTrace_3121153 : CollatzResearch.WordTrace tailWord_3121153 prefixEnd_3121153 1602651685222532208233585 := by
  unfold tailWord_3121153
  simp only [CollatzResearch.WordTrace]
  refine ⟨113837802061603206339192113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75891868041068804226128075 113837802061603206339192113)
  ·
    refine ⟨85378351546202404754394085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113837802061603206339192113 85378351546202404754394085)
    ·
      refine ⟨16008440914912950891448891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85378351546202404754394085 16008440914912950891448891)
      ·
        refine ⟨24012661372369426337173337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16008440914912950891448891 24012661372369426337173337)
        ·
          refine ⟨18009496029277069752880003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24012661372369426337173337 18009496029277069752880003)
          ·
            refine ⟨27014244043915604629320005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18009496029277069752880003 27014244043915604629320005)
            ·
              refine ⟨5065170758234175867997501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27014244043915604629320005 5065170758234175867997501)
              ·
                refine ⟨1899439034337815950499063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5065170758234175867997501 1899439034337815950499063)
                ·
                  refine ⟨2849158551506723925748595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899439034337815950499063 2849158551506723925748595)
                  ·
                    refine ⟨4273737827260085888622893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2849158551506723925748595 4273737827260085888622893)
                    ·
                      refine ⟨1602651685222532208233585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4273737827260085888622893 1602651685222532208233585)
                      ·
                        rfl

theorem cell23_3121153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_3121153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121153 prefixEnd_3121153 := by exact prefixLift 3121153
  have htrace : WordTrace (prefixWord ++ tailWord_3121153) baseStart_3121153 baseEnd_3121153 := by
    simpa [prefixWord, tailWord_3121153, baseEnd_3121153] using wordTrace_append hprefix tailTrace_3121153
  have hstable : (prefixWord ++ tailWord_3121153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121153).length < 2 ^ (prefixWord ++ tailWord_3121153).sum := by decide
  have hdescent : baseEnd_3121153 < baseStart_3121153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121189 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 4]
def baseStart_3121189 : Nat := 118140960795 + 3121189 * 2 ^ 59
def prefixEnd_3121189 : Nat := 4983230072969 + 3 ^ 40 * 3121189 * 2
def baseEnd_3121189 : Nat := 1602670170526094067383419

theorem tailTrace_3121189 : CollatzResearch.WordTrace tailWord_3121189 prefixEnd_3121189 1602670170526094067383419 := by
  unfold tailWord_3121189
  simp only [CollatzResearch.WordTrace]
  refine ⟨113839115089472784487502621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75892743392981856325001747 113839115089472784487502621)
  ·
    refine ⟨42689668158552294182813483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113839115089472784487502621 42689668158552294182813483)
    ·
      refine ⟨64034502237828441274220225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42689668158552294182813483 64034502237828441274220225)
      ·
        refine ⟨48025876678371330955665169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64034502237828441274220225 48025876678371330955665169)
        ·
          refine ⟨36019407508778498216748877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48025876678371330955665169 36019407508778498216748877)
          ·
            refine ⟨13507277815791936831280829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36019407508778498216748877 13507277815791936831280829)
            ·
              refine ⟨5065229180921976311730311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13507277815791936831280829 5065229180921976311730311)
              ·
                refine ⟨7597843771382964467595467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5065229180921976311730311 7597843771382964467595467)
                ·
                  refine ⟨11396765657074446701393201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7597843771382964467595467 11396765657074446701393201)
                  ·
                    refine ⟨8547574242805835026044901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11396765657074446701393201 8547574242805835026044901)
                    ·
                      refine ⟨1602670170526094067383419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8547574242805835026044901 1602670170526094067383419)
                      ·
                        rfl

theorem cell23_3121189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_3121189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121189 prefixEnd_3121189 := by exact prefixLift 3121189
  have htrace : WordTrace (prefixWord ++ tailWord_3121189) baseStart_3121189 baseEnd_3121189 := by
    simpa [prefixWord, tailWord_3121189, baseEnd_3121189] using wordTrace_append hprefix tailTrace_3121189
  have hstable : (prefixWord ++ tailWord_3121189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121189).length < 2 ^ (prefixWord ++ tailWord_3121189).sum := by decide
  have hdescent : baseEnd_3121189 < baseStart_3121189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121204 : List Nat := [2, 5, 1, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_3121204 : Nat := 118140960795 + 3121204 * 2 ^ 59
def prefixEnd_3121204 : Nat := 4983230072969 + 3 ^ 40 * 3121204 * 2
def baseEnd_3121204 : Nat := 1602677872735911508695851

theorem tailTrace_3121204 : CollatzResearch.WordTrace tailWord_3121204 prefixEnd_3121204 1602677872735911508695851 := by
  unfold tailWord_3121204
  simp only [CollatzResearch.WordTrace]
  refine ⟨56919831092209221024649333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75893108122945628032865777 56919831092209221024649333)
  ·
    refine ⟨5336234164894614471060875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56919831092209221024649333 5336234164894614471060875)
    ·
      refine ⟨8004351247341921706591313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5336234164894614471060875 8004351247341921706591313)
      ·
        refine ⟨6003263435506441279943485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8004351247341921706591313 6003263435506441279943485)
        ·
          refine ⟨2251223788314915479978807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6003263435506441279943485 2251223788314915479978807)
          ·
            refine ⟨3376835682472373219968211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251223788314915479978807 3376835682472373219968211)
            ·
              refine ⟨5065253523708559829952317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376835682472373219968211 5065253523708559829952317)
              ·
                refine ⟨1899470071390709936232119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5065253523708559829952317 1899470071390709936232119)
                ·
                  refine ⟨2849205107086064904348179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899470071390709936232119 2849205107086064904348179)
                  ·
                    refine ⟨4273807660629097356522269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2849205107086064904348179 4273807660629097356522269)
                    ·
                      refine ⟨1602677872735911508695851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4273807660629097356522269 1602677872735911508695851)
                      ·
                        rfl

theorem cell23_3121204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_3121204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121204 prefixEnd_3121204 := by exact prefixLift 3121204
  have htrace : WordTrace (prefixWord ++ tailWord_3121204) baseStart_3121204 baseEnd_3121204 := by
    simpa [prefixWord, tailWord_3121204, baseEnd_3121204] using wordTrace_append hprefix tailTrace_3121204
  have hstable : (prefixWord ++ tailWord_3121204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121204).length < 2 ^ (prefixWord ++ tailWord_3121204).sum := by decide
  have hdescent : baseEnd_3121204 < baseStart_3121204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121226 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_3121226 : Nat := 118140960795 + 3121226 * 2 ^ 59
def prefixEnd_3121226 : Nat := 4983230072969 + 3 ^ 40 * 3121226 * 2
def baseEnd_3121226 : Nat := 1602689169310310422620749

theorem tailTrace_3121226 : CollatzResearch.WordTrace tailWord_3121226 prefixEnd_3121226 1602689169310310422620749 := by
  unfold tailWord_3121226
  simp only [CollatzResearch.WordTrace]
  refine ⟨28460116147584684951649883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75893643060225826537733021 28460116147584684951649883)
  ·
    refine ⟨42690174221377027427474825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28460116147584684951649883 42690174221377027427474825)
    ·
      refine ⟨32017630666032770570606119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42690174221377027427474825 32017630666032770570606119)
      ·
        refine ⟨48026445999049155855909179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32017630666032770570606119 48026445999049155855909179)
        ·
          refine ⟨72039668998573733783863769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48026445999049155855909179 72039668998573733783863769)
          ·
            refine ⟨54029751748930300337897827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72039668998573733783863769 54029751748930300337897827)
            ·
              refine ⟨81044627623395450506846741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54029751748930300337897827 81044627623395450506846741)
              ·
                refine ⟨3798966919846661742508441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81044627623395450506846741 3798966919846661742508441)
                ·
                  refine ⟨2849225189884996306881331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3798966919846661742508441 2849225189884996306881331)
                  ·
                    refine ⟨4273837784827494460321997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2849225189884996306881331 4273837784827494460321997)
                    ·
                      refine ⟨1602689169310310422620749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4273837784827494460321997 1602689169310310422620749)
                      ·
                        rfl

theorem cell23_3121226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_3121226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121226 prefixEnd_3121226 := by exact prefixLift 3121226
  have htrace : WordTrace (prefixWord ++ tailWord_3121226) baseStart_3121226 baseEnd_3121226 := by
    simpa [prefixWord, tailWord_3121226, baseEnd_3121226] using wordTrace_append hprefix tailTrace_3121226
  have hstable : (prefixWord ++ tailWord_3121226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121226).length < 2 ^ (prefixWord ++ tailWord_3121226).sum := by decide
  have hdescent : baseEnd_3121226 < baseStart_3121226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121229 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_3121229 : Nat := 118140960795 + 3121229 * 2 ^ 59
def prefixEnd_3121229 : Nat := 4983230072969 + 3 ^ 40 * 3121229 * 2
def baseEnd_3121229 : Nat := 534230236584091303627745

theorem tailTrace_3121229 : CollatzResearch.WordTrace tailWord_3121229 prefixEnd_3121229 534230236584091303627745 := by
  unfold tailWord_3121229
  simp only [CollatzResearch.WordTrace]
  refine ⟨113840574009327871318958741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75893716006218580879305827 113840574009327871318958741)
  ·
    refine ⟨5336276906687243968076191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113840574009327871318958741 5336276906687243968076191)
    ·
      refine ⟨8004415360030865952114287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5336276906687243968076191 8004415360030865952114287)
      ·
        refine ⟨12006623040046298928171431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8004415360030865952114287 12006623040046298928171431)
        ·
          refine ⟨18009934560069448392257147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12006623040046298928171431 18009934560069448392257147)
          ·
            refine ⟨27014901840104172588385721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18009934560069448392257147 27014901840104172588385721)
            ·
              refine ⟨20261176380078129441289291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27014901840104172588385721 20261176380078129441289291)
              ·
                refine ⟨30391764570117194161933937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20261176380078129441289291 30391764570117194161933937)
                ·
                  refine ⟨22793823427587895621450453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30391764570117194161933937 22793823427587895621450453)
                  ·
                    refine ⟨534230236584091303627745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22793823427587895621450453 534230236584091303627745)
                    ·
                      rfl

theorem cell23_3121229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_3121229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121229 prefixEnd_3121229 := by exact prefixLift 3121229
  have htrace : WordTrace (prefixWord ++ tailWord_3121229) baseStart_3121229 baseEnd_3121229 := by
    simpa [prefixWord, tailWord_3121229, baseEnd_3121229] using wordTrace_append hprefix tailTrace_3121229
  have hstable : (prefixWord ++ tailWord_3121229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121229).length < 2 ^ (prefixWord ++ tailWord_3121229).sum := by decide
  have hdescent : baseEnd_3121229 < baseStart_3121229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121236 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_3121236 : Nat := 118140960795 + 3121236 * 2 ^ 59
def prefixEnd_3121236 : Nat := 4983230072969 + 3 ^ 40 * 3121236 * 2
def baseEnd_3121236 : Nat := 1602694304116855383495703

theorem tailTrace_3121236 : CollatzResearch.WordTrace tailWord_3121236 prefixEnd_3121236 1602694304116855383495703 := by
  unfold tailWord_3121236
  simp only [CollatzResearch.WordTrace]
  refine ⟨56920414660151255757231781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75893886213535007676309041 56920414660151255757231781)
  ·
    refine ⟨10672577748778360454480959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56920414660151255757231781 10672577748778360454480959)
    ·
      refine ⟨16008866623167540681721439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10672577748778360454480959 16008866623167540681721439)
      ·
        refine ⟨24013299934751311022582159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16008866623167540681721439 24013299934751311022582159)
        ·
          refine ⟨36019949902126966533873239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24013299934751311022582159 36019949902126966533873239)
          ·
            refine ⟨54029924853190449800809859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36019949902126966533873239 54029924853190449800809859)
            ·
              refine ⟨81044887279785674701214789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54029924853190449800809859 81044887279785674701214789)
              ·
                refine ⟨15195916364959814006477773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81044887279785674701214789 15195916364959814006477773)
                ·
                  refine ⟨5698468636859930252429165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15195916364959814006477773 5698468636859930252429165)
                  ·
                    refine ⟨2136925738822473844660937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5698468636859930252429165 2136925738822473844660937)
                    ·
                      refine ⟨1602694304116855383495703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136925738822473844660937 1602694304116855383495703)
                      ·
                        rfl

theorem cell23_3121236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_3121236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121236 prefixEnd_3121236 := by exact prefixLift 3121236
  have htrace : WordTrace (prefixWord ++ tailWord_3121236) baseStart_3121236 baseEnd_3121236 := by
    simpa [prefixWord, tailWord_3121236, baseEnd_3121236] using wordTrace_append hprefix tailTrace_3121236
  have hstable : (prefixWord ++ tailWord_3121236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121236).length < 2 ^ (prefixWord ++ tailWord_3121236).sum := by decide
  have hdescent : baseEnd_3121236 < baseStart_3121236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121242 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_3121242 : Nat := 118140960795 + 3121242 * 2 ^ 59
def prefixEnd_3121242 : Nat := 4983230072969 + 3 ^ 40 * 3121242 * 2
def baseEnd_3121242 : Nat := 534232461666927453340225

theorem tailTrace_3121242 : CollatzResearch.WordTrace tailWord_3121242 prefixEnd_3121242 534232461666927453340225 := by
  unfold tailWord_3121242
  simp only [CollatzResearch.WordTrace]
  refine ⟨28460262039570193634795495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75894032105520516359454653 28460262039570193634795495)
  ·
    refine ⟨42690393059355290452193243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28460262039570193634795495 42690393059355290452193243)
    ·
      refine ⟨64035589589032935678289865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42690393059355290452193243 64035589589032935678289865)
      ·
        refine ⟨48026692191774701758717399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64035589589032935678289865 48026692191774701758717399)
        ·
          refine ⟨72040038287662052638076099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48026692191774701758717399 72040038287662052638076099)
          ·
            refine ⟨108060057431493078957114149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72040038287662052638076099 108060057431493078957114149)
            ·
              refine ⟨20261260768404952304458903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108060057431493078957114149 20261260768404952304458903)
              ·
                refine ⟨30391891152607428456688355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20261260768404952304458903 30391891152607428456688355)
                ·
                  refine ⟨45587836728911142685032533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30391891152607428456688355 45587836728911142685032533)
                  ·
                    refine ⟨534232461666927453340225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45587836728911142685032533 534232461666927453340225)
                    ·
                      rfl

theorem cell23_3121242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_3121242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121242 prefixEnd_3121242 := by exact prefixLift 3121242
  have htrace : WordTrace (prefixWord ++ tailWord_3121242) baseStart_3121242 baseEnd_3121242 := by
    simpa [prefixWord, tailWord_3121242, baseEnd_3121242] using wordTrace_append hprefix tailTrace_3121242
  have hstable : (prefixWord ++ tailWord_3121242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121242).length < 2 ^ (prefixWord ++ tailWord_3121242).sum := by decide
  have hdescent : baseEnd_3121242 < baseStart_3121242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121253 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 1, 3, 2]
def baseStart_3121253 : Nat := 118140960795 + 3121253 * 2 ^ 59
def prefixEnd_3121253 : Nat := 4983230072969 + 3 ^ 40 * 3121253 * 2
def baseEnd_3121253 : Nat := 1602703033287981816983125

theorem tailTrace_3121253 : CollatzResearch.WordTrace tailWord_3121253 prefixEnd_3121253 1602703033287981816983125 := by
  unfold tailWord_3121253
  simp only [CollatzResearch.WordTrace]
  refine ⟨113841449361240923417832413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75894299574160615611888275 113841449361240923417832413)
  ·
    refine ⟨42690543510465346281687155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113841449361240923417832413 42690543510465346281687155)
    ·
      refine ⟨64035815265698019422530733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42690543510465346281687155 64035815265698019422530733)
      ·
        refine ⟨24013430724636757283449025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64035815265698019422530733 24013430724636757283449025)
        ·
          refine ⟨18010073043477567962586769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24013430724636757283449025 18010073043477567962586769)
          ·
            refine ⟨13507554782608175971940077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18010073043477567962586769 13507554782608175971940077)
            ·
              refine ⟨5065333043478065989477529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13507554782608175971940077 5065333043478065989477529)
              ·
                refine ⟨3798999782608549492108147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5065333043478065989477529 3798999782608549492108147)
                ·
                  refine ⟨5698499673912824238162221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798999782608549492108147 5698499673912824238162221)
                  ·
                    refine ⟨2136937377717309089310833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5698499673912824238162221 2136937377717309089310833)
                    ·
                      refine ⟨1602703033287981816983125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136937377717309089310833 1602703033287981816983125)
                      ·
                        rfl

theorem cell23_3121253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_3121253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121253 prefixEnd_3121253 := by exact prefixLift 3121253
  have htrace : WordTrace (prefixWord ++ tailWord_3121253) baseStart_3121253 baseEnd_3121253 := by
    simpa [prefixWord, tailWord_3121253, baseEnd_3121253] using wordTrace_append hprefix tailTrace_3121253
  have hstable : (prefixWord ++ tailWord_3121253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121253).length < 2 ^ (prefixWord ++ tailWord_3121253).sum := by decide
  have hdescent : baseEnd_3121253 < baseStart_3121253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121266 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 3, 4, 2]
def baseStart_3121266 : Nat := 118140960795 + 3121266 * 2 ^ 59
def prefixEnd_3121266 : Nat := 4983230072969 + 3 ^ 40 * 3121266 * 2
def baseEnd_3121266 : Nat := 1602709708536490266120565

theorem tailTrace_3121266 : CollatzResearch.WordTrace tailWord_3121266 prefixEnd_3121266 1602709708536490266120565 := by
  unfold tailWord_3121266
  simp only [CollatzResearch.WordTrace]
  refine ⟨28460480877548456659513913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75894615673462551092037101 28460480877548456659513913)
  ·
    refine ⟨21345360658161342494635435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28460480877548456659513913 21345360658161342494635435)
    ·
      refine ⟨32018040987242013741953153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21345360658161342494635435 32018040987242013741953153)
      ·
        refine ⟨24013530740431510306464865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32018040987242013741953153 24013530740431510306464865)
        ·
          refine ⟨18010148055323632729848649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24013530740431510306464865 18010148055323632729848649)
          ·
            refine ⟨13507611041492724547386487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18010148055323632729848649 13507611041492724547386487)
            ·
              refine ⟨20261416562239086821079731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13507611041492724547386487 20261416562239086821079731)
              ·
                refine ⟨30392124843358630231619597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20261416562239086821079731 30392124843358630231619597)
                ·
                  refine ⟨11397046816259486336857349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30392124843358630231619597 11397046816259486336857349)
                  ·
                    refine ⟨2136946278048653688160753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11397046816259486336857349 2136946278048653688160753)
                    ·
                      refine ⟨1602709708536490266120565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136946278048653688160753 1602709708536490266120565)
                      ·
                        rfl

theorem cell23_3121266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_3121266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121266 prefixEnd_3121266 := by exact prefixLift 3121266
  have htrace : WordTrace (prefixWord ++ tailWord_3121266) baseStart_3121266 baseEnd_3121266 := by
    simpa [prefixWord, tailWord_3121266, baseEnd_3121266] using wordTrace_append hprefix tailTrace_3121266
  have hstable : (prefixWord ++ tailWord_3121266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121266).length < 2 ^ (prefixWord ++ tailWord_3121266).sum := by decide
  have hdescent : baseEnd_3121266 < baseStart_3121266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121283 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 2, 2, 2]
def baseStart_3121283 : Nat := 118140960795 + 3121283 * 2 ^ 59
def prefixEnd_3121283 : Nat := 4983230072969 + 3 ^ 40 * 3121283 * 2
def baseEnd_3121283 : Nat := 1602718437707616699607987

theorem tailTrace_3121283 : CollatzResearch.WordTrace tailWord_3121283 prefixEnd_3121283 1602718437707616699607987 := by
  unfold tailWord_3121283
  simp only [CollatzResearch.WordTrace]
  refine ⟨113842543551132238541424503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75895029034088159027616335 113842543551132238541424503)
  ·
    refine ⟨170763815326698357812136755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113842543551132238541424503 170763815326698357812136755)
    ·
      refine ⟨256145722990047536718205133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170763815326698357812136755 256145722990047536718205133)
      ·
        refine ⟨96054646121267826269326925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256145722990047536718205133 96054646121267826269326925)
        ·
          refine ⟨36020492295475434850997597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96054646121267826269326925 36020492295475434850997597)
          ·
            refine ⟨13507684610803288069124099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36020492295475434850997597 13507684610803288069124099)
            ·
              refine ⟨20261526916204932103686149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13507684610803288069124099 20261526916204932103686149)
              ·
                refine ⟨3799036296788424769441153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20261526916204932103686149 3799036296788424769441153)
                ·
                  refine ⟨2849277222591318577080865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3799036296788424769441153 2849277222591318577080865)
                  ·
                    refine ⟨2136957916943488932810649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2849277222591318577080865 2136957916943488932810649)
                    ·
                      refine ⟨1602718437707616699607987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2136957916943488932810649 1602718437707616699607987)
                      ·
                        rfl

theorem cell23_3121283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_3121283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121283 prefixEnd_3121283 := by exact prefixLift 3121283
  have htrace : WordTrace (prefixWord ++ tailWord_3121283) baseStart_3121283 baseEnd_3121283 := by
    simpa [prefixWord, tailWord_3121283, baseEnd_3121283] using wordTrace_append hprefix tailTrace_3121283
  have hstable : (prefixWord ++ tailWord_3121283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121283).length < 2 ^ (prefixWord ++ tailWord_3121283).sum := by decide
  have hdescent : baseEnd_3121283 < baseStart_3121283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121292 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3121292 : Nat := 118140960795 + 3121292 * 2 ^ 59
def prefixEnd_3121292 : Nat := 4983230072969 + 3 ^ 40 * 3121292 * 2
def baseEnd_3121292 : Nat := 1602723059033507164395445

theorem tailTrace_3121292 : CollatzResearch.WordTrace tailWord_3121292 prefixEnd_3121292 1602723059033507164395445 := by
  unfold tailWord_3121292
  simp only [CollatzResearch.WordTrace]
  refine ⟨56921435904049816539251065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75895247872066422052334753 56921435904049816539251065)
  ·
    refine ⟨42691076928037362404438299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56921435904049816539251065 42691076928037362404438299)
    ·
      refine ⟨64036615392056043606657449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42691076928037362404438299 64036615392056043606657449)
      ·
        refine ⟨48027461544042032704993087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64036615392056043606657449 48027461544042032704993087)
        ·
          refine ⟨72041192316063049057489631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48027461544042032704993087 72041192316063049057489631)
          ·
            refine ⟨108061788474094573586234447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72041192316063049057489631 108061788474094573586234447)
            ·
              refine ⟨162092682711141860379351671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108061788474094573586234447 162092682711141860379351671)
              ·
                refine ⟨243139024066712790569027507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162092682711141860379351671 243139024066712790569027507)
                ·
                  refine ⟨364708536100069185853541261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243139024066712790569027507 364708536100069185853541261)
                  ·
                    refine ⟨136765701037525944695077973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 364708536100069185853541261 136765701037525944695077973)
                    ·
                      refine ⟨1602723059033507164395445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 136765701037525944695077973 1602723059033507164395445)
                      ·
                        rfl

theorem cell23_3121292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3121292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121292 prefixEnd_3121292 := by exact prefixLift 3121292
  have htrace : WordTrace (prefixWord ++ tailWord_3121292) baseStart_3121292 baseEnd_3121292 := by
    simpa [prefixWord, tailWord_3121292, baseEnd_3121292] using wordTrace_append hprefix tailTrace_3121292
  have hstable : (prefixWord ++ tailWord_3121292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121292).length < 2 ^ (prefixWord ++ tailWord_3121292).sum := by decide
  have hdescent : baseEnd_3121292 < baseStart_3121292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121306 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 7]
def baseStart_3121306 : Nat := 118140960795 + 3121306 * 2 ^ 59
def prefixEnd_3121306 : Nat := 4983230072969 + 3 ^ 40 * 3121306 * 2
def baseEnd_3121306 : Nat := 178081138640296678846709

theorem tailTrace_3121306 : CollatzResearch.WordTrace tailWord_3121306 prefixEnd_3121306 178081138640296678846709 := by
  unfold tailWord_3121306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28460845607512228367377943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75895588286699275646341181 28460845607512228367377943)
  ·
    refine ⟨42691268411268342551066915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28460845607512228367377943 42691268411268342551066915)
    ·
      refine ⟨64036902616902513826600373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42691268411268342551066915 64036902616902513826600373)
      ·
        refine ⟨6003459620334610671243785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64036902616902513826600373 6003459620334610671243785)
        ·
          refine ⟨4502594715250958003432839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6003459620334610671243785 4502594715250958003432839)
          ·
            refine ⟨6753892072876437005149259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4502594715250958003432839 6753892072876437005149259)
            ·
              refine ⟨10130838109314655507723889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6753892072876437005149259 10130838109314655507723889)
              ·
                refine ⟨7598128581985991630792917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10130838109314655507723889 7598128581985991630792917)
                ·
                  refine ⟨178081138640296678846709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7598128581985991630792917 178081138640296678846709)
                  ·
                    rfl

theorem cell23_3121306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_3121306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121306 prefixEnd_3121306 := by exact prefixLift 3121306
  have htrace : WordTrace (prefixWord ++ tailWord_3121306) baseStart_3121306 baseEnd_3121306 := by
    simpa [prefixWord, tailWord_3121306, baseEnd_3121306] using wordTrace_append hprefix tailTrace_3121306
  have hstable : (prefixWord ++ tailWord_3121306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121306).length < 2 ^ (prefixWord ++ tailWord_3121306).sum := by decide
  have hdescent : baseEnd_3121306 < baseStart_3121306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121339 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 4]
def baseStart_3121339 : Nat := 118140960795 + 3121339 * 2 ^ 59
def prefixEnd_3121339 : Nat := 4983230072969 + 3 ^ 40 * 3121339 * 2
def baseEnd_3121339 : Nat := 1602747192624268480507729

theorem tailTrace_3121339 : CollatzResearch.WordTrace tailWord_3121339 prefixEnd_3121339 1602747192624268480507729 := by
  unfold tailWord_3121339
  simp only [CollatzResearch.WordTrace]
  refine ⟨113844586038929360105463071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75896390692619573403642047 113844586038929360105463071)
  ·
    refine ⟨170766879058394040158194607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113844586038929360105463071 170766879058394040158194607)
    ·
      refine ⟨256150318587591060237291911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170766879058394040158194607 256150318587591060237291911)
      ·
        refine ⟨384225477881386590355937867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256150318587591060237291911 384225477881386590355937867)
        ·
          refine ⟨576338216822079885533906801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384225477881386590355937867 576338216822079885533906801)
          ·
            refine ⟨432253662616559914150430101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576338216822079885533906801 432253662616559914150430101)
            ·
              refine ⟨20261890435151245975801411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 432253662616559914150430101 20261890435151245975801411)
              ·
                refine ⟨30392835652726868963702117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20261890435151245975801411 30392835652726868963702117)
                ·
                  refine ⟨5698656684886287930694147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30392835652726868963702117 5698656684886287930694147)
                  ·
                    refine ⟨8547985027329431896041221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5698656684886287930694147 8547985027329431896041221)
                    ·
                      refine ⟨1602747192624268480507729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8547985027329431896041221 1602747192624268480507729)
                      ·
                        rfl

theorem cell23_3121339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 4].length) (baseStart_3121339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121339 prefixEnd_3121339 := by exact prefixLift 3121339
  have htrace : WordTrace (prefixWord ++ tailWord_3121339) baseStart_3121339 baseEnd_3121339 := by
    simpa [prefixWord, tailWord_3121339, baseEnd_3121339] using wordTrace_append hprefix tailTrace_3121339
  have hstable : (prefixWord ++ tailWord_3121339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121339).length < 2 ^ (prefixWord ++ tailWord_3121339).sum := by decide
  have hdescent : baseEnd_3121339 < baseStart_3121339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121359 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 3]
def baseStart_3121359 : Nat := 118140960795 + 3121359 * 2 ^ 59
def prefixEnd_3121359 : Nat := 4983230072969 + 3 ^ 40 * 3121359 * 2
def baseEnd_3121359 : Nat := 1602757462237358402257637

theorem tailTrace_3121359 : CollatzResearch.WordTrace tailWord_3121359 prefixEnd_3121359 1602757462237358402257637 := by
  unfold tailWord_3121359
  simp only [CollatzResearch.WordTrace]
  refine ⟨113845315498856903521191131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75896876999237935680794087 113845315498856903521191131)
  ·
    refine ⟨170767973248285355281786697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113845315498856903521191131 170767973248285355281786697)
    ·
      refine ⟨128075979936214016461340023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170767973248285355281786697 128075979936214016461340023)
      ·
        refine ⟨192113969904321024692010035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128075979936214016461340023 192113969904321024692010035)
        ·
          refine ⟨288170954856481537038015053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192113969904321024692010035 288170954856481537038015053)
          ·
            refine ⟨108064108071180576389255645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288170954856481537038015053 108064108071180576389255645)
            ·
              refine ⟨40524040526692716145970867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108064108071180576389255645 40524040526692716145970867)
              ·
                refine ⟨60786060790039074218956301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40524040526692716145970867 60786060790039074218956301)
                ·
                  refine ⟨22794772796264652832108613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60786060790039074218956301 22794772796264652832108613)
                  ·
                    refine ⟨4274019899299622406020365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22794772796264652832108613 4274019899299622406020365)
                    ·
                      refine ⟨1602757462237358402257637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4274019899299622406020365 1602757462237358402257637)
                      ·
                        rfl

theorem cell23_3121359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 3].length) (baseStart_3121359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121359 prefixEnd_3121359 := by exact prefixLift 3121359
  have htrace : WordTrace (prefixWord ++ tailWord_3121359) baseStart_3121359 baseEnd_3121359 := by
    simpa [prefixWord, tailWord_3121359, baseEnd_3121359] using wordTrace_append hprefix tailTrace_3121359
  have hstable : (prefixWord ++ tailWord_3121359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121359).length < 2 ^ (prefixWord ++ tailWord_3121359).sum := by decide
  have hdescent : baseEnd_3121359 < baseStart_3121359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121376 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3]
def baseStart_3121376 : Nat := 118140960795 + 3121376 * 2 ^ 59
def prefixEnd_3121376 : Nat := 4983230072969 + 3 ^ 40 * 3121376 * 2
def baseEnd_3121376 : Nat := 1602766191408484835745059

theorem tailTrace_3121376 : CollatzResearch.WordTrace tailWord_3121376 prefixEnd_3121376 1602766191408484835745059 := by
  unfold tailWord_3121376
  simp only [CollatzResearch.WordTrace]
  refine ⟨56922967769897657712279991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75897290359863543616373321 56922967769897657712279991)
  ·
    refine ⟨85384451654846486568419987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56922967769897657712279991 85384451654846486568419987)
    ·
      refine ⟨128076677482269729852629981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85384451654846486568419987 128076677482269729852629981)
      ·
        refine ⟨48028754055851148694736243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128076677482269729852629981 48028754055851148694736243)
        ·
          refine ⟨72043131083776723042104365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48028754055851148694736243 72043131083776723042104365)
          ·
            refine ⟨27016174156416271140789137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72043131083776723042104365 27016174156416271140789137)
            ·
              refine ⟨20262130617312203355591853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27016174156416271140789137 20262130617312203355591853)
              ·
                refine ⟨7598298981492076258346945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20262130617312203355591853 7598298981492076258346945)
                ·
                  refine ⟨5698724236119057193760209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7598298981492076258346945 5698724236119057193760209)
                  ·
                    refine ⟨4274043177089292895320157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5698724236119057193760209 4274043177089292895320157)
                    ·
                      refine ⟨1602766191408484835745059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4274043177089292895320157 1602766191408484835745059)
                      ·
                        rfl

theorem cell23_3121376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_3121376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121376 prefixEnd_3121376 := by exact prefixLift 3121376
  have htrace : WordTrace (prefixWord ++ tailWord_3121376) baseStart_3121376 baseEnd_3121376 := by
    simpa [prefixWord, tailWord_3121376, baseEnd_3121376] using wordTrace_append hprefix tailTrace_3121376
  have hstable : (prefixWord ++ tailWord_3121376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121376).length < 2 ^ (prefixWord ++ tailWord_3121376).sum := by decide
  have hdescent : baseEnd_3121376 < baseStart_3121376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121443 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 1, 5]
def baseStart_3121443 : Nat := 118140960795 + 3121443 * 2 ^ 59
def prefixEnd_3121443 : Nat := 4983230072969 + 3 ^ 40 * 3121443 * 2
def baseEnd_3121443 : Nat := 534266864870778691202417

theorem tailTrace_3121443 : CollatzResearch.WordTrace tailWord_3121443 prefixEnd_3121443 534266864870778691202417 := by
  unfold tailWord_3121443
  simp only [CollatzResearch.WordTrace]
  refine ⟨113848379230552585867248983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75898919487035057244832655 113848379230552585867248983)
  ·
    refine ⟨170772568845828878800873475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113848379230552585867248983 170772568845828878800873475)
    ·
      refine ⟨256158853268743318201310213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170772568845828878800873475 256158853268743318201310213)
      ·
        refine ⟨48029784987889372162745665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256158853268743318201310213 48029784987889372162745665)
        ·
          refine ⟨36022338740917029122059249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48029784987889372162745665 36022338740917029122059249)
          ·
            refine ⟨27016754055687771841544437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36022338740917029122059249 27016754055687771841544437)
            ·
              refine ⟨2532820692720728610144791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27016754055687771841544437 2532820692720728610144791)
              ·
                refine ⟨3799231039081092915217187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532820692720728610144791 3799231039081092915217187)
                ·
                  refine ⟨5698846558621639372825781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3799231039081092915217187 5698846558621639372825781)
                  ·
                    refine ⟨534266864870778691202417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5698846558621639372825781 534266864870778691202417)
                    ·
                      rfl

theorem cell23_3121443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 5].length) (baseStart_3121443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121443 prefixEnd_3121443 := by exact prefixLift 3121443
  have htrace : WordTrace (prefixWord ++ tailWord_3121443) baseStart_3121443 baseEnd_3121443 := by
    simpa [prefixWord, tailWord_3121443, baseEnd_3121443] using wordTrace_append hprefix tailTrace_3121443
  have hstable : (prefixWord ++ tailWord_3121443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121443).length < 2 ^ (prefixWord ++ tailWord_3121443).sum := by decide
  have hdescent : baseEnd_3121443 < baseStart_3121443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121447 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 6]
def baseStart_3121447 : Nat := 118140960795 + 3121447 * 2 ^ 59
def prefixEnd_3121447 : Nat := 4983230072969 + 3 ^ 40 * 3121447 * 2
def baseEnd_3121447 : Nat := 178089183170550450884137

theorem tailTrace_3121447 : CollatzResearch.WordTrace tailWord_3121447 prefixEnd_3121447 178089183170550450884137 := by
  unfold tailWord_3121447
  simp only [CollatzResearch.WordTrace]
  refine ⟨113848525122538094550394595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75899016748358729700263063 113848525122538094550394595)
  ·
    refine ⟨170772787683807141825591893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113848525122538094550394595 170772787683807141825591893)
    ·
      refine ⟨2001243605669614943268655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 170772787683807141825591893 2001243605669614943268655)
      ·
        refine ⟨3001865408504422414902983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001243605669614943268655 3001865408504422414902983)
        ·
          refine ⟨4502798112756633622354475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3001865408504422414902983 4502798112756633622354475)
          ·
            refine ⟨6754197169134950433531713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4502798112756633622354475 6754197169134950433531713)
            ·
              refine ⟨5065647876851212825148785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6754197169134950433531713 5065647876851212825148785)
              ·
                refine ⟨3799235907638409618861589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5065647876851212825148785 3799235907638409618861589)
                ·
                  refine ⟨178089183170550450884137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3799235907638409618861589 178089183170550450884137)
                  ·
                    rfl

theorem cell23_3121447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 6].length) (baseStart_3121447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121447 prefixEnd_3121447 := by exact prefixLift 3121447
  have htrace : WordTrace (prefixWord ++ tailWord_3121447) baseStart_3121447 baseEnd_3121447 := by
    simpa [prefixWord, tailWord_3121447, baseEnd_3121447] using wordTrace_append hprefix tailTrace_3121447
  have hstable : (prefixWord ++ tailWord_3121447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121447).length < 2 ^ (prefixWord ++ tailWord_3121447).sum := by decide
  have hdescent : baseEnd_3121447 < baseStart_3121447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121457 : List Nat := [1, 2, 2, 3, 4, 1, 1, 4, 1, 1, 3]
def baseStart_3121457 : Nat := 118140960795 + 3121457 * 2 ^ 59
def prefixEnd_3121457 : Nat := 4983230072969 + 3 ^ 40 * 3121457 * 2
def baseEnd_3121457 : Nat := 1602807783341499018832187

theorem tailTrace_3121457 : CollatzResearch.WordTrace tailWord_3121457 prefixEnd_3121457 1602807783341499018832187 := by
  unfold tailWord_3121457
  simp only [CollatzResearch.WordTrace]
  refine ⟨113848889852501866258258625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75899259901667910838839083 113848889852501866258258625)
  ·
    refine ⟨85386667389376399693693969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113848889852501866258258625 85386667389376399693693969)
    ·
      refine ⟨64040000542032299770270477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85386667389376399693693969 64040000542032299770270477)
      ·
        refine ⟨24015000203262112413851429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64040000542032299770270477 24015000203262112413851429)
        ·
          refine ⟨4502812538111646077597143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24015000203262112413851429 4502812538111646077597143)
          ·
            refine ⟨6754218807167469116395715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4502812538111646077597143 6754218807167469116395715)
            ·
              refine ⟨10131328210751203674593573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6754218807167469116395715 10131328210751203674593573)
              ·
                refine ⟨1899624039515850688986295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10131328210751203674593573 1899624039515850688986295)
                ·
                  refine ⟨2849436059273776033479443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899624039515850688986295 2849436059273776033479443)
                  ·
                    refine ⟨4274154088910664050219165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2849436059273776033479443 4274154088910664050219165)
                    ·
                      refine ⟨1602807783341499018832187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4274154088910664050219165 1602807783341499018832187)
                      ·
                        rfl

theorem cell23_3121457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_3121457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121457 prefixEnd_3121457 := by exact prefixLift 3121457
  have htrace : WordTrace (prefixWord ++ tailWord_3121457) baseStart_3121457 baseEnd_3121457 := by
    simpa [prefixWord, tailWord_3121457, baseEnd_3121457] using wordTrace_append hprefix tailTrace_3121457
  have hstable : (prefixWord ++ tailWord_3121457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121457).length < 2 ^ (prefixWord ++ tailWord_3121457).sum := by decide
  have hdescent : baseEnd_3121457 < baseStart_3121457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121463 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 7, 2, 2]
def baseStart_3121463 : Nat := 118140960795 + 3121463 * 2 ^ 59
def prefixEnd_3121463 : Nat := 4983230072969 + 3 ^ 40 * 3121463 * 2
def baseEnd_3121463 : Nat := 1602810864225425995357159

theorem tailTrace_3121463 : CollatzResearch.WordTrace tailWord_3121463 prefixEnd_3121463 1602810864225425995357159 := by
  unfold tailWord_3121463
  simp only [CollatzResearch.WordTrace]
  refine ⟨113849108690480129282977043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75899405793653419521984695 113849108690480129282977043)
  ·
    refine ⟨170773663035720193924465565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113849108690480129282977043 170773663035720193924465565)
    ·
      refine ⟨64040123638395072721674587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170773663035720193924465565 64040123638395072721674587)
      ·
        refine ⟨96060185457592609082511881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64040123638395072721674587 96060185457592609082511881)
        ·
          refine ⟨72045139093194456811883911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96060185457592609082511881 72045139093194456811883911)
          ·
            refine ⟨108067708639791685217825867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72045139093194456811883911 108067708639791685217825867)
            ·
              refine ⟨162101562959687527826738801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108067708639791685217825867 162101562959687527826738801)
              ·
                refine ⟨121576172219765645870054101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162101562959687527826738801 121576172219765645870054101)
                ·
                  refine ⟨2849441536400757325079393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 121576172219765645870054101 2849441536400757325079393)
                  ·
                    refine ⟨2137081152300567993809545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2849441536400757325079393 2137081152300567993809545)
                    ·
                      refine ⟨1602810864225425995357159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137081152300567993809545 1602810864225425995357159)
                      ·
                        rfl

theorem cell23_3121463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_3121463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121463 prefixEnd_3121463 := by exact prefixLift 3121463
  have htrace : WordTrace (prefixWord ++ tailWord_3121463) baseStart_3121463 baseEnd_3121463 := by
    simpa [prefixWord, tailWord_3121463, baseEnd_3121463] using wordTrace_append hprefix tailTrace_3121463
  have hstable : (prefixWord ++ tailWord_3121463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121463).length < 2 ^ (prefixWord ++ tailWord_3121463).sum := by decide
  have hdescent : baseEnd_3121463 < baseStart_3121463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121496 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 3, 3, 3]
def baseStart_3121496 : Nat := 118140960795 + 3121496 * 2 ^ 59
def prefixEnd_3121496 : Nat := 4983230072969 + 3 ^ 40 * 3121496 * 2
def baseEnd_3121496 : Nat := 1602827809087024366244507

theorem tailTrace_3121496 : CollatzResearch.WordTrace tailWord_3121496 prefixEnd_3121496 1602827809087024366244507 := by
  unfold tailWord_3121496
  simp only [CollatzResearch.WordTrace]
  refine ⟨56925156149680287959464171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75900208199573717279285561 56925156149680287959464171)
  ·
    refine ⟨85387734224520431939196257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56925156149680287959464171 85387734224520431939196257)
    ·
      refine ⟨64040800668390323954397193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85387734224520431939196257 64040800668390323954397193)
      ·
        refine ⟨48030600501292742965797895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64040800668390323954397193 48030600501292742965797895)
        ·
          refine ⟨72045900751939114448696843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48030600501292742965797895 72045900751939114448696843)
          ·
            refine ⟨108068851127908671673045265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72045900751939114448696843 108068851127908671673045265)
            ·
              refine ⟨81051638345931503754783949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108068851127908671673045265 81051638345931503754783949)
              ·
                refine ⟨30394364379724313908043981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81051638345931503754783949 30394364379724313908043981)
                ·
                  refine ⟨11397886642396617715516493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30394364379724313908043981 11397886642396617715516493)
                  ·
                    refine ⟨4274207490898731643318685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11397886642396617715516493 4274207490898731643318685)
                    ·
                      refine ⟨1602827809087024366244507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4274207490898731643318685 1602827809087024366244507)
                      ·
                        rfl

theorem cell23_3121496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_3121496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121496 prefixEnd_3121496 := by exact prefixLift 3121496
  have htrace : WordTrace (prefixWord ++ tailWord_3121496) baseStart_3121496 baseEnd_3121496 := by
    simpa [prefixWord, tailWord_3121496, baseEnd_3121496] using wordTrace_append hprefix tailTrace_3121496
  have hstable : (prefixWord ++ tailWord_3121496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121496).length < 2 ^ (prefixWord ++ tailWord_3121496).sum := by decide
  have hdescent : baseEnd_3121496 < baseStart_3121496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121513 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 4, 1, 3]
def baseStart_3121513 : Nat := 118140960795 + 3121513 * 2 ^ 59
def prefixEnd_3121513 : Nat := 4983230072969 + 3 ^ 40 * 3121513 * 2
def baseEnd_3121513 : Nat := 1602836538258150799731929

theorem tailTrace_3121513 : CollatzResearch.WordTrace tailWord_3121513 prefixEnd_3121513 1602836538258150799731929 := by
  unfold tailWord_3121513
  simp only [CollatzResearch.WordTrace]
  refine ⟨113850932340298987822297193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75900621560199325214864795 113850932340298987822297193)
  ·
    refine ⟨85388199255224240866722895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113850932340298987822297193 85388199255224240866722895)
    ·
      refine ⟨128082298882836361300084343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85388199255224240866722895 128082298882836361300084343)
      ·
        refine ⟨192123448324254541950126515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128082298882836361300084343 192123448324254541950126515)
        ·
          refine ⟨288185172486381812925189773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192123448324254541950126515 288185172486381812925189773)
          ·
            refine ⟨108069439682393179846946165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288185172486381812925189773 108069439682393179846946165)
            ·
              refine ⟨10131509970224360610651203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108069439682393179846946165 10131509970224360610651203)
              ·
                refine ⟨15197264955336540915976805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10131509970224360610651203 15197264955336540915976805)
                ·
                  refine ⟨2849487179125601421745651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15197264955336540915976805 2849487179125601421745651)
                  ·
                    refine ⟨4274230768688402132618477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2849487179125601421745651 4274230768688402132618477)
                    ·
                      refine ⟨1602836538258150799731929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4274230768688402132618477 1602836538258150799731929)
                      ·
                        rfl

theorem cell23_3121513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 1, 3].length) (baseStart_3121513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121513 prefixEnd_3121513 := by exact prefixLift 3121513
  have htrace : WordTrace (prefixWord ++ tailWord_3121513) baseStart_3121513 baseEnd_3121513 := by
    simpa [prefixWord, tailWord_3121513, baseEnd_3121513] using wordTrace_append hprefix tailTrace_3121513
  have hstable : (prefixWord ++ tailWord_3121513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121513).length < 2 ^ (prefixWord ++ tailWord_3121513).sum := by decide
  have hdescent : baseEnd_3121513 < baseStart_3121513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121514 : List Nat := [3, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_3121514 : Nat := 118140960795 + 3121514 * 2 ^ 59
def prefixEnd_3121514 : Nat := 4983230072969 + 3 ^ 40 * 3121514 * 2
def baseEnd_3121514 : Nat := 1602837051738805295819425

theorem tailTrace_3121514 : CollatzResearch.WordTrace tailWord_3121514 prefixEnd_3121514 1602837051738805295819425 := by
  unfold tailWord_3121514
  simp only [CollatzResearch.WordTrace]
  refine ⟨28462742203323841248270899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75900645875530243328722397 28462742203323841248270899)
  ·
    refine ⟨42694113304985761872406349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28462742203323841248270899 42694113304985761872406349)
    ·
      refine ⟨16010292489369660702152381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42694113304985761872406349 16010292489369660702152381)
      ·
        refine ⟨6003859683513622763307143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16010292489369660702152381 6003859683513622763307143)
        ·
          refine ⟨9005789525270434144960715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6003859683513622763307143 9005789525270434144960715)
          ·
            refine ⟨13508684287905651217441073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005789525270434144960715 13508684287905651217441073)
            ·
              refine ⟨10131513215929238413080805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13508684287905651217441073 10131513215929238413080805)
              ·
                refine ⟨1899658727986732202452651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10131513215929238413080805 1899658727986732202452651)
                ·
                  refine ⟨2849488091980098303678977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899658727986732202452651 2849488091980098303678977)
                  ·
                    refine ⟨2137116068985073727759233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2849488091980098303678977 2137116068985073727759233)
                    ·
                      refine ⟨1602837051738805295819425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137116068985073727759233 1602837051738805295819425)
                      ·
                        rfl

theorem cell23_3121514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_3121514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121514 prefixEnd_3121514 := by exact prefixLift 3121514
  have htrace : WordTrace (prefixWord ++ tailWord_3121514) baseStart_3121514 baseEnd_3121514 := by
    simpa [prefixWord, tailWord_3121514, baseEnd_3121514] using wordTrace_append hprefix tailTrace_3121514
  have hstable : (prefixWord ++ tailWord_3121514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121514).length < 2 ^ (prefixWord ++ tailWord_3121514).sum := by decide
  have hdescent : baseEnd_3121514 < baseStart_3121514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121581 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_3121581 : Nat := 118140960795 + 3121581 * 2 ^ 59
def prefixEnd_3121581 : Nat := 4983230072969 + 3 ^ 40 * 3121581 * 2
def baseEnd_3121581 : Nat := 1602871454942656533681617

theorem tailTrace_3121581 : CollatzResearch.WordTrace tailWord_3121581 prefixEnd_3121581 1602871454942656533681617 := by
  unfold tailWord_3121581
  simp only [CollatzResearch.WordTrace]
  refine ⟨113853412504052635435772597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75902275002701756957181731 113853412504052635435772597)
  ·
    refine ⟨10673757422254934572103681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113853412504052635435772597 10673757422254934572103681)
    ·
      refine ⟨8005318066691200929077761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10673757422254934572103681 8005318066691200929077761)
      ·
        refine ⟨6003988550018400696808321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8005318066691200929077761 6003988550018400696808321)
        ·
          refine ⟨4502991412513800522606241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6003988550018400696808321 4502991412513800522606241)
          ·
            refine ⟨3377243559385350391954681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4502991412513800522606241 3377243559385350391954681)
            ·
              refine ⟨2532932669539012793966011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3377243559385350391954681 2532932669539012793966011)
              ·
                refine ⟨3799399004308519190949017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532932669539012793966011 3799399004308519190949017)
                ·
                  refine ⟨2849549253231389393211763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3799399004308519190949017 2849549253231389393211763)
                  ·
                    refine ⟨4274323879847084089817645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2849549253231389393211763 4274323879847084089817645)
                    ·
                      refine ⟨1602871454942656533681617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4274323879847084089817645 1602871454942656533681617)
                      ·
                        rfl

theorem cell23_3121581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_3121581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121581 prefixEnd_3121581 := by exact prefixLift 3121581
  have htrace : WordTrace (prefixWord ++ tailWord_3121581) baseStart_3121581 baseEnd_3121581 := by
    simpa [prefixWord, tailWord_3121581, baseEnd_3121581] using wordTrace_append hprefix tailTrace_3121581
  have hstable : (prefixWord ++ tailWord_3121581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121581).length < 2 ^ (prefixWord ++ tailWord_3121581).sum := by decide
  have hdescent : baseEnd_3121581 < baseStart_3121581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121636 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_3121636 : Nat := 118140960795 + 3121636 * 2 ^ 59
def prefixEnd_3121636 : Nat := 4983230072969 + 3 ^ 40 * 3121636 * 2
def baseEnd_3121636 : Nat := 534299898792884606164621

theorem tailTrace_3121636 : CollatzResearch.WordTrace tailWord_3121636 prefixEnd_3121636 534299898792884606164621 := by
  unfold tailWord_3121636
  simp only [CollatzResearch.WordTrace]
  refine ⟨56927709259426689914512381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75903612345902253219349841 56927709259426689914512381)
  ·
    refine ⟨21347890972285008717942143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56927709259426689914512381 21347890972285008717942143)
    ·
      refine ⟨32021836458427513076913215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21347890972285008717942143 32021836458427513076913215)
      ·
        refine ⟨48032754687641269615369823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32021836458427513076913215 48032754687641269615369823)
        ·
          refine ⟨72049132031461904423054735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48032754687641269615369823 72049132031461904423054735)
          ·
            refine ⟨108073698047192856634582103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72049132031461904423054735 108073698047192856634582103)
            ·
              refine ⟨162110547070789284951873155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108073698047192856634582103 162110547070789284951873155)
              ·
                refine ⟨243165820606183927427809733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162110547070789284951873155 243165820606183927427809733)
                ·
                  refine ⟨45593591363659486392714325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243165820606183927427809733 45593591363659486392714325)
                  ·
                    refine ⟨534299898792884606164621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45593591363659486392714325 534299898792884606164621)
                    ·
                      rfl

theorem cell23_3121636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_3121636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121636 prefixEnd_3121636 := by exact prefixLift 3121636
  have htrace : WordTrace (prefixWord ++ tailWord_3121636) baseStart_3121636 baseEnd_3121636 := by
    simpa [prefixWord, tailWord_3121636, baseEnd_3121636] using wordTrace_append hprefix tailTrace_3121636
  have hstable : (prefixWord ++ tailWord_3121636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121636).length < 2 ^ (prefixWord ++ tailWord_3121636).sum := by decide
  have hdescent : baseEnd_3121636 < baseStart_3121636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121663 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 3]
def baseStart_3121663 : Nat := 118140960795 + 3121663 * 2 ^ 59
def prefixEnd_3121663 : Nat := 4983230072969 + 3 ^ 40 * 3121663 * 2
def baseEnd_3121663 : Nat := 1602913560356325212856239

theorem tailTrace_3121663 : CollatzResearch.WordTrace tailWord_3121663 prefixEnd_3121663 1602913560356325212856239 := by
  unfold tailWord_3121663
  simp only [CollatzResearch.WordTrace]
  refine ⟨113856403289755563440257643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75904268859837042293505095 113856403289755563440257643)
  ·
    refine ⟨170784604934633345160386465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113856403289755563440257643 170784604934633345160386465)
    ·
      refine ⟨128088453700975008870289849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170784604934633345160386465 128088453700975008870289849)
      ·
        refine ⟨96066340275731256652717387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128088453700975008870289849 96066340275731256652717387)
        ·
          refine ⟨144099510413596884979076081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96066340275731256652717387 144099510413596884979076081)
          ·
            refine ⟨108074632810197663734307061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144099510413596884979076081 108074632810197663734307061)
            ·
              refine ⟨10131996825956030975091287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108074632810197663734307061 10131996825956030975091287)
              ·
                refine ⟨15197995238934046462636931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10131996825956030975091287 15197995238934046462636931)
                ·
                  refine ⟨22796992858401069693955397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15197995238934046462636931 22796992858401069693955397)
                  ·
                    refine ⟨4274436160950200567616637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22796992858401069693955397 4274436160950200567616637)
                    ·
                      refine ⟨1602913560356325212856239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4274436160950200567616637 1602913560356325212856239)
                      ·
                        rfl

theorem cell23_3121663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_3121663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121663 prefixEnd_3121663 := by exact prefixLift 3121663
  have htrace : WordTrace (prefixWord ++ tailWord_3121663) baseStart_3121663 baseEnd_3121663 := by
    simpa [prefixWord, tailWord_3121663, baseEnd_3121663] using wordTrace_append hprefix tailTrace_3121663
  have hstable : (prefixWord ++ tailWord_3121663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121663).length < 2 ^ (prefixWord ++ tailWord_3121663).sum := by decide
  have hdescent : baseEnd_3121663 < baseStart_3121663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121713 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 3, 5]
def baseStart_3121713 : Nat := 118140960795 + 3121713 * 2 ^ 59
def prefixEnd_3121713 : Nat := 4983230072969 + 3 ^ 40 * 3121713 * 2
def baseEnd_3121713 : Nat := 534313078129683339077003

theorem tailTrace_3121713 : CollatzResearch.WordTrace tailWord_3121713 prefixEnd_3121713 534313078129683339077003 := by
  unfold tailWord_3121713
  simp only [CollatzResearch.WordTrace]
  refine ⟨113858226939574421979577793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75905484626382947986385195 113858226939574421979577793)
  ·
    refine ⟨85393670204680816484683345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113858226939574421979577793 85393670204680816484683345)
    ·
      refine ⟨64045252653510612363512509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85393670204680816484683345 64045252653510612363512509)
      ·
        refine ⟨24016969745066479636317191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64045252653510612363512509 24016969745066479636317191)
        ·
          refine ⟨36025454617599719454475787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24016969745066479636317191 36025454617599719454475787)
          ·
            refine ⟨54038181926399579181713681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36025454617599719454475787 54038181926399579181713681)
            ·
              refine ⟨40528636444799684386285261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54038181926399579181713681 40528636444799684386285261)
              ·
                refine ⟨15198238666799881644856973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40528636444799684386285261 15198238666799881644856973)
                ·
                  refine ⟨5699339500049955616821365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15198238666799881644856973 5699339500049955616821365)
                  ·
                    refine ⟨534313078129683339077003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5699339500049955616821365 534313078129683339077003)
                    ·
                      rfl

theorem cell23_3121713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_3121713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121713 prefixEnd_3121713 := by exact prefixLift 3121713
  have htrace : WordTrace (prefixWord ++ tailWord_3121713) baseStart_3121713 baseEnd_3121713 := by
    simpa [prefixWord, tailWord_3121713, baseEnd_3121713] using wordTrace_append hprefix tailTrace_3121713
  have hstable : (prefixWord ++ tailWord_3121713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121713).length < 2 ^ (prefixWord ++ tailWord_3121713).sum := by decide
  have hdescent : baseEnd_3121713 < baseStart_3121713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121720 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 1, 5, 2]
def baseStart_3121720 : Nat := 118140960795 + 3121720 * 2 ^ 59
def prefixEnd_3121720 : Nat := 4983230072969 + 3 ^ 40 * 3121720 * 2
def baseEnd_3121720 : Nat := 1602942828753631489843477

theorem tailTrace_3121720 : CollatzResearch.WordTrace tailWord_3121720 prefixEnd_3121720 1602942828753631489843477 := by
  unfold tailWord_3121720
  simp only [CollatzResearch.WordTrace]
  refine ⟨56929241125274531087541307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75905654833699374783388409 56929241125274531087541307)
  ·
    refine ⟨85393861687911796631311961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56929241125274531087541307 85393861687911796631311961)
    ·
      refine ⟨64045396265933847473483971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85393861687911796631311961 64045396265933847473483971)
      ·
        refine ⟨96068094398900771210225957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64045396265933847473483971 96068094398900771210225957)
        ·
          refine ⟨18012767699793894601917367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96068094398900771210225957 18012767699793894601917367)
          ·
            refine ⟨27019151549690841902876051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18012767699793894601917367 27019151549690841902876051)
            ·
              refine ⟨40528727324536262854314077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27019151549690841902876051 40528727324536262854314077)
              ·
                refine ⟨15198272746701098570367779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40528727324536262854314077 15198272746701098570367779)
                ·
                  refine ⟨22797409120051647855551669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15198272746701098570367779 22797409120051647855551669)
                  ·
                    refine ⟨2137257105004841986457969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22797409120051647855551669 2137257105004841986457969)
                    ·
                      refine ⟨1602942828753631489843477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137257105004841986457969 1602942828753631489843477)
                      ·
                        rfl

theorem cell23_3121720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_3121720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121720 prefixEnd_3121720 := by exact prefixLift 3121720
  have htrace : WordTrace (prefixWord ++ tailWord_3121720) baseStart_3121720 baseEnd_3121720 := by
    simpa [prefixWord, tailWord_3121720, baseEnd_3121720] using wordTrace_append hprefix tailTrace_3121720
  have hstable : (prefixWord ++ tailWord_3121720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121720).length < 2 ^ (prefixWord ++ tailWord_3121720).sum := by decide
  have hdescent : baseEnd_3121720 < baseStart_3121720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121753 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 1, 8, 3]
def baseStart_3121753 : Nat := 118140960795 + 3121753 * 2 ^ 59
def prefixEnd_3121753 : Nat := 4983230072969 + 3 ^ 40 * 3121753 * 2
def baseEnd_3121753 : Nat := 1602959773615229860730825

theorem tailTrace_3121753 : CollatzResearch.WordTrace tailWord_3121753 prefixEnd_3121753 1602959773615229860730825 := by
  unfold tailWord_3121753
  simp only [CollatzResearch.WordTrace]
  refine ⟨113859685859429508811033913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75906457239619672540689275 113859685859429508811033913)
  ·
    refine ⟨85394764394572131608275435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113859685859429508811033913 85394764394572131608275435)
    ·
      refine ⟨128092146591858197412413153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85394764394572131608275435 128092146591858197412413153)
      ·
        refine ⟨96069109943893648059309865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128092146591858197412413153 96069109943893648059309865)
        ·
          refine ⟨72051832457920236044482399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96069109943893648059309865 72051832457920236044482399)
          ·
            refine ⟨108077748686880354066723599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72051832457920236044482399 108077748686880354066723599)
            ·
              refine ⟨162116623030320531100085399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108077748686880354066723599 162116623030320531100085399)
              ·
                refine ⟨243174934545480796650128099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162116623030320531100085399 243174934545480796650128099)
                ·
                  refine ⟨364762401818221194975192149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243174934545480796650128099 364762401818221194975192149)
                  ·
                    refine ⟨4274559396307279628615533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 364762401818221194975192149 4274559396307279628615533)
                    ·
                      refine ⟨1602959773615229860730825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4274559396307279628615533 1602959773615229860730825)
                      ·
                        rfl

theorem cell23_3121753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_3121753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121753 prefixEnd_3121753 := by exact prefixLift 3121753
  have htrace : WordTrace (prefixWord ++ tailWord_3121753) baseStart_3121753 baseEnd_3121753 := by
    simpa [prefixWord, tailWord_3121753, baseEnd_3121753] using wordTrace_append hprefix tailTrace_3121753
  have hstable : (prefixWord ++ tailWord_3121753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121753).length < 2 ^ (prefixWord ++ tailWord_3121753).sum := by decide
  have hdescent : baseEnd_3121753 < baseStart_3121753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121763 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 6]
def baseStart_3121763 : Nat := 118140960795 + 3121763 * 2 ^ 59
def prefixEnd_3121763 : Nat := 4983230072969 + 3 ^ 40 * 3121763 * 2
def baseEnd_3121763 : Nat := 1602964908421774821605779

theorem tailTrace_3121763 : CollatzResearch.WordTrace tailWord_3121763 prefixEnd_3121763 1602964908421774821605779 := by
  unfold tailWord_3121763
  simp only [CollatzResearch.WordTrace]
  refine ⟨113860050589393280518897943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75906700392928853679265295 113860050589393280518897943)
  ·
    refine ⟨170790075884089920778346915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113860050589393280518897943 170790075884089920778346915)
    ·
      refine ⟨256185113826134881167520373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170790075884089920778346915 256185113826134881167520373)
      ·
        refine ⟨24017354421200145109455035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256185113826134881167520373 24017354421200145109455035)
        ·
          refine ⟨36026031631800217664182553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24017354421200145109455035 36026031631800217664182553)
          ·
            refine ⟨27019523723850163248136915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36026031631800217664182553 27019523723850163248136915)
            ·
              refine ⟨40529285585775244872205373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27019523723850163248136915 40529285585775244872205373)
              ·
                refine ⟨15198482094665716827077015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40529285585775244872205373 15198482094665716827077015)
                ·
                  refine ⟨22797723141998575240615523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15198482094665716827077015 22797723141998575240615523)
                  ·
                    refine ⟨34196584712997862860923285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22797723141998575240615523 34196584712997862860923285)
                    ·
                      refine ⟨1602964908421774821605779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34196584712997862860923285 1602964908421774821605779)
                      ·
                        rfl

theorem cell23_3121763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_3121763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121763 prefixEnd_3121763 := by exact prefixLift 3121763
  have htrace : WordTrace (prefixWord ++ tailWord_3121763) baseStart_3121763 baseEnd_3121763 := by
    simpa [prefixWord, tailWord_3121763, baseEnd_3121763] using wordTrace_append hprefix tailTrace_3121763
  have hstable : (prefixWord ++ tailWord_3121763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121763).length < 2 ^ (prefixWord ++ tailWord_3121763).sum := by decide
  have hdescent : baseEnd_3121763 < baseStart_3121763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121767 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_3121767 : Nat := 118140960795 + 3121767 * 2 ^ 59
def prefixEnd_3121767 : Nat := 4983230072969 + 3 ^ 40 * 3121767 * 2
def baseEnd_3121767 : Nat := 1602966962344392805955761

theorem tailTrace_3121767 : CollatzResearch.WordTrace tailWord_3121767 prefixEnd_3121767 1602966962344392805955761 := by
  unfold tailWord_3121767
  simp only [CollatzResearch.WordTrace]
  refine ⟨113860196481378789202043555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75906797654252526134695703 113860196481378789202043555)
  ·
    refine ⟨170790294722068183803065333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113860196481378789202043555 170790294722068183803065333)
    ·
      refine ⟨16011590130193892231537375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170790294722068183803065333 16011590130193892231537375)
      ·
        refine ⟨24017385195290838347306063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16011590130193892231537375 24017385195290838347306063)
        ·
          refine ⟨36026077792936257520959095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24017385195290838347306063 36026077792936257520959095)
          ·
            refine ⟨54039116689404386281438643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36026077792936257520959095 54039116689404386281438643)
            ·
              refine ⟨81058675034106579422157965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54039116689404386281438643 81058675034106579422157965)
              ·
                refine ⟨30397003137789967283309237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81058675034106579422157965 30397003137789967283309237)
                ·
                  refine ⟨2849719044167809432810241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30397003137789967283309237 2849719044167809432810241)
                  ·
                    refine ⟨2137289283125857074607681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2849719044167809432810241 2137289283125857074607681)
                    ·
                      refine ⟨1602966962344392805955761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137289283125857074607681 1602966962344392805955761)
                      ·
                        rfl

theorem cell23_3121767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_3121767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121767 prefixEnd_3121767 := by exact prefixLift 3121767
  have htrace : WordTrace (prefixWord ++ tailWord_3121767) baseStart_3121767 baseEnd_3121767 := by
    simpa [prefixWord, tailWord_3121767, baseEnd_3121767] using wordTrace_append hprefix tailTrace_3121767
  have hstable : (prefixWord ++ tailWord_3121767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121767).length < 2 ^ (prefixWord ++ tailWord_3121767).sum := by decide
  have hdescent : baseEnd_3121767 < baseStart_3121767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121813 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_3121813 : Nat := 118140960795 + 3121813 * 2 ^ 59
def prefixEnd_3121813 : Nat := 4983230072969 + 3 ^ 40 * 3121813 * 2
def baseEnd_3121813 : Nat := 1602990582454499625980549

theorem tailTrace_3121813 : CollatzResearch.WordTrace tailWord_3121813 prefixEnd_3121813 1602990582454499625980549 := by
  unfold tailWord_3121813
  simp only [CollatzResearch.WordTrace]
  refine ⟨113861874239212139058218093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75907916159474759372145395 113861874239212139058218093)
  ·
    refine ⟨42698202839704552146831785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113861874239212139058218093 42698202839704552146831785)
    ·
      refine ⟨32023652129778414110123839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42698202839704552146831785 32023652129778414110123839)
      ·
        refine ⟨48035478194667621165185759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32023652129778414110123839 48035478194667621165185759)
        ·
          refine ⟨72053217292001431747778639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48035478194667621165185759 72053217292001431747778639)
          ·
            refine ⟨108079825938002147621667959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72053217292001431747778639 108079825938002147621667959)
            ·
              refine ⟨162119738907003221432501939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108079825938002147621667959 162119738907003221432501939)
              ·
                refine ⟨243179608360504832148752909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162119738907003221432501939 243179608360504832148752909)
                ·
                  refine ⟨91192353135189312055782341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243179608360504832148752909 91192353135189312055782341)
                  ·
                    refine ⟨17098566212847996010459189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91192353135189312055782341 17098566212847996010459189)
                    ·
                      refine ⟨1602990582454499625980549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17098566212847996010459189 1602990582454499625980549)
                      ·
                        rfl

theorem cell23_3121813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_3121813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121813 prefixEnd_3121813 := by exact prefixLift 3121813
  have htrace : WordTrace (prefixWord ++ tailWord_3121813) baseStart_3121813 baseEnd_3121813 := by
    simpa [prefixWord, tailWord_3121813, baseEnd_3121813] using wordTrace_append hprefix tailTrace_3121813
  have hstable : (prefixWord ++ tailWord_3121813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121813).length < 2 ^ (prefixWord ++ tailWord_3121813).sum := by decide
  have hdescent : baseEnd_3121813 < baseStart_3121813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121817 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 2, 1, 3]
def baseStart_3121817 : Nat := 118140960795 + 3121817 * 2 ^ 59
def prefixEnd_3121817 : Nat := 4983230072969 + 3 ^ 40 * 3121817 * 2
def baseEnd_3121817 : Nat := 1602992636377117610330531

theorem tailTrace_3121817 : CollatzResearch.WordTrace tailWord_3121817 prefixEnd_3121817 1602992636377117610330531 := by
  unfold tailWord_3121817
  simp only [CollatzResearch.WordTrace]
  refine ⟨113862020131197647741363705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75908013420798431827575803 113862020131197647741363705)
  ·
    refine ⟨85396515098398235806022779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113862020131197647741363705 85396515098398235806022779)
    ·
      refine ⟨128094772647597353709034169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85396515098398235806022779 128094772647597353709034169)
      ·
        refine ⟨96071079485698015281775627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128094772647597353709034169 96071079485698015281775627)
        ·
          refine ⟨144106619228547022922663441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96071079485698015281775627 144106619228547022922663441)
          ·
            refine ⟨108079964421410267191997581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144106619228547022922663441 108079964421410267191997581)
            ·
              refine ⟨40529986658028850196999093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108079964421410267191997581 40529986658028850196999093)
              ·
                refine ⟨3799686249190204705968665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40529986658028850196999093 3799686249190204705968665)
                ·
                  refine ⟨2849764686892653529476499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3799686249190204705968665 2849764686892653529476499)
                  ·
                    refine ⟨4274647030338980294214749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2849764686892653529476499 4274647030338980294214749)
                    ·
                      refine ⟨1602992636377117610330531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4274647030338980294214749 1602992636377117610330531)
                      ·
                        rfl

theorem cell23_3121817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_3121817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121817 prefixEnd_3121817 := by exact prefixLift 3121817
  have htrace : WordTrace (prefixWord ++ tailWord_3121817) baseStart_3121817 baseEnd_3121817 := by
    simpa [prefixWord, tailWord_3121817, baseEnd_3121817] using wordTrace_append hprefix tailTrace_3121817
  have hstable : (prefixWord ++ tailWord_3121817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121817).length < 2 ^ (prefixWord ++ tailWord_3121817).sum := by decide
  have hdescent : baseEnd_3121817 < baseStart_3121817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121833 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 4, 6]
def baseStart_3121833 : Nat := 118140960795 + 3121833 * 2 ^ 59
def prefixEnd_3121833 : Nat := 4983230072969 + 3 ^ 40 * 3121833 * 2
def baseEnd_3121833 : Nat := 534333617355863182576819

theorem tailTrace_3121833 : CollatzResearch.WordTrace tailWord_3121833 prefixEnd_3121833 534333617355863182576819 := by
  unfold tailWord_3121833
  simp only [CollatzResearch.WordTrace]
  refine ⟨113862603699139682473946153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75908402466093121649297435 113862603699139682473946153)
  ·
    refine ⟨85396952774354761855459615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113862603699139682473946153 85396952774354761855459615)
    ·
      refine ⟨128095429161532142783189423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85396952774354761855459615 128095429161532142783189423)
      ·
        refine ⟨192143143742298214174784135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128095429161532142783189423 192143143742298214174784135)
        ·
          refine ⟨288214715613447321262176203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192143143742298214174784135 288214715613447321262176203)
          ·
            refine ⟨432322073420170981893264305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288214715613447321262176203 432322073420170981893264305)
            ·
              refine ⟨324241555065128236419948229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432322073420170981893264305 324241555065128236419948229)
              ·
                refine ⟨60795291574711544328740293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324241555065128236419948229 60795291574711544328740293)
                ·
                  refine ⟨11399117170258414561638805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60795291574711544328740293 11399117170258414561638805)
                  ·
                    refine ⟨534333617355863182576819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11399117170258414561638805 534333617355863182576819)
                    ·
                      rfl

theorem cell23_3121833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_3121833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121833 prefixEnd_3121833 := by exact prefixLift 3121833
  have htrace : WordTrace (prefixWord ++ tailWord_3121833) baseStart_3121833 baseEnd_3121833 := by
    simpa [prefixWord, tailWord_3121833, baseEnd_3121833] using wordTrace_append hprefix tailTrace_3121833
  have hstable : (prefixWord ++ tailWord_3121833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121833).length < 2 ^ (prefixWord ++ tailWord_3121833).sum := by decide
  have hdescent : baseEnd_3121833 < baseStart_3121833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
