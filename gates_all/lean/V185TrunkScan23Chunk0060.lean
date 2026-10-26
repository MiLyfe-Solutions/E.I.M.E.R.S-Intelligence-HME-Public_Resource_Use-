import V185TrunkScan23Chunk0059

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_354913 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 4, 2, 2]
def baseStart_354913 : Nat := 118140960795 + 354913 * 2 ^ 59
def prefixEnd_354913 : Nat := 4983230072969 + 3 ^ 40 * 354913 * 2
def baseEnd_354913 : Nat := 182240959529275134955291

theorem tailTrace_354913 : CollatzResearch.WordTrace tailWord_354913 prefixEnd_354913 182240959529275134955291 := by
  unfold tailWord_354913
  simp only [CollatzResearch.WordTrace]
  refine ⟨12944740563218290159757393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8629827042145526773171595 12944740563218290159757393)
  ·
    refine ⟨9708555422413717619818045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12944740563218290159757393 9708555422413717619818045)
    ·
      refine ⟨3640708283405144107431767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9708555422413717619818045 3640708283405144107431767)
      ·
        refine ⟨5461062425107716161147651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640708283405144107431767 5461062425107716161147651)
        ·
          refine ⟨8191593637661574241721477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5461062425107716161147651 8191593637661574241721477)
          ·
            refine ⟨1535923807061545170322777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8191593637661574241721477 1535923807061545170322777)
            ·
              refine ⟨1151942855296158877742083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535923807061545170322777 1151942855296158877742083)
              ·
                refine ⟨1727914282944238316613125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151942855296158877742083 1727914282944238316613125)
                ·
                  refine ⟨323983928052044684364961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727914282944238316613125 323983928052044684364961)
                  ·
                    refine ⟨242987946039033513273721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 323983928052044684364961 242987946039033513273721)
                    ·
                      refine ⟨182240959529275134955291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 242987946039033513273721 182240959529275134955291)
                      ·
                        rfl

theorem cell23_354913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_354913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354913 prefixEnd_354913 := by exact prefixLift 354913
  have htrace : WordTrace (prefixWord ++ tailWord_354913) baseStart_354913 baseEnd_354913 := by
    simpa [prefixWord, tailWord_354913, baseEnd_354913] using wordTrace_append hprefix tailTrace_354913
  have hstable : (prefixWord ++ tailWord_354913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354913).length < 2 ^ (prefixWord ++ tailWord_354913).sum := by decide
  have hdescent : baseEnd_354913 < baseStart_354913 := by decide
  rcases family_descends (prefixWord ++ tailWord_354913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354934 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_354934 : Nat := 118140960795 + 354934 * 2 ^ 59
def prefixEnd_354934 : Nat := 4983230072969 + 3 ^ 40 * 354934 * 2
def baseEnd_354934 : Nat := 182251742623019552792695

theorem tailTrace_354934 : CollatzResearch.WordTrace tailWord_354934 prefixEnd_354934 182251742623019552792695 := by
  unfold tailWord_354934
  simp only [CollatzResearch.WordTrace]
  refine ⟨809094156008888171641991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8630337664094807164181237 809094156008888171641991)
  ·
    refine ⟨1213641234013332257462987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 809094156008888171641991 1213641234013332257462987)
    ·
      refine ⟨1820461851019998386194481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1213641234013332257462987 1820461851019998386194481)
      ·
        refine ⟨1365346388264998789645861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1820461851019998386194481 1365346388264998789645861)
        ·
          refine ⟨256002447799687273058599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1365346388264998789645861 256002447799687273058599)
          ·
            refine ⟨384003671699530909587899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256002447799687273058599 384003671699530909587899)
            ·
              refine ⟨576005507549296364381849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384003671699530909587899 576005507549296364381849)
              ·
                refine ⟨432004130661972273286387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576005507549296364381849 432004130661972273286387)
                ·
                  refine ⟨648006195992958409929581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432004130661972273286387 648006195992958409929581)
                  ·
                    refine ⟨243002323497359403723593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648006195992958409929581 243002323497359403723593)
                    ·
                      refine ⟨182251742623019552792695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243002323497359403723593 182251742623019552792695)
                      ·
                        rfl

theorem cell23_354934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_354934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354934 prefixEnd_354934 := by exact prefixLift 354934
  have htrace : WordTrace (prefixWord ++ tailWord_354934) baseStart_354934 baseEnd_354934 := by
    simpa [prefixWord, tailWord_354934, baseEnd_354934] using wordTrace_append hprefix tailTrace_354934
  have hstable : (prefixWord ++ tailWord_354934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354934).length < 2 ^ (prefixWord ++ tailWord_354934).sum := by decide
  have hdescent : baseEnd_354934 < baseStart_354934 := by decide
  rcases family_descends (prefixWord ++ tailWord_354934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354970 : List Nat := [3, 1, 1, 6, 1, 1, 1, 4, 5]
def baseStart_354970 : Nat := 118140960795 + 354970 * 2 ^ 59
def prefixEnd_354970 : Nat := 4983230072969 + 3 ^ 40 * 354970 * 2
def baseEnd_354970 : Nat := 20252247547397934660281

theorem tailTrace_354970 : CollatzResearch.WordTrace tailWord_354970 prefixEnd_354970 20252247547397934660281 := by
  unfold tailWord_354970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3236704881002947223645591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8631213016007859263054909 3236704881002947223645591)
  ·
    refine ⟨4855057321504420835468387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3236704881002947223645591 4855057321504420835468387)
    ·
      refine ⟨7282585982256631253202581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4855057321504420835468387 7282585982256631253202581)
      ·
        refine ⟨341371217918279589993871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7282585982256631253202581 341371217918279589993871)
        ·
          refine ⟨512056826877419384990807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341371217918279589993871 512056826877419384990807)
          ·
            refine ⟨768085240316129077486211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512056826877419384990807 768085240316129077486211)
            ·
              refine ⟨1152127860474193616229317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768085240316129077486211 1152127860474193616229317)
              ·
                refine ⟨216023973838911303042997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1152127860474193616229317 216023973838911303042997)
                ·
                  refine ⟨20252247547397934660281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 216023973838911303042997 20252247547397934660281)
                  ·
                    rfl

theorem cell23_354970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_354970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_354970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_354970 prefixEnd_354970 := by exact prefixLift 354970
  have htrace : WordTrace (prefixWord ++ tailWord_354970) baseStart_354970 baseEnd_354970 := by
    simpa [prefixWord, tailWord_354970, baseEnd_354970] using wordTrace_append hprefix tailTrace_354970
  have hstable : (prefixWord ++ tailWord_354970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354970).length < 2 ^ (prefixWord ++ tailWord_354970).sum := by decide
  have hdescent : baseEnd_354970 < baseStart_354970 := by decide
  rcases family_descends (prefixWord ++ tailWord_354970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355049 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_355049 : Nat := 118140960795 + 355049 * 2 ^ 59
def prefixEnd_355049 : Nat := 4983230072969 + 3 ^ 40 * 355049 * 2
def baseEnd_355049 : Nat := 182310792898286602854665

theorem tailTrace_355049 : CollatzResearch.WordTrace tailWord_355049 prefixEnd_355049 182310792898286602854665 := by
  unfold tailWord_355049
  simp only [CollatzResearch.WordTrace]
  refine ⟨12949700890725585386708201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8633133927150390257805467 12949700890725585386708201)
  ·
    refine ⟨9712275668044189040031151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12949700890725585386708201 9712275668044189040031151)
    ·
      refine ⟨14568413502066283560046727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9712275668044189040031151 14568413502066283560046727)
      ·
        refine ⟨21852620253099425340070091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14568413502066283560046727 21852620253099425340070091)
        ·
          refine ⟨32778930379649138010105137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21852620253099425340070091 32778930379649138010105137)
          ·
            refine ⟨24584197784736853507578853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32778930379649138010105137 24584197784736853507578853)
            ·
              refine ⟨4609537084638160032671035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24584197784736853507578853 4609537084638160032671035)
              ·
                refine ⟨6914305626957240049006553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4609537084638160032671035 6914305626957240049006553)
                ·
                  refine ⟨5185729220217930036754915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6914305626957240049006553 5185729220217930036754915)
                  ·
                    refine ⟨7778593830326895055132373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5185729220217930036754915 7778593830326895055132373)
                    ·
                      refine ⟨182310792898286602854665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7778593830326895055132373 182310792898286602854665)
                      ·
                        rfl

theorem cell23_355049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_355049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355049 prefixEnd_355049 := by exact prefixLift 355049
  have htrace : WordTrace (prefixWord ++ tailWord_355049) baseStart_355049 baseEnd_355049 := by
    simpa [prefixWord, tailWord_355049, baseEnd_355049] using wordTrace_append hprefix tailTrace_355049
  have hstable : (prefixWord ++ tailWord_355049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355049).length < 2 ^ (prefixWord ++ tailWord_355049).sum := by decide
  have hdescent : baseEnd_355049 < baseStart_355049 := by decide
  rcases family_descends (prefixWord ++ tailWord_355049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355063 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 2, 3, 2]
def baseStart_355063 : Nat := 118140960795 + 355063 * 2 ^ 59
def prefixEnd_355063 : Nat := 4983230072969 + 3 ^ 40 * 355063 * 2
def baseEnd_355063 : Nat := 182317981627449548079601

theorem tailTrace_355063 : CollatzResearch.WordTrace tailWord_355063 prefixEnd_355063 182317981627449548079601 := by
  unfold tailWord_355063
  simp only [CollatzResearch.WordTrace]
  refine ⟨12950211512674865777717843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8633474341783243851811895 12950211512674865777717843)
  ·
    refine ⟨19425317269012298666576765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12950211512674865777717843 19425317269012298666576765)
    ·
      refine ⟨7284493975879611999966287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19425317269012298666576765 7284493975879611999966287)
      ·
        refine ⟨10926740963819417999949431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7284493975879611999966287 10926740963819417999949431)
        ·
          refine ⟨16390111445729126999924147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10926740963819417999949431 16390111445729126999924147)
          ·
            refine ⟨24585167168593690499886221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16390111445729126999924147 24585167168593690499886221)
            ·
              refine ⟨9219437688222633937457333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24585167168593690499886221 9219437688222633937457333)
              ·
                refine ⟨864322283270871931636625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9219437688222633937457333 864322283270871931636625)
                ·
                  refine ⟨648241712453153948727469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 864322283270871931636625 648241712453153948727469)
                  ·
                    refine ⟨243090642169932730772801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648241712453153948727469 243090642169932730772801)
                    ·
                      refine ⟨182317981627449548079601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243090642169932730772801 182317981627449548079601)
                      ·
                        rfl

theorem cell23_355063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_355063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355063 prefixEnd_355063 := by exact prefixLift 355063
  have htrace : WordTrace (prefixWord ++ tailWord_355063) baseStart_355063 baseEnd_355063 := by
    simpa [prefixWord, tailWord_355063, baseEnd_355063] using wordTrace_append hprefix tailTrace_355063
  have hstable : (prefixWord ++ tailWord_355063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355063).length < 2 ^ (prefixWord ++ tailWord_355063).sum := by decide
  have hdescent : baseEnd_355063 < baseStart_355063 := by decide
  rcases family_descends (prefixWord ++ tailWord_355063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355080 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 2, 3, 2]
def baseStart_355080 : Nat := 118140960795 + 355080 * 2 ^ 59
def prefixEnd_355080 : Nat := 4983230072969 + 3 ^ 40 * 355080 * 2
def baseEnd_355080 : Nat := 182326710798575981567023

theorem tailTrace_355080 : CollatzResearch.WordTrace tailWord_355080 prefixEnd_355080 182326710798575981567023 := by
  unfold tailWord_355080
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475415776806638840543347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8633887702408851787391129 6475415776806638840543347)
  ·
    refine ⟨9713123665209958260815021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6475415776806638840543347 9713123665209958260815021)
    ·
      refine ⟨3642421374453734347805633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9713123665209958260815021 3642421374453734347805633)
      ·
        refine ⟨2731816030840300760854225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3642421374453734347805633 2731816030840300760854225)
        ·
          refine ⟨2048862023130225570640669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2731816030840300760854225 2048862023130225570640669)
          ·
            refine ⟨768323258673834588990251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2048862023130225570640669 768323258673834588990251)
            ·
              refine ⟨1152484888010751883485377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768323258673834588990251 1152484888010751883485377)
              ·
                refine ⟨864363666008063912614033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152484888010751883485377 864363666008063912614033)
                ·
                  refine ⟨648272749506047934460525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 864363666008063912614033 648272749506047934460525)
                  ·
                    refine ⟨243102281064767975422697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648272749506047934460525 243102281064767975422697)
                    ·
                      refine ⟨182326710798575981567023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243102281064767975422697 182326710798575981567023)
                      ·
                        rfl

theorem cell23_355080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_355080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355080 prefixEnd_355080 := by exact prefixLift 355080
  have htrace : WordTrace (prefixWord ++ tailWord_355080) baseStart_355080 baseEnd_355080 := by
    simpa [prefixWord, tailWord_355080, baseEnd_355080] using wordTrace_append hprefix tailTrace_355080
  have hstable : (prefixWord ++ tailWord_355080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355080).length < 2 ^ (prefixWord ++ tailWord_355080).sum := by decide
  have hdescent : baseEnd_355080 < baseStart_355080 := by decide
  rcases family_descends (prefixWord ++ tailWord_355080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355087 : List Nat := [1, 1, 2, 1, 1, 1, 9, 2, 1, 1, 3]
def baseStart_355087 : Nat := 118140960795 + 355087 * 2 ^ 59
def prefixEnd_355087 : Nat := 4983230072969 + 3 ^ 40 * 355087 * 2
def baseEnd_355087 : Nat := 182330305163157454179491

theorem tailTrace_355087 : CollatzResearch.WordTrace tailWord_355087 prefixEnd_355087 182330305163157454179491 := by
  unfold tailWord_355087
  simp only [CollatzResearch.WordTrace]
  refine ⟨12951086864587917876591515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8634057909725278584394343 12951086864587917876591515)
  ·
    refine ⟨19426630296881876814887273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12951086864587917876591515 19426630296881876814887273)
    ·
      refine ⟨14569972722661407611165455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19426630296881876814887273 14569972722661407611165455)
      ·
        refine ⟨21854959083992111416748183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14569972722661407611165455 21854959083992111416748183)
        ·
          refine ⟨32782438625988167125122275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21854959083992111416748183 32782438625988167125122275)
          ·
            refine ⟨49173657938982250687683413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32782438625988167125122275 49173657938982250687683413)
            ·
              refine ⟨288126901986224125123145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 49173657938982250687683413 288126901986224125123145)
              ·
                refine ⟨216095176489668093842359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288126901986224125123145 216095176489668093842359)
                ·
                  refine ⟨324142764734502140763539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216095176489668093842359 324142764734502140763539)
                  ·
                    refine ⟨486214147101753211145309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 324142764734502140763539 486214147101753211145309)
                    ·
                      refine ⟨182330305163157454179491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 486214147101753211145309 182330305163157454179491)
                      ·
                        rfl

theorem cell23_355087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 1, 1, 3].length) (baseStart_355087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355087 prefixEnd_355087 := by exact prefixLift 355087
  have htrace : WordTrace (prefixWord ++ tailWord_355087) baseStart_355087 baseEnd_355087 := by
    simpa [prefixWord, tailWord_355087, baseEnd_355087] using wordTrace_append hprefix tailTrace_355087
  have hstable : (prefixWord ++ tailWord_355087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355087).length < 2 ^ (prefixWord ++ tailWord_355087).sum := by decide
  have hdescent : baseEnd_355087 < baseStart_355087 := by decide
  rcases family_descends (prefixWord ++ tailWord_355087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355096 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 2, 6, 3]
def baseStart_355096 : Nat := 118140960795 + 355096 * 2 ^ 59
def prefixEnd_355096 : Nat := 4983230072969 + 3 ^ 40 * 355096 * 2
def baseEnd_355096 : Nat := 182334926489047918966949

theorem tailTrace_355096 : CollatzResearch.WordTrace tailWord_355096 prefixEnd_355096 182334926489047918966949 := by
  unfold tailWord_355096
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475707560777656206834571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8634276747703541609112761 6475707560777656206834571)
  ·
    refine ⟨9713561341166484310251857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6475707560777656206834571 9713561341166484310251857)
    ·
      refine ⟨7285171005874863232688893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9713561341166484310251857 7285171005874863232688893)
      ·
        refine ⟨2731939127203073712258335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7285171005874863232688893 2731939127203073712258335)
        ·
          refine ⟨4097908690804610568387503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731939127203073712258335 4097908690804610568387503)
          ·
            refine ⟨6146863036206915852581255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097908690804610568387503 6146863036206915852581255)
            ·
              refine ⟨9220294554310373778871883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6146863036206915852581255 9220294554310373778871883)
              ·
                refine ⟨13830441831465560668307825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9220294554310373778871883 13830441831465560668307825)
                ·
                  refine ⟨10372831373599170501230869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13830441831465560668307825 10372831373599170501230869)
                  ·
                    refine ⟨486226470637461117245197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10372831373599170501230869 486226470637461117245197)
                    ·
                      refine ⟨182334926489047918966949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 486226470637461117245197 182334926489047918966949)
                      ·
                        rfl

theorem cell23_355096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_355096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355096 prefixEnd_355096 := by exact prefixLift 355096
  have htrace : WordTrace (prefixWord ++ tailWord_355096) baseStart_355096 baseEnd_355096 := by
    simpa [prefixWord, tailWord_355096, baseEnd_355096] using wordTrace_append hprefix tailTrace_355096
  have hstable : (prefixWord ++ tailWord_355096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355096).length < 2 ^ (prefixWord ++ tailWord_355096).sum := by decide
  have hdescent : baseEnd_355096 < baseStart_355096 := by decide
  rcases family_descends (prefixWord ++ tailWord_355096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355114 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_355114 : Nat := 118140960795 + 355114 * 2 ^ 59
def prefixEnd_355114 : Nat := 4983230072969 + 3 ^ 40 * 355114 * 2
def baseEnd_355114 : Nat := 182344169140828848541867

theorem tailTrace_355114 : CollatzResearch.WordTrace tailWord_355114 prefixEnd_355114 182344169140828848541867 := by
  unfold tailWord_355114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3238017908872525371956099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8634714423660067658549597 3238017908872525371956099)
  ·
    refine ⟨4857026863308788057934149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3238017908872525371956099 4857026863308788057934149)
    ·
      refine ⟨910692536870397760862653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4857026863308788057934149 910692536870397760862653)
      ·
        refine ⟨341509701326399160323495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 910692536870397760862653 341509701326399160323495)
        ·
          refine ⟨512264551989598740485243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341509701326399160323495 512264551989598740485243)
          ·
            refine ⟨768396827984398110727865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512264551989598740485243 768396827984398110727865)
            ·
              refine ⟨576297620988298583045899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768396827984398110727865 576297620988298583045899)
              ·
                refine ⟨864446431482447874568849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576297620988298583045899 864446431482447874568849)
                ·
                  refine ⟨648334823611835905926637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 864446431482447874568849 648334823611835905926637)
                  ·
                    refine ⟨243125558854438464722489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648334823611835905926637 243125558854438464722489)
                    ·
                      refine ⟨182344169140828848541867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243125558854438464722489 182344169140828848541867)
                      ·
                        rfl

theorem cell23_355114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_355114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355114 prefixEnd_355114 := by exact prefixLift 355114
  have htrace : WordTrace (prefixWord ++ tailWord_355114) baseStart_355114 baseEnd_355114 := by
    simpa [prefixWord, tailWord_355114, baseEnd_355114] using wordTrace_append hprefix tailTrace_355114
  have hstable : (prefixWord ++ tailWord_355114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355114).length < 2 ^ (prefixWord ++ tailWord_355114).sum := by decide
  have hdescent : baseEnd_355114 < baseStart_355114 := by decide
  rcases family_descends (prefixWord ++ tailWord_355114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355123 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 4]
def baseStart_355123 : Nat := 118140960795 + 355123 * 2 ^ 59
def prefixEnd_355123 : Nat := 4983230072969 + 3 ^ 40 * 355123 * 2
def baseEnd_355123 : Nat := 182348790466719313329325

theorem tailTrace_355123 : CollatzResearch.WordTrace tailWord_355123 prefixEnd_355123 182348790466719313329325 := by
  unfold tailWord_355123
  simp only [CollatzResearch.WordTrace]
  refine ⟨12952399892457496024902023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8634933261638330683268015 12952399892457496024902023)
  ·
    refine ⟨19428599838686244037353035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12952399892457496024902023 19428599838686244037353035)
    ·
      refine ⟨29142899758029366056029553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19428599838686244037353035 29142899758029366056029553)
      ·
        refine ⟨21857174818522024542022165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29142899758029366056029553 21857174818522024542022165)
        ·
          refine ⟨1024555069618219900407289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21857174818522024542022165 1024555069618219900407289)
          ·
            refine ⟨768416302213664925305467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024555069618219900407289 768416302213664925305467)
            ·
              refine ⟨1152624453320497387958201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768416302213664925305467 1152624453320497387958201)
              ·
                refine ⟨864468339990373040968651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152624453320497387958201 864468339990373040968651)
                ·
                  refine ⟨1296702509985559561452977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864468339990373040968651 1296702509985559561452977)
                  ·
                    refine ⟨972526882489169671089733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1296702509985559561452977 972526882489169671089733)
                    ·
                      refine ⟨182348790466719313329325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 972526882489169671089733 182348790466719313329325)
                      ·
                        rfl

theorem cell23_355123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_355123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355123 prefixEnd_355123 := by exact prefixLift 355123
  have htrace : WordTrace (prefixWord ++ tailWord_355123) baseStart_355123 baseEnd_355123 := by
    simpa [prefixWord, tailWord_355123, baseEnd_355123] using wordTrace_append hprefix tailTrace_355123
  have hstable : (prefixWord ++ tailWord_355123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355123).length < 2 ^ (prefixWord ++ tailWord_355123).sum := by decide
  have hdescent : baseEnd_355123 < baseStart_355123 := by decide
  rcases family_descends (prefixWord ++ tailWord_355123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355127 : List Nat := [1, 1, 3, 1, 2, 1, 4, 5, 1, 2, 2]
def baseStart_355127 : Nat := 118140960795 + 355127 * 2 ^ 59
def prefixEnd_355127 : Nat := 4983230072969 + 3 ^ 40 * 355127 * 2
def baseEnd_355127 : Nat := 182350844389337297679307

theorem tailTrace_355127 : CollatzResearch.WordTrace tailWord_355127 prefixEnd_355127 182350844389337297679307 := by
  unfold tailWord_355127
  simp only [CollatzResearch.WordTrace]
  refine ⟨12952545784443004708047635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8635030522962003138698423 12952545784443004708047635)
  ·
    refine ⟨19428818676664507062071453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12952545784443004708047635 19428818676664507062071453)
    ·
      refine ⟨7285807003749190148276795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19428818676664507062071453 7285807003749190148276795)
      ·
        refine ⟨10928710505623785222415193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7285807003749190148276795 10928710505623785222415193)
        ·
          refine ⟨8196532879217838916811395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10928710505623785222415193 8196532879217838916811395)
          ·
            refine ⟨12294799318826758375217093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8196532879217838916811395 12294799318826758375217093)
            ·
              refine ⟨2305274872280017195353205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12294799318826758375217093 2305274872280017195353205)
              ·
                refine ⟨216119519276251612064363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2305274872280017195353205 216119519276251612064363)
                ·
                  refine ⟨324179278914377418096545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216119519276251612064363 324179278914377418096545)
                  ·
                    refine ⟨243134459185783063572409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 324179278914377418096545 243134459185783063572409)
                    ·
                      refine ⟨182350844389337297679307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243134459185783063572409 182350844389337297679307)
                      ·
                        rfl

theorem cell23_355127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 1, 2, 2].length) (baseStart_355127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355127 prefixEnd_355127 := by exact prefixLift 355127
  have htrace : WordTrace (prefixWord ++ tailWord_355127) baseStart_355127 baseEnd_355127 := by
    simpa [prefixWord, tailWord_355127, baseEnd_355127] using wordTrace_append hprefix tailTrace_355127
  have hstable : (prefixWord ++ tailWord_355127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355127).length < 2 ^ (prefixWord ++ tailWord_355127).sum := by decide
  have hdescent : baseEnd_355127 < baseStart_355127 := by decide
  rcases family_descends (prefixWord ++ tailWord_355127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355130 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5]
def baseStart_355130 : Nat := 118140960795 + 355130 * 2 ^ 59
def prefixEnd_355130 : Nat := 4983230072969 + 3 ^ 40 * 355130 * 2
def baseEnd_355130 : Nat := 182352384831300785941793

theorem tailTrace_355130 : CollatzResearch.WordTrace tailWord_355130 prefixEnd_355130 182352384831300785941793 := by
  unfold tailWord_355130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3238163800858034055101711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8635103468954757480271229 3238163800858034055101711)
  ·
    refine ⟨4857245701287051082652567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3238163800858034055101711 4857245701287051082652567)
    ·
      refine ⟨7285868551930576623978851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4857245701287051082652567 7285868551930576623978851)
      ·
        refine ⟨10928802827895864935968277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7285868551930576623978851 10928802827895864935968277)
        ·
          refine ⟨512287632557618668873513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10928802827895864935968277 512287632557618668873513)
          ·
            refine ⟨384215724418214001655135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512287632557618668873513 384215724418214001655135)
            ·
              refine ⟨576323586627321002482703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384215724418214001655135 576323586627321002482703)
              ·
                refine ⟨864485379940981503724055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576323586627321002482703 864485379940981503724055)
                ·
                  refine ⟨1296728069911472255586083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864485379940981503724055 1296728069911472255586083)
                  ·
                    refine ⟨1945092104867208383379125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1296728069911472255586083 1945092104867208383379125)
                    ·
                      refine ⟨182352384831300785941793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1945092104867208383379125 182352384831300785941793)
                      ·
                        rfl

theorem cell23_355130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_355130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355130 prefixEnd_355130 := by exact prefixLift 355130
  have htrace : WordTrace (prefixWord ++ tailWord_355130) baseStart_355130 baseEnd_355130 := by
    simpa [prefixWord, tailWord_355130, baseEnd_355130] using wordTrace_append hprefix tailTrace_355130
  have hstable : (prefixWord ++ tailWord_355130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355130).length < 2 ^ (prefixWord ++ tailWord_355130).sum := by decide
  have hdescent : baseEnd_355130 < baseStart_355130 := by decide
  rcases family_descends (prefixWord ++ tailWord_355130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355133 : List Nat := [1, 4, 1, 4, 3, 10]
def baseStart_355133 : Nat := 118140960795 + 355133 * 2 ^ 59
def prefixEnd_355133 : Nat := 4983230072969 + 3 ^ 40 * 355133 * 2
def baseEnd_355133 : Nat := 750427676021663679853

theorem tailTrace_355133 : CollatzResearch.WordTrace tailWord_355133 prefixEnd_355133 750427676021663679853 := by
  unfold tailWord_355133
  simp only [CollatzResearch.WordTrace]
  refine ⟨12952764622421267732766053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8635176414947511821844035 12952764622421267732766053)
  ·
    refine ⟨2428643366703987699893635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12952764622421267732766053 2428643366703987699893635)
    ·
      refine ⟨3642965050055981549840453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2428643366703987699893635 3642965050055981549840453)
      ·
        refine ⟨683055946885496540595085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3642965050055981549840453 683055946885496540595085)
        ·
          refine ⟨256145980082061202723157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 683055946885496540595085 256145980082061202723157)
          ·
            refine ⟨750427676021663679853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 256145980082061202723157 750427676021663679853)
            ·
              rfl

theorem cell23_355133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 10].length) (baseStart_355133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355133 prefixEnd_355133 := by exact prefixLift 355133
  have htrace : WordTrace (prefixWord ++ tailWord_355133) baseStart_355133 baseEnd_355133 := by
    simpa [prefixWord, tailWord_355133, baseEnd_355133] using wordTrace_append hprefix tailTrace_355133
  have hstable : (prefixWord ++ tailWord_355133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355133).length < 2 ^ (prefixWord ++ tailWord_355133).sum := by decide
  have hdescent : baseEnd_355133 < baseStart_355133 := by decide
  rcases family_descends (prefixWord ++ tailWord_355133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355187 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 1, 3, 2]
def baseStart_355187 : Nat := 118140960795 + 355187 * 2 ^ 59
def prefixEnd_355187 : Nat := 4983230072969 + 3 ^ 40 * 355187 * 2
def baseEnd_355187 : Nat := 182381653228607062929031

theorem tailTrace_355187 : CollatzResearch.WordTrace tailWord_355187 prefixEnd_355187 182381653228607062929031 := by
  unfold tailWord_355187
  simp only [CollatzResearch.WordTrace]
  refine ⟨12954734164225634955231815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8636489442817089970154543 12954734164225634955231815)
  ·
    refine ⟨19432101246338452432847723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12954734164225634955231815 19432101246338452432847723)
    ·
      refine ⟨29148151869507678649271585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19432101246338452432847723 29148151869507678649271585)
      ·
        refine ⟨21861113902130758986953689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29148151869507678649271585 21861113902130758986953689)
        ·
          refine ⟨16395835426598069240215267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21861113902130758986953689 16395835426598069240215267)
          ·
            refine ⟨24593753139897103860322901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16395835426598069240215267 24593753139897103860322901)
            ·
              refine ⟨288208044608169185863159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 24593753139897103860322901 288208044608169185863159)
              ·
                refine ⟨432312066912253778794739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288208044608169185863159 432312066912253778794739)
                ·
                  refine ⟨648468100368380668192109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432312066912253778794739 648468100368380668192109)
                  ·
                    refine ⟨243175537638142750572041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648468100368380668192109 243175537638142750572041)
                    ·
                      refine ⟨182381653228607062929031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243175537638142750572041 182381653228607062929031)
                      ·
                        rfl

theorem cell23_355187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 3, 2].length) (baseStart_355187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355187 prefixEnd_355187 := by exact prefixLift 355187
  have htrace : WordTrace (prefixWord ++ tailWord_355187) baseStart_355187 baseEnd_355187 := by
    simpa [prefixWord, tailWord_355187, baseEnd_355187] using wordTrace_append hprefix tailTrace_355187
  have hstable : (prefixWord ++ tailWord_355187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355187).length < 2 ^ (prefixWord ++ tailWord_355187).sum := by decide
  have hdescent : baseEnd_355187 < baseStart_355187 := by decide
  rcases family_descends (prefixWord ++ tailWord_355187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355257 : List Nat := [1, 2, 1, 4, 2, 3, 3, 2, 5]
def baseStart_355257 : Nat := 118140960795 + 355257 * 2 ^ 59
def prefixEnd_355257 : Nat := 4983230072969 + 3 ^ 40 * 355257 * 2
def baseEnd_355257 : Nat := 20268621874935754339301

theorem tailTrace_355257 : CollatzResearch.WordTrace tailWord_355257 prefixEnd_355257 20268621874935754339301 := by
  unfold tailWord_355257
  simp only [CollatzResearch.WordTrace]
  refine ⟨12957287273972036910280025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8638191515981357940186683 12957287273972036910280025)
  ·
    refine ⟨9717965455479027682710019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12957287273972036910280025 9717965455479027682710019)
    ·
      refine ⟨14576948183218541524065029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9717965455479027682710019 14576948183218541524065029)
      ·
        refine ⟨2733177784353476535762193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14576948183218541524065029 2733177784353476535762193)
        ·
          refine ⟨2049883338265107401821645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2733177784353476535762193 2049883338265107401821645)
          ·
            refine ⟨768706251849415275683117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2049883338265107401821645 768706251849415275683117)
            ·
              refine ⟨288264844443530728381169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 768706251849415275683117 288264844443530728381169)
              ·
                refine ⟨216198633332648046285877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288264844443530728381169 216198633332648046285877)
                ·
                  refine ⟨20268621874935754339301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 216198633332648046285877 20268621874935754339301)
                  ·
                    rfl

theorem cell23_355257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 5].length) (baseStart_355257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355257 prefixEnd_355257 := by exact prefixLift 355257
  have htrace : WordTrace (prefixWord ++ tailWord_355257) baseStart_355257 baseEnd_355257 := by
    simpa [prefixWord, tailWord_355257, baseEnd_355257] using wordTrace_append hprefix tailTrace_355257
  have hstable : (prefixWord ++ tailWord_355257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355257).length < 2 ^ (prefixWord ++ tailWord_355257).sum := by decide
  have hdescent : baseEnd_355257 < baseStart_355257 := by decide
  rcases family_descends (prefixWord ++ tailWord_355257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355290 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_355290 : Nat := 118140960795 + 355290 * 2 ^ 59
def prefixEnd_355290 : Nat := 4983230072969 + 3 ^ 40 * 355290 * 2
def baseEnd_355290 : Nat := 182434541736020159941057

theorem tailTrace_355290 : CollatzResearch.WordTrace tailWord_355290 prefixEnd_355290 182434541736020159941057 := by
  unfold tailWord_355290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3239622720713120886557831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8638993921901655697487549 3239622720713120886557831)
  ·
    refine ⟨4859434081069681329836747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3239622720713120886557831 4859434081069681329836747)
    ·
      refine ⟨7289151121604521994755121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4859434081069681329836747 7289151121604521994755121)
      ·
        refine ⟨5466863341203391496066341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7289151121604521994755121 5466863341203391496066341)
        ·
          refine ⟨1025036876475635905512439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5466863341203391496066341 1025036876475635905512439)
          ·
            refine ⟨1537555314713453858268659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025036876475635905512439 1537555314713453858268659)
            ·
              refine ⟨2306332972070180787402989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537555314713453858268659 2306332972070180787402989)
              ·
                refine ⟨864874864526317795276121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2306332972070180787402989 864874864526317795276121)
                ·
                  refine ⟨648656148394738346457091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 864874864526317795276121 648656148394738346457091)
                  ·
                    refine ⟨972984222592107519685637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 648656148394738346457091 972984222592107519685637)
                    ·
                      refine ⟨182434541736020159941057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 972984222592107519685637 182434541736020159941057)
                      ·
                        rfl

theorem cell23_355290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_355290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355290 prefixEnd_355290 := by exact prefixLift 355290
  have htrace : WordTrace (prefixWord ++ tailWord_355290) baseStart_355290 baseEnd_355290 := by
    simpa [prefixWord, tailWord_355290, baseEnd_355290] using wordTrace_append hprefix tailTrace_355290
  have hstable : (prefixWord ++ tailWord_355290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355290).length < 2 ^ (prefixWord ++ tailWord_355290).sum := by decide
  have hdescent : baseEnd_355290 < baseStart_355290 := by decide
  rcases family_descends (prefixWord ++ tailWord_355290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355323 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 3]
def baseStart_355323 : Nat := 118140960795 + 355323 * 2 ^ 59
def prefixEnd_355323 : Nat := 4983230072969 + 3 ^ 40 * 355323 * 2
def baseEnd_355323 : Nat := 182451486597618530828405

theorem tailTrace_355323 : CollatzResearch.WordTrace tailWord_355323 prefixEnd_355323 182451486597618530828405 := by
  unfold tailWord_355323
  simp only [CollatzResearch.WordTrace]
  refine ⟨12959694491732930182182623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8639796327821953454788415 12959694491732930182182623)
  ·
    refine ⟨19439541737599395273273935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12959694491732930182182623 19439541737599395273273935)
    ·
      refine ⟨29159312606399092909910903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19439541737599395273273935 29159312606399092909910903)
      ·
        refine ⟨43738968909598639364866355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29159312606399092909910903 43738968909598639364866355)
        ·
          refine ⟨65608453364397959047299533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43738968909598639364866355 65608453364397959047299533)
          ·
            refine ⟨24603170011649234642737325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65608453364397959047299533 24603170011649234642737325)
            ·
              refine ⟨9226188754368462991026497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24603170011649234642737325 9226188754368462991026497)
              ·
                refine ⟨6919641565776347243269873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9226188754368462991026497 6919641565776347243269873)
                ·
                  refine ⟨5189731174332260432452405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6919641565776347243269873 5189731174332260432452405)
                  ·
                    refine ⟨486537297593649415542413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5189731174332260432452405 486537297593649415542413)
                    ·
                      refine ⟨182451486597618530828405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 486537297593649415542413 182451486597618530828405)
                      ·
                        rfl

theorem cell23_355323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 3].length) (baseStart_355323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355323 prefixEnd_355323 := by exact prefixLift 355323
  have htrace : WordTrace (prefixWord ++ tailWord_355323) baseStart_355323 baseEnd_355323 := by
    simpa [prefixWord, tailWord_355323, baseEnd_355323] using wordTrace_append hprefix tailTrace_355323
  have hstable : (prefixWord ++ tailWord_355323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355323).length < 2 ^ (prefixWord ++ tailWord_355323).sum := by decide
  have hdescent : baseEnd_355323 < baseStart_355323 := by decide
  rcases family_descends (prefixWord ++ tailWord_355323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355374 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_355374 : Nat := 118140960795 + 355374 * 2 ^ 59
def prefixEnd_355374 : Nat := 4983230072969 + 3 ^ 40 * 355374 * 2
def baseEnd_355374 : Nat := 182477674110997831290671

theorem tailTrace_355374 : CollatzResearch.WordTrace tailWord_355374 prefixEnd_355374 182477674110997831290671 := by
  unfold tailWord_355374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1620194326818520736536147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8641036409698777261526117 1620194326818520736536147)
  ·
    refine ⟨2430291490227781104804221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1620194326818520736536147 2430291490227781104804221)
    ·
      refine ⟨911359308835417914301583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2430291490227781104804221 911359308835417914301583)
      ·
        refine ⟨1367038963253126871452375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911359308835417914301583 1367038963253126871452375)
        ·
          refine ⟨2050558444879690307178563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367038963253126871452375 2050558444879690307178563)
          ·
            refine ⟨3075837667319535460767845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2050558444879690307178563 3075837667319535460767845)
            ·
              refine ⟨576719562622412898893971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3075837667319535460767845 576719562622412898893971)
              ·
                refine ⟨865079343933619348340957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576719562622412898893971 865079343933619348340957)
                ·
                  refine ⟨324404753975107255627859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865079343933619348340957 324404753975107255627859)
                  ·
                    refine ⟨486607130962660883441789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 324404753975107255627859 486607130962660883441789)
                    ·
                      refine ⟨182477674110997831290671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 486607130962660883441789 182477674110997831290671)
                      ·
                        rfl

theorem cell23_355374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_355374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355374 prefixEnd_355374 := by exact prefixLift 355374
  have htrace : WordTrace (prefixWord ++ tailWord_355374) baseStart_355374 baseEnd_355374 := by
    simpa [prefixWord, tailWord_355374, baseEnd_355374] using wordTrace_append hprefix tailTrace_355374
  have hstable : (prefixWord ++ tailWord_355374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355374).length < 2 ^ (prefixWord ++ tailWord_355374).sum := by decide
  have hdescent : baseEnd_355374 < baseStart_355374 := by decide
  rcases family_descends (prefixWord ++ tailWord_355374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355431 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_355431 : Nat := 118140960795 + 355431 * 2 ^ 59
def prefixEnd_355431 : Nat := 4983230072969 + 3 ^ 40 * 355431 * 2
def baseEnd_355431 : Nat := 182506942508304108277909

theorem tailTrace_355431 : CollatzResearch.WordTrace tailWord_355431 prefixEnd_355431 182506942508304108277909 := by
  unfold tailWord_355431
  simp only [CollatzResearch.WordTrace]
  refine ⟨12963633575341664627114147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8642422383561109751409431 12963633575341664627114147)
  ·
    refine ⟨19445450363012496940671221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12963633575341664627114147 19445450363012496940671221)
    ·
      refine ⟨1823010971532421588187927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19445450363012496940671221 1823010971532421588187927)
      ·
        refine ⟨2734516457298632382281891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1823010971532421588187927 2734516457298632382281891)
        ·
          refine ⟨4101774685947948573422837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734516457298632382281891 4101774685947948573422837)
          ·
            refine ⟨384541376807620178758391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4101774685947948573422837 384541376807620178758391)
            ·
              refine ⟨576812065211430268137587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384541376807620178758391 576812065211430268137587)
              ·
                refine ⟨865218097817145402206381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576812065211430268137587 865218097817145402206381)
                ·
                  refine ⟨324456786681429525827393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865218097817145402206381 324456786681429525827393)
                  ·
                    refine ⟨243342590011072144370545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 324456786681429525827393 243342590011072144370545)
                    ·
                      refine ⟨182506942508304108277909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243342590011072144370545 182506942508304108277909)
                      ·
                        rfl

theorem cell23_355431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_355431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355431 prefixEnd_355431 := by exact prefixLift 355431
  have htrace : WordTrace (prefixWord ++ tailWord_355431) baseStart_355431 baseEnd_355431 := by
    simpa [prefixWord, tailWord_355431, baseEnd_355431] using wordTrace_append hprefix tailTrace_355431
  have hstable : (prefixWord ++ tailWord_355431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355431).length < 2 ^ (prefixWord ++ tailWord_355431).sum := by decide
  have hdescent : baseEnd_355431 < baseStart_355431 := by decide
  rcases family_descends (prefixWord ++ tailWord_355431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355464 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_355464 : Nat := 118140960795 + 355464 * 2 ^ 59
def prefixEnd_355464 : Nat := 4983230072969 + 3 ^ 40 * 355464 * 2
def baseEnd_355464 : Nat := 182523887369902479165257

theorem tailTrace_355464 : CollatzResearch.WordTrace tailWord_355464 prefixEnd_355464 182523887369902479165257 := by
  unfold tailWord_355464
  simp only [CollatzResearch.WordTrace]
  refine ⟨6482418592111055631532723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8643224789481407508710297 6482418592111055631532723)
  ·
    refine ⟨9723627888166583447299085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6482418592111055631532723 9723627888166583447299085)
    ·
      refine ⟨3646360458062468792737157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9723627888166583447299085 3646360458062468792737157)
      ·
        refine ⟨683692585886712898638217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3646360458062468792737157 683692585886712898638217)
        ·
          refine ⟨512769439415034673978663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683692585886712898638217 512769439415034673978663)
          ·
            refine ⟨769154159122552010967995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512769439415034673978663 769154159122552010967995)
            ·
              refine ⟨1153731238683828016451993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769154159122552010967995 1153731238683828016451993)
              ·
                refine ⟨865298429012871012338995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153731238683828016451993 865298429012871012338995)
                ·
                  refine ⟨1297947643519306518508493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865298429012871012338995 1297947643519306518508493)
                  ·
                    refine ⟨486730366319739944440685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1297947643519306518508493 486730366319739944440685)
                    ·
                      refine ⟨182523887369902479165257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 486730366319739944440685 182523887369902479165257)
                      ·
                        rfl

theorem cell23_355464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_355464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355464 prefixEnd_355464 := by exact prefixLift 355464
  have htrace : WordTrace (prefixWord ++ tailWord_355464) baseStart_355464 baseEnd_355464 := by
    simpa [prefixWord, tailWord_355464, baseEnd_355464] using wordTrace_append hprefix tailTrace_355464
  have hstable : (prefixWord ++ tailWord_355464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355464).length < 2 ^ (prefixWord ++ tailWord_355464).sum := by decide
  have hdescent : baseEnd_355464 < baseStart_355464 := by decide
  rcases family_descends (prefixWord ++ tailWord_355464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355521 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_355521 : Nat := 118140960795 + 355521 * 2 ^ 59
def prefixEnd_355521 : Nat := 4983230072969 + 3 ^ 40 * 355521 * 2
def baseEnd_355521 : Nat := 182553155767208756152495

theorem tailTrace_355521 : CollatzResearch.WordTrace tailWord_355521 prefixEnd_355521 182553155767208756152495 := by
  unfold tailWord_355521
  simp only [CollatzResearch.WordTrace]
  refine ⟨12966916145015609997890417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8644610763343739998593611 12966916145015609997890417)
  ·
    refine ⟨9725187108761707498417813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12966916145015609997890417 9725187108761707498417813)
    ·
      refine ⟨455868145723205038988335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9725187108761707498417813 455868145723205038988335)
      ·
        refine ⟨683802218584807558482503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455868145723205038988335 683802218584807558482503)
        ·
          refine ⟨1025703327877211337723755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683802218584807558482503 1025703327877211337723755)
          ·
            refine ⟨1538554991815817006585633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025703327877211337723755 1538554991815817006585633)
            ·
              refine ⟨1153916243861862754939225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538554991815817006585633 1153916243861862754939225)
              ·
                refine ⟨865437182896397066204419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153916243861862754939225 865437182896397066204419)
                ·
                  refine ⟨1298155774344595599306629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865437182896397066204419 1298155774344595599306629)
                  ·
                    refine ⟨243404207689611674869993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1298155774344595599306629 243404207689611674869993)
                    ·
                      refine ⟨182553155767208756152495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243404207689611674869993 182553155767208756152495)
                      ·
                        rfl

theorem cell23_355521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_355521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355521 prefixEnd_355521 := by exact prefixLift 355521
  have htrace : WordTrace (prefixWord ++ tailWord_355521) baseStart_355521 baseEnd_355521 := by
    simpa [prefixWord, tailWord_355521, baseEnd_355521] using wordTrace_append hprefix tailTrace_355521
  have hstable : (prefixWord ++ tailWord_355521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355521).length < 2 ^ (prefixWord ++ tailWord_355521).sum := by decide
  have hdescent : baseEnd_355521 < baseStart_355521 := by decide
  rcases family_descends (prefixWord ++ tailWord_355521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355577 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 4]
def baseStart_355577 : Nat := 118140960795 + 355577 * 2 ^ 59
def prefixEnd_355577 : Nat := 4983230072969 + 3 ^ 40 * 355577 * 2
def baseEnd_355577 : Nat := 182581910683860537052237

theorem tailTrace_355577 : CollatzResearch.WordTrace tailWord_355577 prefixEnd_355577 182581910683860537052237 := by
  unfold tailWord_355577
  simp only [CollatzResearch.WordTrace]
  refine ⟨12968958632812731561928985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8645972421875154374619323 12968958632812731561928985)
  ·
    refine ⟨9726718974609548671446739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12968958632812731561928985 9726718974609548671446739)
    ·
      refine ⟨14590078461914323007170109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9726718974609548671446739 14590078461914323007170109)
      ·
        refine ⟨5471279423217871127688791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14590078461914323007170109 5471279423217871127688791)
        ·
          refine ⟨8206919134826806691533187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5471279423217871127688791 8206919134826806691533187)
          ·
            refine ⟨12310378702240210037299781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8206919134826806691533187 12310378702240210037299781)
            ·
              refine ⟨2308196006670039381993709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12310378702240210037299781 2308196006670039381993709)
              ·
                refine ⟨865573502501264768247641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2308196006670039381993709 865573502501264768247641)
                ·
                  refine ⟨649180126875948576185731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 865573502501264768247641 649180126875948576185731)
                  ·
                    refine ⟨973770190313922864278597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 649180126875948576185731 973770190313922864278597)
                    ·
                      refine ⟨182581910683860537052237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 973770190313922864278597 182581910683860537052237)
                      ·
                        rfl

theorem cell23_355577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_355577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355577 prefixEnd_355577 := by exact prefixLift 355577
  have htrace : WordTrace (prefixWord ++ tailWord_355577) baseStart_355577 baseEnd_355577 := by
    simpa [prefixWord, tailWord_355577, baseEnd_355577] using wordTrace_append hprefix tailTrace_355577
  have hstable : (prefixWord ++ tailWord_355577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355577).length < 2 ^ (prefixWord ++ tailWord_355577).sum := by decide
  have hdescent : baseEnd_355577 < baseStart_355577 := by decide
  rcases family_descends (prefixWord ++ tailWord_355577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355667 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 4]
def baseStart_355667 : Nat := 118140960795 + 355667 * 2 ^ 59
def prefixEnd_355667 : Nat := 4983230072969 + 3 ^ 40 * 355667 * 2
def baseEnd_355667 : Nat := 182628123942765184926823

theorem tailTrace_355667 : CollatzResearch.WordTrace tailWord_355667 prefixEnd_355667 182628123942765184926823 := by
  unfold tailWord_355667
  simp only [CollatzResearch.WordTrace]
  refine ⟨12972241202486676932705255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8648160801657784621803503 12972241202486676932705255)
  ·
    refine ⟨19458361803730015399057883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12972241202486676932705255 19458361803730015399057883)
    ·
      refine ⟨29187542705595023098586825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19458361803730015399057883 29187542705595023098586825)
      ·
        refine ⟨21890657029196267323940119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29187542705595023098586825 21890657029196267323940119)
        ·
          refine ⟨32835985543794400985910179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21890657029196267323940119 32835985543794400985910179)
          ·
            refine ⟨49253978315691601478865269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32835985543794400985910179 49253978315691601478865269)
            ·
              refine ⟨4617560467096087638643619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49253978315691601478865269 4617560467096087638643619)
              ·
                refine ⟨6926340700644131457965429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617560467096087638643619 6926340700644131457965429)
                ·
                  refine ⟨649344440685387324184259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6926340700644131457965429 649344440685387324184259)
                  ·
                    refine ⟨974016661028080986276389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 649344440685387324184259 974016661028080986276389)
                    ·
                      refine ⟨182628123942765184926823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 974016661028080986276389 182628123942765184926823)
                      ·
                        rfl

theorem cell23_355667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_355667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355667 prefixEnd_355667 := by exact prefixLift 355667
  have htrace : WordTrace (prefixWord ++ tailWord_355667) baseStart_355667 baseEnd_355667 := by
    simpa [prefixWord, tailWord_355667, baseEnd_355667] using wordTrace_append hprefix tailTrace_355667
  have hstable : (prefixWord ++ tailWord_355667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355667).length < 2 ^ (prefixWord ++ tailWord_355667).sum := by decide
  have hdescent : baseEnd_355667 < baseStart_355667 := by decide
  rcases family_descends (prefixWord ++ tailWord_355667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355684 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_355684 : Nat := 118140960795 + 355684 * 2 ^ 59
def prefixEnd_355684 : Nat := 4983230072969 + 3 ^ 40 * 355684 * 2
def baseEnd_355684 : Nat := 182636853113891618414245

theorem tailTrace_355684 : CollatzResearch.WordTrace tailWord_355684 prefixEnd_355684 182636853113891618414245 := by
  unfold tailWord_355684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6486430621712544418037053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8648574162283392557382737 6486430621712544418037053)
  ·
    refine ⟨2432411483142204156763895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6486430621712544418037053 2432411483142204156763895)
    ·
      refine ⟨3648617224713306235145843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2432411483142204156763895 3648617224713306235145843)
      ·
        refine ⟨5472925837069959352718765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3648617224713306235145843 5472925837069959352718765)
        ·
          refine ⟨2052347188901234757269537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5472925837069959352718765 2052347188901234757269537)
          ·
            refine ⟨1539260391675926067952153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2052347188901234757269537 1539260391675926067952153)
            ·
              refine ⟨1154445293756944550964115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539260391675926067952153 1154445293756944550964115)
              ·
                refine ⟨1731667940635416826446173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154445293756944550964115 1731667940635416826446173)
                ·
                  refine ⟨649375477738281309917315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1731667940635416826446173 649375477738281309917315)
                  ·
                    refine ⟨974063216607421964875973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 649375477738281309917315 974063216607421964875973)
                    ·
                      refine ⟨182636853113891618414245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 974063216607421964875973 182636853113891618414245)
                      ·
                        rfl

theorem cell23_355684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_355684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355684 prefixEnd_355684 := by exact prefixLift 355684
  have htrace : WordTrace (prefixWord ++ tailWord_355684) baseStart_355684 baseEnd_355684 := by
    simpa [prefixWord, tailWord_355684, baseEnd_355684] using wordTrace_append hprefix tailTrace_355684
  have hstable : (prefixWord ++ tailWord_355684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355684).length < 2 ^ (prefixWord ++ tailWord_355684).sum := by decide
  have hdescent : baseEnd_355684 < baseStart_355684 := by decide
  rcases family_descends (prefixWord ++ tailWord_355684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355741 : List Nat := [1, 4, 2, 1, 3, 3, 2, 7]
def baseStart_355741 : Nat := 118140960795 + 355741 * 2 ^ 59
def prefixEnd_355741 : Nat := 4983230072969 + 3 ^ 40 * 355741 * 2
def baseEnd_355741 : Nat := 6765411907822144274129

theorem tailTrace_355741 : CollatzResearch.WordTrace tailWord_355741 prefixEnd_355741 6765411907822144274129 := by
  unfold tailWord_355741
  simp only [CollatzResearch.WordTrace]
  refine ⟨12974940204218587570899077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8649960136145725047266051 12974940204218587570899077)
  ·
    refine ⟨2432801288290985169543577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12974940204218587570899077 2432801288290985169543577)
    ·
      refine ⟨1824600966218238877157683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2432801288290985169543577 1824600966218238877157683)
      ·
        refine ⟨2736901449327358315736525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824600966218238877157683 2736901449327358315736525)
        ·
          refine ⟨1026338043497759368401197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2736901449327358315736525 1026338043497759368401197)
          ·
            refine ⟨384876766311659763150449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1026338043497759368401197 384876766311659763150449)
            ·
              refine ⟨288657574733744822362837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384876766311659763150449 288657574733744822362837)
              ·
                refine ⟨6765411907822144274129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 288657574733744822362837 6765411907822144274129)
                ·
                  rfl

theorem cell23_355741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 7].length) (baseStart_355741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355741 prefixEnd_355741 := by exact prefixLift 355741
  have htrace : WordTrace (prefixWord ++ tailWord_355741) baseStart_355741 baseEnd_355741 := by
    simpa [prefixWord, tailWord_355741, baseEnd_355741] using wordTrace_append hprefix tailTrace_355741
  have hstable : (prefixWord ++ tailWord_355741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355741).length < 2 ^ (prefixWord ++ tailWord_355741).sum := by decide
  have hdescent : baseEnd_355741 < baseStart_355741 := by decide
  rcases family_descends (prefixWord ++ tailWord_355741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355747 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 5]
def baseStart_355747 : Nat := 118140960795 + 355747 * 2 ^ 59
def prefixEnd_355747 : Nat := 4983230072969 + 3 ^ 40 * 355747 * 2
def baseEnd_355747 : Nat := 182669202395124871926455

theorem tailTrace_355747 : CollatzResearch.WordTrace tailWord_355747 prefixEnd_355747 182669202395124871926455 := by
  unfold tailWord_355747
  simp only [CollatzResearch.WordTrace]
  refine ⟨12975159042196850595617495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8650106028131233730411663 12975159042196850595617495)
  ·
    refine ⟨19462738563295275893426243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12975159042196850595617495 19462738563295275893426243)
    ·
      refine ⟨29194107844942913840139365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19462738563295275893426243 29194107844942913840139365)
      ·
        refine ⟨5473895220926796345026131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29194107844942913840139365 5473895220926796345026131)
        ·
          refine ⟨8210842831390194517539197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5473895220926796345026131 8210842831390194517539197)
          ·
            refine ⟨3079066061771322944077199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8210842831390194517539197 3079066061771322944077199)
            ·
              refine ⟨4618599092656984416115799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079066061771322944077199 4618599092656984416115799)
              ·
                refine ⟨6927898638985476624173699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618599092656984416115799 6927898638985476624173699)
                ·
                  refine ⟨10391847958478214936260549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6927898638985476624173699 10391847958478214936260549)
                  ·
                    refine ⟨1948471492214665300548853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10391847958478214936260549 1948471492214665300548853)
                    ·
                      refine ⟨182669202395124871926455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1948471492214665300548853 182669202395124871926455)
                      ·
                        rfl

theorem cell23_355747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_355747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355747 prefixEnd_355747 := by exact prefixLift 355747
  have htrace : WordTrace (prefixWord ++ tailWord_355747) baseStart_355747 baseEnd_355747 := by
    simpa [prefixWord, tailWord_355747, baseEnd_355747] using wordTrace_append hprefix tailTrace_355747
  have hstable : (prefixWord ++ tailWord_355747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355747).length < 2 ^ (prefixWord ++ tailWord_355747).sum := by decide
  have hdescent : baseEnd_355747 < baseStart_355747 := by decide
  rcases family_descends (prefixWord ++ tailWord_355747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355751 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_355751 : Nat := 118140960795 + 355751 * 2 ^ 59
def prefixEnd_355751 : Nat := 4983230072969 + 3 ^ 40 * 355751 * 2
def baseEnd_355751 : Nat := 182671256317742856276437

theorem tailTrace_355751 : CollatzResearch.WordTrace tailWord_355751 prefixEnd_355751 182671256317742856276437 := by
  unfold tailWord_355751
  simp only [CollatzResearch.WordTrace]
  refine ⟨12975304934182359278763107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8650203289454906185842071 12975304934182359278763107)
  ·
    refine ⟨19462957401273538918144661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12975304934182359278763107 19462957401273538918144661)
    ·
      refine ⟨912326128184697136788031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19462957401273538918144661 912326128184697136788031)
      ·
        refine ⟨1368489192277045705182047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 912326128184697136788031 1368489192277045705182047)
        ·
          refine ⟨2052733788415568557773071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368489192277045705182047 2052733788415568557773071)
          ·
            refine ⟨3079100682623352836659607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2052733788415568557773071 3079100682623352836659607)
            ·
              refine ⟨4618651023935029254989411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079100682623352836659607 4618651023935029254989411)
              ·
                refine ⟨6927976535902543882484117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618651023935029254989411 6927976535902543882484117)
                ·
                  refine ⟨324748900120431744491443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6927976535902543882484117 324748900120431744491443)
                  ·
                    refine ⟨487123350180647616737165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 324748900120431744491443 487123350180647616737165)
                    ·
                      refine ⟨182671256317742856276437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 487123350180647616737165 182671256317742856276437)
                      ·
                        rfl

theorem cell23_355751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_355751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355751 prefixEnd_355751 := by exact prefixLift 355751
  have htrace : WordTrace (prefixWord ++ tailWord_355751) baseStart_355751 baseEnd_355751 := by
    simpa [prefixWord, tailWord_355751, baseEnd_355751] using wordTrace_append hprefix tailTrace_355751
  have hstable : (prefixWord ++ tailWord_355751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355751).length < 2 ^ (prefixWord ++ tailWord_355751).sum := by decide
  have hdescent : baseEnd_355751 < baseStart_355751 := by decide
  rcases family_descends (prefixWord ++ tailWord_355751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355774 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_355774 : Nat := 118140960795 + 355774 * 2 ^ 59
def prefixEnd_355774 : Nat := 4983230072969 + 3 ^ 40 * 355774 * 2
def baseEnd_355774 : Nat := 182683066372796266288831

theorem tailTrace_355774 : CollatzResearch.WordTrace tailWord_355774 prefixEnd_355774 182683066372796266288831 := by
  unfold tailWord_355774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1622017976637379275856297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8650762542066022804566917 1622017976637379275856297)
  ·
    refine ⟨1216513482478034456892223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1622017976637379275856297 1216513482478034456892223)
    ·
      refine ⟨1824770223717051685338335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216513482478034456892223 1824770223717051685338335)
      ·
        refine ⟨2737155335575577528007503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824770223717051685338335 2737155335575577528007503)
        ·
          refine ⟨4105733003363366292011255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737155335575577528007503 4105733003363366292011255)
          ·
            refine ⟨6158599505045049438016883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105733003363366292011255 6158599505045049438016883)
            ·
              refine ⟨9237899257567574157025325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6158599505045049438016883 9237899257567574157025325)
              ·
                refine ⟨3464212221587840308884497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9237899257567574157025325 3464212221587840308884497)
                ·
                  refine ⟨2598159166190880231663373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3464212221587840308884497 2598159166190880231663373)
                  ·
                    refine ⟨974309687321580086873765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598159166190880231663373 974309687321580086873765)
                    ·
                      refine ⟨182683066372796266288831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 974309687321580086873765 182683066372796266288831)
                      ·
                        rfl

theorem cell23_355774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_355774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355774 prefixEnd_355774 := by exact prefixLift 355774
  have htrace : WordTrace (prefixWord ++ tailWord_355774) baseStart_355774 baseEnd_355774 := by
    simpa [prefixWord, tailWord_355774, baseEnd_355774] using wordTrace_append hprefix tailTrace_355774
  have hstable : (prefixWord ++ tailWord_355774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355774).length < 2 ^ (prefixWord ++ tailWord_355774).sum := by decide
  have hdescent : baseEnd_355774 < baseStart_355774 := by decide
  rcases family_descends (prefixWord ++ tailWord_355774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355817 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_355817 : Nat := 118140960795 + 355817 * 2 ^ 59
def prefixEnd_355817 : Nat := 4983230072969 + 3 ^ 40 * 355817 * 2
def baseEnd_355817 : Nat := 182705146040939598051133

theorem tailTrace_355817 : CollatzResearch.WordTrace tailWord_355817 prefixEnd_355817 182705146040939598051133 := by
  unfold tailWord_355817
  simp only [CollatzResearch.WordTrace]
  refine ⟨12977712151943252550665705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8651808101295501700443803 12977712151943252550665705)
  ·
    refine ⟨9733284113957439412999279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12977712151943252550665705 9733284113957439412999279)
    ·
      refine ⟨14599926170936159119498919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9733284113957439412999279 14599926170936159119498919)
      ·
        refine ⟨21899889256404238679248379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14599926170936159119498919 21899889256404238679248379)
        ·
          refine ⟨32849833884606358018872569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21899889256404238679248379 32849833884606358018872569)
          ·
            refine ⟨24637375413454768514154427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32849833884606358018872569 24637375413454768514154427)
            ·
              refine ⟨36956063120182152771231641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24637375413454768514154427 36956063120182152771231641)
              ·
                refine ⟨27717047340136614578423731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36956063120182152771231641 27717047340136614578423731)
                ·
                  refine ⟨41575571010204921867635597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27717047340136614578423731 41575571010204921867635597)
                  ·
                    refine ⟨15590839128826845700363349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41575571010204921867635597 15590839128826845700363349)
                    ·
                      refine ⟨182705146040939598051133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 15590839128826845700363349 182705146040939598051133)
                      ·
                        rfl

theorem cell23_355817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_355817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355817 prefixEnd_355817 := by exact prefixLift 355817
  have htrace : WordTrace (prefixWord ++ tailWord_355817) baseStart_355817 baseEnd_355817 := by
    simpa [prefixWord, tailWord_355817, baseEnd_355817] using wordTrace_append hprefix tailTrace_355817
  have hstable : (prefixWord ++ tailWord_355817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355817).length < 2 ^ (prefixWord ++ tailWord_355817).sum := by decide
  have hdescent : baseEnd_355817 < baseStart_355817 := by decide
  rcases family_descends (prefixWord ++ tailWord_355817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355825 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 2, 2, 2]
def baseStart_355825 : Nat := 118140960795 + 355825 * 2 ^ 59
def prefixEnd_355825 : Nat := 4983230072969 + 3 ^ 40 * 355825 * 2
def baseEnd_355825 : Nat := 182709253886175566751097

theorem tailTrace_355825 : CollatzResearch.WordTrace tailWord_355825 prefixEnd_355825 182709253886175566751097 := by
  unfold tailWord_355825
  simp only [CollatzResearch.WordTrace]
  refine ⟨12978003935914269916956929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8652002623942846611304619 12978003935914269916956929)
  ·
    refine ⟨9733502951935702437717697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12978003935914269916956929 9733502951935702437717697)
    ·
      refine ⟨7300127213951776828288273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9733502951935702437717697 7300127213951776828288273)
      ·
        refine ⟨5475095410463832621216205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7300127213951776828288273 5475095410463832621216205)
        ·
          refine ⟨2053160778923937232956077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5475095410463832621216205 2053160778923937232956077)
          ·
            refine ⟨769935292096476462358529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2053160778923937232956077 769935292096476462358529)
            ·
              refine ⟨577451469072357346768897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769935292096476462358529 577451469072357346768897)
              ·
                refine ⟨433088601804268010076673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577451469072357346768897 433088601804268010076673)
                ·
                  refine ⟨324816451353201007557505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433088601804268010076673 324816451353201007557505)
                  ·
                    refine ⟨243612338514900755668129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 324816451353201007557505 243612338514900755668129)
                    ·
                      refine ⟨182709253886175566751097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243612338514900755668129 182709253886175566751097)
                      ·
                        rfl

theorem cell23_355825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_355825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355825 prefixEnd_355825 := by exact prefixLift 355825
  have htrace : WordTrace (prefixWord ++ tailWord_355825) baseStart_355825 baseEnd_355825 := by
    simpa [prefixWord, tailWord_355825, baseEnd_355825] using wordTrace_append hprefix tailTrace_355825
  have hstable : (prefixWord ++ tailWord_355825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355825).length < 2 ^ (prefixWord ++ tailWord_355825).sum := by decide
  have hdescent : baseEnd_355825 < baseStart_355825 := by decide
  rcases family_descends (prefixWord ++ tailWord_355825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355842 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_355842 : Nat := 118140960795 + 355842 * 2 ^ 59
def prefixEnd_355842 : Nat := 4983230072969 + 3 ^ 40 * 355842 * 2
def baseEnd_355842 : Nat := 182717983057302000238519

theorem tailTrace_355842 : CollatzResearch.WordTrace tailWord_355842 prefixEnd_355842 182717983057302000238519 := by
  unfold tailWord_355842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244655994213170455081445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8652415984568454546883853 3244655994213170455081445)
  ·
    refine ⟨608372998914969460327771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3244655994213170455081445 608372998914969460327771)
    ·
      refine ⟨912559498372454190491657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 608372998914969460327771 912559498372454190491657)
      ·
        refine ⟨684419623779340642868743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912559498372454190491657 684419623779340642868743)
        ·
          refine ⟨1026629435669010964303115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684419623779340642868743 1026629435669010964303115)
          ·
            refine ⟨1539944153503516446454673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026629435669010964303115 1539944153503516446454673)
            ·
              refine ⟨1154958115127637334841005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539944153503516446454673 1154958115127637334841005)
              ·
                refine ⟨433109293172864000565377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1154958115127637334841005 433109293172864000565377)
                ·
                  refine ⟨324831969879648000424033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433109293172864000565377 324831969879648000424033)
                  ·
                    refine ⟨243623977409736000318025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 324831969879648000424033 243623977409736000318025)
                    ·
                      refine ⟨182717983057302000238519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243623977409736000318025 182717983057302000238519)
                      ·
                        rfl

theorem cell23_355842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_355842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355842 prefixEnd_355842 := by exact prefixLift 355842
  have htrace : WordTrace (prefixWord ++ tailWord_355842) baseStart_355842 baseEnd_355842 := by
    simpa [prefixWord, tailWord_355842, baseEnd_355842] using wordTrace_append hprefix tailTrace_355842
  have hstable : (prefixWord ++ tailWord_355842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355842).length < 2 ^ (prefixWord ++ tailWord_355842).sum := by decide
  have hdescent : baseEnd_355842 < baseStart_355842 := by decide
  rcases family_descends (prefixWord ++ tailWord_355842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355861 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_355861 : Nat := 118140960795 + 355861 * 2 ^ 59
def prefixEnd_355861 : Nat := 4983230072969 + 3 ^ 40 * 355861 * 2
def baseEnd_355861 : Nat := 60909246396579141966977

theorem tailTrace_355861 : CollatzResearch.WordTrace tailWord_355861 prefixEnd_355861 60909246396579141966977 := by
  unfold tailWord_355861
  simp only [CollatzResearch.WordTrace]
  refine ⟨12979316963783848065267437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8652877975855898710178291 12979316963783848065267437)
  ·
    refine ⟨4867243861418943024475289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12979316963783848065267437 4867243861418943024475289)
    ·
      refine ⟨3650432896064207268356467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4867243861418943024475289 3650432896064207268356467)
      ·
        refine ⟨5475649344096310902534701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3650432896064207268356467 5475649344096310902534701)
        ·
          refine ⟨2053368504036116588450513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5475649344096310902534701 2053368504036116588450513)
          ·
            refine ⟨1540026378027087441337885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2053368504036116588450513 1540026378027087441337885)
            ·
              refine ⟨577509891760157790501707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1540026378027087441337885 577509891760157790501707)
              ·
                refine ⟨866264837640236685752561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577509891760157790501707 866264837640236685752561)
                ·
                  refine ⟨649698628230177514314421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 866264837640236685752561 649698628230177514314421)
                  ·
                    refine ⟨60909246396579141966977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 649698628230177514314421 60909246396579141966977)
                    ·
                      rfl

theorem cell23_355861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_355861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355861 prefixEnd_355861 := by exact prefixLift 355861
  have htrace : WordTrace (prefixWord ++ tailWord_355861) baseStart_355861 baseEnd_355861 := by
    simpa [prefixWord, tailWord_355861, baseEnd_355861] using wordTrace_append hprefix tailTrace_355861
  have hstable : (prefixWord ++ tailWord_355861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355861).length < 2 ^ (prefixWord ++ tailWord_355861).sum := by decide
  have hdescent : baseEnd_355861 < baseStart_355861 := by decide
  rcases family_descends (prefixWord ++ tailWord_355861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355891 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 3, 4]
def baseStart_355891 : Nat := 118140960795 + 355891 * 2 ^ 59
def prefixEnd_355891 : Nat := 4983230072969 + 3 ^ 40 * 355891 * 2
def baseEnd_355891 : Nat := 60914381203124102841931

theorem tailTrace_355891 : CollatzResearch.WordTrace tailWord_355891 prefixEnd_355891 60914381203124102841931 := by
  unfold tailWord_355891
  simp only [CollatzResearch.WordTrace]
  refine ⟨12980411153675163188859527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8653607435783442125906351 12980411153675163188859527)
  ·
    refine ⟨19470616730512744783289291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12980411153675163188859527 19470616730512744783289291)
    ·
      refine ⟨29205925095769117174933937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19470616730512744783289291 29205925095769117174933937)
      ·
        refine ⟨21904443821826837881200453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29205925095769117174933937 21904443821826837881200453)
        ·
          refine ⟨4107083216592532102725085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21904443821826837881200453 4107083216592532102725085)
          ·
            refine ⟨1540156206222199538521907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4107083216592532102725085 1540156206222199538521907)
            ·
              refine ⟨2310234309333299307782861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540156206222199538521907 2310234309333299307782861)
              ·
                refine ⟨866337865999987240418573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2310234309333299307782861 866337865999987240418573)
                ·
                  refine ⟨324876699749995215156965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 866337865999987240418573 324876699749995215156965)
                  ·
                    refine ⟨60914381203124102841931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 324876699749995215156965 60914381203124102841931)
                    ·
                      rfl

theorem cell23_355891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 4].length) (baseStart_355891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355891 prefixEnd_355891 := by exact prefixLift 355891
  have htrace : WordTrace (prefixWord ++ tailWord_355891) baseStart_355891 baseEnd_355891 := by
    simpa [prefixWord, tailWord_355891, baseEnd_355891] using wordTrace_append hprefix tailTrace_355891
  have hstable : (prefixWord ++ tailWord_355891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355891).length < 2 ^ (prefixWord ++ tailWord_355891).sum := by decide
  have hdescent : baseEnd_355891 < baseStart_355891 := by decide
  rcases family_descends (prefixWord ++ tailWord_355891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355975 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 2, 3, 2]
def baseStart_355975 : Nat := 118140960795 + 355975 * 2 ^ 59
def prefixEnd_355975 : Nat := 4983230072969 + 3 ^ 40 * 355975 * 2
def baseEnd_355975 : Nat := 182786275984349979875407

theorem tailTrace_355975 : CollatzResearch.WordTrace tailWord_355975 prefixEnd_355975 182786275984349979875407 := by
  unfold tailWord_355975
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983474885370845534917379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8655649923580563689944919 12983474885370845534917379)
  ·
    refine ⟨19475212328056268302376069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12983474885370845534917379 19475212328056268302376069)
    ·
      refine ⟨3651602311510550306695513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19475212328056268302376069 3651602311510550306695513)
      ·
        refine ⟨2738701733632912730021635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3651602311510550306695513 2738701733632912730021635)
        ·
          refine ⟨4108052600449369095032453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2738701733632912730021635 4108052600449369095032453)
          ·
            refine ⟨770259862584256705318585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4108052600449369095032453 770259862584256705318585)
            ·
              refine ⟨577694896938192528988939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770259862584256705318585 577694896938192528988939)
              ·
                refine ⟨866542345407288793483409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577694896938192528988939 866542345407288793483409)
                ·
                  refine ⟨649906759055466595112557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 866542345407288793483409 649906759055466595112557)
                  ·
                    refine ⟨243715034645799973167209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 649906759055466595112557 243715034645799973167209)
                    ·
                      refine ⟨182786275984349979875407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243715034645799973167209 182786275984349979875407)
                      ·
                        rfl

theorem cell23_355975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_355975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355975 prefixEnd_355975 := by exact prefixLift 355975
  have htrace : WordTrace (prefixWord ++ tailWord_355975) baseStart_355975 baseEnd_355975 := by
    simpa [prefixWord, tailWord_355975, baseEnd_355975] using wordTrace_append hprefix tailTrace_355975
  have hstable : (prefixWord ++ tailWord_355975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355975).length < 2 ^ (prefixWord ++ tailWord_355975).sum := by decide
  have hdescent : baseEnd_355975 < baseStart_355975 := by decide
  rcases family_descends (prefixWord ++ tailWord_355975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355994 : List Nat := [3, 1, 1, 18]
def baseStart_355994 : Nat := 118140960795 + 355994 * 2 ^ 59
def prefixEnd_355994 : Nat := 4983230072969 + 3 ^ 40 * 355994 * 2
def baseEnd_355994 : Nat := 83583005083120898737

theorem tailTrace_355994 : CollatzResearch.WordTrace tailWord_355994 prefixEnd_355994 83583005083120898737 := by
  unfold tailWord_355994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3246041968075502944964759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8656111914868007853239357 3246041968075502944964759)
  ·
    refine ⟨4869062952113254417447139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3246041968075502944964759 4869062952113254417447139)
    ·
      refine ⟨7303594428169881626170709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4869062952113254417447139 7303594428169881626170709)
      ·
        refine ⟨83583005083120898737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 18 7303594428169881626170709 83583005083120898737)
        ·
          rfl

theorem cell23_355994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 18].length) (baseStart_355994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355994 prefixEnd_355994 := by exact prefixLift 355994
  have htrace : WordTrace (prefixWord ++ tailWord_355994) baseStart_355994 baseEnd_355994 := by
    simpa [prefixWord, tailWord_355994, baseEnd_355994] using wordTrace_append hprefix tailTrace_355994
  have hstable : (prefixWord ++ tailWord_355994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355994).length < 2 ^ (prefixWord ++ tailWord_355994).sum := by decide
  have hdescent : baseEnd_355994 < baseStart_355994 := by decide
  rcases family_descends (prefixWord ++ tailWord_355994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355999 : List Nat := [1, 1, 2, 7, 1, 1, 1, 4, 1, 1, 3]
def baseStart_355999 : Nat := 118140960795 + 355999 * 2 ^ 59
def prefixEnd_355999 : Nat := 4983230072969 + 3 ^ 40 * 355999 * 2
def baseEnd_355999 : Nat := 182798599520057885975297

theorem tailTrace_355999 : CollatzResearch.WordTrace tailWord_355999 prefixEnd_355999 182798599520057885975297 := by
  unfold tailWord_355999
  simp only [CollatzResearch.WordTrace]
  refine ⟨12984350237283897633791051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8656233491522598422527367 12984350237283897633791051)
  ·
    refine ⟨19476525355925846450686577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12984350237283897633791051 19476525355925846450686577)
    ·
      refine ⟨14607394016944384838014933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19476525355925846450686577 14607394016944384838014933)
      ·
        refine ⟨342360797272134019640975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14607394016944384838014933 342360797272134019640975)
        ·
          refine ⟨513541195908201029461463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342360797272134019640975 513541195908201029461463)
          ·
            refine ⟨770311793862301544192195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513541195908201029461463 770311793862301544192195)
            ·
              refine ⟨1155467690793452316288293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770311793862301544192195 1155467690793452316288293)
              ·
                refine ⟨216650192023772309304055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1155467690793452316288293 216650192023772309304055)
                ·
                  refine ⟨324975288035658463956083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216650192023772309304055 324975288035658463956083)
                  ·
                    refine ⟨487462932053487695934125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 324975288035658463956083 487462932053487695934125)
                    ·
                      refine ⟨182798599520057885975297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 487462932053487695934125 182798599520057885975297)
                      ·
                        rfl

theorem cell23_355999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_355999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_355999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_355999 prefixEnd_355999 := by exact prefixLift 355999
  have htrace : WordTrace (prefixWord ++ tailWord_355999) baseStart_355999 baseEnd_355999 := by
    simpa [prefixWord, tailWord_355999, baseEnd_355999] using wordTrace_append hprefix tailTrace_355999
  have hstable : (prefixWord ++ tailWord_355999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355999).length < 2 ^ (prefixWord ++ tailWord_355999).sum := by decide
  have hdescent : baseEnd_355999 < baseStart_355999 := by decide
  rcases family_descends (prefixWord ++ tailWord_355999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356028 : List Nat := [2, 2, 2, 3, 1, 3, 3, 7]
def baseStart_356028 : Nat := 118140960795 + 356028 * 2 ^ 59
def prefixEnd_356028 : Nat := 4983230072969 + 3 ^ 40 * 356028 * 2
def baseEnd_356028 : Nat := 6770870017001417500469

theorem tailTrace_356028 : CollatzResearch.WordTrace tailWord_356028 prefixEnd_356028 6770870017001417500469 := by
  unfold tailWord_356028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6492703977089417793298369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8656938636119223724397825 6492703977089417793298369)
  ·
    refine ⟨4869527982817063344973777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6492703977089417793298369 4869527982817063344973777)
    ·
      refine ⟨3652145987112797508730333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4869527982817063344973777 3652145987112797508730333)
      ·
        refine ⟨1369554745167299065773875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3652145987112797508730333 1369554745167299065773875)
        ·
          refine ⟨2054332117750948598660813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369554745167299065773875 2054332117750948598660813)
          ·
            refine ⟨770374544156605724497805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2054332117750948598660813 770374544156605724497805)
            ·
              refine ⟨288890454058727146686677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 770374544156605724497805 288890454058727146686677)
              ·
                refine ⟨6770870017001417500469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 288890454058727146686677 6770870017001417500469)
                ·
                  rfl

theorem cell23_356028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 7].length) (baseStart_356028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356028 prefixEnd_356028 := by exact prefixLift 356028
  have htrace : WordTrace (prefixWord ++ tailWord_356028) baseStart_356028 baseEnd_356028 := by
    simpa [prefixWord, tailWord_356028, baseEnd_356028] using wordTrace_append hprefix tailTrace_356028
  have hstable : (prefixWord ++ tailWord_356028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356028).length < 2 ^ (prefixWord ++ tailWord_356028).sum := by decide
  have hdescent : baseEnd_356028 < baseStart_356028 := by decide
  rcases family_descends (prefixWord ++ tailWord_356028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356048 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 5, 3, 2]
def baseStart_356048 : Nat := 118140960795 + 356048 * 2 ^ 59
def prefixEnd_356048 : Nat := 4983230072969 + 3 ^ 40 * 356048 * 2
def baseEnd_356048 : Nat := 182823760072128194262571

theorem tailTrace_356048 : CollatzResearch.WordTrace tailWord_356048 prefixEnd_356048 182823760072128194262571 := by
  unfold tailWord_356048
  simp only [CollatzResearch.WordTrace]
  refine ⟨6493068707053189501162399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8657424942737586001549865 6493068707053189501162399)
  ·
    refine ⟨9739603060579784251743599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6493068707053189501162399 9739603060579784251743599)
    ·
      refine ⟨14609404590869676377615399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9739603060579784251743599 14609404590869676377615399)
      ·
        refine ⟨21914106886304514566423099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14609404590869676377615399 21914106886304514566423099)
        ·
          refine ⟨32871160329456771849634649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21914106886304514566423099 32871160329456771849634649)
          ·
            refine ⟨24653370247092578887225987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32871160329456771849634649 24653370247092578887225987)
            ·
              refine ⟨36980055370638868330838981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24653370247092578887225987 36980055370638868330838981)
              ·
                refine ⟨6933760381994787812032309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36980055370638868330838981 6933760381994787812032309)
                ·
                  refine ⟨650040035812011357378029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6933760381994787812032309 650040035812011357378029)
                  ·
                    refine ⟨243765013429504259016761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 650040035812011357378029 243765013429504259016761)
                    ·
                      refine ⟨182823760072128194262571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243765013429504259016761 182823760072128194262571)
                      ·
                        rfl

theorem cell23_356048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 3, 2].length) (baseStart_356048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356048 prefixEnd_356048 := by exact prefixLift 356048
  have htrace : WordTrace (prefixWord ++ tailWord_356048) baseStart_356048 baseEnd_356048 := by
    simpa [prefixWord, tailWord_356048, baseEnd_356048] using wordTrace_append hprefix tailTrace_356048
  have hstable : (prefixWord ++ tailWord_356048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356048).length < 2 ^ (prefixWord ++ tailWord_356048).sum := by decide
  have hdescent : baseEnd_356048 < baseStart_356048 := by decide
  rcases family_descends (prefixWord ++ tailWord_356048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356082 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 1, 3, 2]
def baseStart_356082 : Nat := 118140960795 + 356082 * 2 ^ 59
def prefixEnd_356082 : Nat := 4983230072969 + 3 ^ 40 * 356082 * 2
def baseEnd_356082 : Nat := 182841218414381061237415

theorem tailTrace_356082 : CollatzResearch.WordTrace tailWord_356082 prefixEnd_356082 182841218414381061237415 := by
  unfold tailWord_356082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3246844373995800702265625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8658251663988801872708333 3246844373995800702265625)
  ·
    refine ⟨2435133280496850526699219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3246844373995800702265625 2435133280496850526699219)
    ·
      refine ⟨3652699920745275790048829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2435133280496850526699219 3652699920745275790048829)
      ·
        refine ⟨1369762470279478421268311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3652699920745275790048829 1369762470279478421268311)
        ·
          refine ⟨2054643705419217631902467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369762470279478421268311 2054643705419217631902467)
          ·
            refine ⟨3081965558128826447853701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054643705419217631902467 3081965558128826447853701)
            ·
              refine ⟨577868542149154958972569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3081965558128826447853701 577868542149154958972569)
              ·
                refine ⟨433401406611866219229427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577868542149154958972569 433401406611866219229427)
                ·
                  refine ⟨650102109917799328844141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433401406611866219229427 650102109917799328844141)
                  ·
                    refine ⟨243788291219174748316553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 650102109917799328844141 243788291219174748316553)
                    ·
                      refine ⟨182841218414381061237415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243788291219174748316553 182841218414381061237415)
                      ·
                        rfl

theorem cell23_356082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_356082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356082 prefixEnd_356082 := by exact prefixLift 356082
  have htrace : WordTrace (prefixWord ++ tailWord_356082) baseStart_356082 baseEnd_356082 := by
    simpa [prefixWord, tailWord_356082, baseEnd_356082] using wordTrace_append hprefix tailTrace_356082
  have hstable : (prefixWord ++ tailWord_356082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356082).length < 2 ^ (prefixWord ++ tailWord_356082).sum := by decide
  have hdescent : baseEnd_356082 < baseStart_356082 := by decide
  rcases family_descends (prefixWord ++ tailWord_356082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356091 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 4]
def baseStart_356091 : Nat := 118140960795 + 356091 * 2 ^ 59
def prefixEnd_356091 : Nat := 4983230072969 + 3 ^ 40 * 356091 * 2
def baseEnd_356091 : Nat := 182845839740271526024873

theorem tailTrace_356091 : CollatzResearch.WordTrace tailWord_356091 prefixEnd_356091 182845839740271526024873 := by
  unfold tailWord_356091
  simp only [CollatzResearch.WordTrace]
  refine ⟨12987705752950597346140127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8658470501967064897426751 12987705752950597346140127)
  ·
    refine ⟨19481558629425896019210191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12987705752950597346140127 19481558629425896019210191)
    ·
      refine ⟨29222337944138844028815287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19481558629425896019210191 29222337944138844028815287)
      ·
        refine ⟨43833506916208266043222931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29222337944138844028815287 43833506916208266043222931)
        ·
          refine ⟨65750260374312399064834397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43833506916208266043222931 65750260374312399064834397)
          ·
            refine ⟨24656347640367149649312899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65750260374312399064834397 24656347640367149649312899)
            ·
              refine ⟨36984521460550724473969349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24656347640367149649312899 36984521460550724473969349)
              ·
                refine ⟨6934597773853260838869253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36984521460550724473969349 6934597773853260838869253)
                ·
                  refine ⟨1300237082597486407287985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6934597773853260838869253 1300237082597486407287985)
                  ·
                    refine ⟨975177811948114805465989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1300237082597486407287985 975177811948114805465989)
                    ·
                      refine ⟨182845839740271526024873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 975177811948114805465989 182845839740271526024873)
                      ·
                        rfl

theorem cell23_356091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 4].length) (baseStart_356091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356091 prefixEnd_356091 := by exact prefixLift 356091
  have htrace : WordTrace (prefixWord ++ tailWord_356091) baseStart_356091 baseEnd_356091 := by
    simpa [prefixWord, tailWord_356091, baseEnd_356091] using wordTrace_append hprefix tailTrace_356091
  have hstable : (prefixWord ++ tailWord_356091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356091).length < 2 ^ (prefixWord ++ tailWord_356091).sum := by decide
  have hdescent : baseEnd_356091 < baseStart_356091 := by decide
  rcases family_descends (prefixWord ++ tailWord_356091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356095 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 4, 2, 2]
def baseStart_356095 : Nat := 118140960795 + 356095 * 2 ^ 59
def prefixEnd_356095 : Nat := 4983230072969 + 3 ^ 40 * 356095 * 2
def baseEnd_356095 : Nat := 182847893662889510374855

theorem tailTrace_356095 : CollatzResearch.WordTrace tailWord_356095 prefixEnd_356095 182847893662889510374855 := by
  unfold tailWord_356095
  simp only [CollatzResearch.WordTrace]
  refine ⟨12987851644936106029285739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8658567763290737352857159 12987851644936106029285739)
  ·
    refine ⟨19481777467404159043928609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12987851644936106029285739 19481777467404159043928609)
    ·
      refine ⟨14611333100553119282946457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19481777467404159043928609 14611333100553119282946457)
      ·
        refine ⟨10958499825414839462209843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14611333100553119282946457 10958499825414839462209843)
        ·
          refine ⟨16437749738122259193314765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10958499825414839462209843 16437749738122259193314765)
          ·
            refine ⟨6164156151795847197493037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16437749738122259193314765 6164156151795847197493037)
            ·
              refine ⟨2311558556923442699059889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6164156151795847197493037 2311558556923442699059889)
              ·
                refine ⟨1733668917692582024294917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2311558556923442699059889 1733668917692582024294917)
                ·
                  refine ⟨325062922067359129555297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1733668917692582024294917 325062922067359129555297)
                  ·
                    refine ⟨243797191550519347166473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 325062922067359129555297 243797191550519347166473)
                    ·
                      refine ⟨182847893662889510374855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243797191550519347166473 182847893662889510374855)
                      ·
                        rfl

theorem cell23_356095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_356095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356095 prefixEnd_356095 := by exact prefixLift 356095
  have htrace : WordTrace (prefixWord ++ tailWord_356095) baseStart_356095 baseEnd_356095 := by
    simpa [prefixWord, tailWord_356095, baseEnd_356095] using wordTrace_append hprefix tailTrace_356095
  have hstable : (prefixWord ++ tailWord_356095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356095).length < 2 ^ (prefixWord ++ tailWord_356095).sum := by decide
  have hdescent : baseEnd_356095 < baseStart_356095 := by decide
  rcases family_descends (prefixWord ++ tailWord_356095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356128 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 3]
def baseStart_356128 : Nat := 118140960795 + 356128 * 2 ^ 59
def prefixEnd_356128 : Nat := 4983230072969 + 3 ^ 40 * 356128 * 2
def baseEnd_356128 : Nat := 182864838524487881262203

theorem tailTrace_356128 : CollatzResearch.WordTrace tailWord_356128 prefixEnd_356128 182864838524487881262203 := by
  unfold tailWord_356128
  simp only [CollatzResearch.WordTrace]
  refine ⟨6494527626908276332618519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8659370169211035110158025 6494527626908276332618519)
  ·
    refine ⟨9741791440362414498927779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6494527626908276332618519 9741791440362414498927779)
    ·
      refine ⟨14612687160543621748391669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9741791440362414498927779 14612687160543621748391669)
      ·
        refine ⟨1369939421300964538911719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14612687160543621748391669 1369939421300964538911719)
        ·
          refine ⟨2054909131951446808367579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369939421300964538911719 2054909131951446808367579)
          ·
            refine ⟨3082363697927170212551369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054909131951446808367579 3082363697927170212551369)
            ·
              refine ⟨2311772773445377659413527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3082363697927170212551369 2311772773445377659413527)
              ·
                refine ⟨3467659160168066489120291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311772773445377659413527 3467659160168066489120291)
                ·
                  refine ⟨5201488740252099733680437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467659160168066489120291 5201488740252099733680437)
                  ·
                    refine ⟨487639569398634350032541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5201488740252099733680437 487639569398634350032541)
                    ·
                      refine ⟨182864838524487881262203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 487639569398634350032541 182864838524487881262203)
                      ·
                        rfl

theorem cell23_356128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_356128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356128 prefixEnd_356128 := by exact prefixLift 356128
  have htrace : WordTrace (prefixWord ++ tailWord_356128) baseStart_356128 baseEnd_356128 := by
    simpa [prefixWord, tailWord_356128, baseEnd_356128] using wordTrace_append hprefix tailTrace_356128
  have hstable : (prefixWord ++ tailWord_356128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356128).length < 2 ^ (prefixWord ++ tailWord_356128).sum := by decide
  have hdescent : baseEnd_356128 < baseStart_356128 := by decide
  rcases family_descends (prefixWord ++ tailWord_356128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356129 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 2, 2, 2]
def baseStart_356129 : Nat := 118140960795 + 356129 * 2 ^ 59
def prefixEnd_356129 : Nat := 4983230072969 + 3 ^ 40 * 356129 * 2
def baseEnd_356129 : Nat := 182865352005142377349699

theorem tailTrace_356129 : CollatzResearch.WordTrace tailWord_356129 prefixEnd_356129 182865352005142377349699 := by
  unfold tailWord_356129
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989091726812929836023441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8659394484541953224015627 12989091726812929836023441)
  ·
    refine ⟨9741818795109697377017581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12989091726812929836023441 9741818795109697377017581)
    ·
      refine ⟨3653182048166136516381593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9741818795109697377017581 3653182048166136516381593)
      ·
        refine ⟨2739886536124602387286195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3653182048166136516381593 2739886536124602387286195)
        ·
          refine ⟨4109829804186903580929293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739886536124602387286195 4109829804186903580929293)
          ·
            refine ⟨1541186176570088842848485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4109829804186903580929293 1541186176570088842848485)
            ·
              refine ⟨288972408106891658034091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1541186176570088842848485 288972408106891658034091)
              ·
                refine ⟨433458612160337487051137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288972408106891658034091 433458612160337487051137)
                ·
                  refine ⟨325093959120253115288353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433458612160337487051137 325093959120253115288353)
                  ·
                    refine ⟨243820469340189836466265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 325093959120253115288353 243820469340189836466265)
                    ·
                      refine ⟨182865352005142377349699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243820469340189836466265 182865352005142377349699)
                      ·
                        rfl

theorem cell23_356129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_356129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356129 prefixEnd_356129 := by exact prefixLift 356129
  have htrace : WordTrace (prefixWord ++ tailWord_356129) baseStart_356129 baseEnd_356129 := by
    simpa [prefixWord, tailWord_356129, baseEnd_356129] using wordTrace_append hprefix tailTrace_356129
  have hstable : (prefixWord ++ tailWord_356129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356129).length < 2 ^ (prefixWord ++ tailWord_356129).sum := by decide
  have hdescent : baseEnd_356129 < baseStart_356129 := by decide
  rcases family_descends (prefixWord ++ tailWord_356129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356131 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 3, 7]
def baseStart_356131 : Nat := 118140960795 + 356131 * 2 ^ 59
def prefixEnd_356131 : Nat := 4983230072969 + 3 ^ 40 * 356131 * 2
def baseEnd_356131 : Nat := 60955459655483789841563

theorem tailTrace_356131 : CollatzResearch.WordTrace tailWord_356131 prefixEnd_356131 60955459655483789841563 := by
  unfold tailWord_356131
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989164672805684177596247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8659443115203789451730831 12989164672805684177596247)
  ·
    refine ⟨19483747009208526266394371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12989164672805684177596247 19483747009208526266394371)
    ·
      refine ⟨29225620513812789399591557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19483747009208526266394371 29225620513812789399591557)
      ·
        refine ⟨5479803846339898012423417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29225620513812789399591557 5479803846339898012423417)
        ·
          refine ⟨4109852884754923509317563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5479803846339898012423417 4109852884754923509317563)
          ·
            refine ⟨6164779327132385263976345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109852884754923509317563 6164779327132385263976345)
            ·
              refine ⟨4623584495349288947982259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6164779327132385263976345 4623584495349288947982259)
              ·
                refine ⟨6935376743023933421973389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4623584495349288947982259 6935376743023933421973389)
                ·
                  refine ⟨2600766278633975033240021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6935376743023933421973389 2600766278633975033240021)
                  ·
                    refine ⟨60955459655483789841563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2600766278633975033240021 60955459655483789841563)
                    ·
                      rfl

theorem cell23_356131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 7].length) (baseStart_356131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356131 prefixEnd_356131 := by exact prefixLift 356131
  have htrace : WordTrace (prefixWord ++ tailWord_356131) baseStart_356131 baseEnd_356131 := by
    simpa [prefixWord, tailWord_356131, baseEnd_356131] using wordTrace_append hprefix tailTrace_356131
  have hstable : (prefixWord ++ tailWord_356131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356131).length < 2 ^ (prefixWord ++ tailWord_356131).sum := by decide
  have hdescent : baseEnd_356131 < baseStart_356131 := by decide
  rcases family_descends (prefixWord ++ tailWord_356131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356185 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 2, 4, 2]
def baseStart_356185 : Nat := 118140960795 + 356185 * 2 ^ 59
def prefixEnd_356185 : Nat := 4983230072969 + 3 ^ 40 * 356185 * 2
def baseEnd_356185 : Nat := 182894106921794158249441

theorem tailTrace_356185 : CollatzResearch.WordTrace tailWord_356185 prefixEnd_356185 182894106921794158249441 := by
  unfold tailWord_356185
  simp only [CollatzResearch.WordTrace]
  refine ⟨12991134214610051400062009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8660756143073367600041339 12991134214610051400062009)
  ·
    refine ⟨9743350660957538550046507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12991134214610051400062009 9743350660957538550046507)
    ·
      refine ⟨14615025991436307825069761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9743350660957538550046507 14615025991436307825069761)
      ·
        refine ⟨10961269493577230868802321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14615025991436307825069761 10961269493577230868802321)
        ·
          refine ⟨8220952120182923151601741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10961269493577230868802321 8220952120182923151601741)
          ·
            refine ⟨3082857045068596181850653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8220952120182923151601741 3082857045068596181850653)
            ·
              refine ⟨1156071391900723568193995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3082857045068596181850653 1156071391900723568193995)
              ·
                refine ⟨1734107087851085352290993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156071391900723568193995 1734107087851085352290993)
                ·
                  refine ⟨1300580315888314014218245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1734107087851085352290993 1300580315888314014218245)
                  ·
                    refine ⟨243858809229058877665921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1300580315888314014218245 243858809229058877665921)
                    ·
                      refine ⟨182894106921794158249441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243858809229058877665921 182894106921794158249441)
                      ·
                        rfl

theorem cell23_356185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_356185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356185 prefixEnd_356185 := by exact prefixLift 356185
  have htrace : WordTrace (prefixWord ++ tailWord_356185) baseStart_356185 baseEnd_356185 := by
    simpa [prefixWord, tailWord_356185, baseEnd_356185] using wordTrace_append hprefix tailTrace_356185
  have hstable : (prefixWord ++ tailWord_356185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356185).length < 2 ^ (prefixWord ++ tailWord_356185).sum := by decide
  have hdescent : baseEnd_356185 < baseStart_356185 := by decide
  rcases family_descends (prefixWord ++ tailWord_356185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356202 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_356202 : Nat := 118140960795 + 356202 * 2 ^ 59
def prefixEnd_356202 : Nat := 4983230072969 + 3 ^ 40 * 356202 * 2
def baseEnd_356202 : Nat := 182902836092920591736863

theorem tailTrace_356202 : CollatzResearch.WordTrace tailWord_356202 prefixEnd_356202 182902836092920591736863 := by
  unfold tailWord_356202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3247938563887115825857715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8661169503698975535620573 3247938563887115825857715)
  ·
    refine ⟨4871907845830673738786573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3247938563887115825857715 4871907845830673738786573)
    ·
      refine ⟨1826965442186502652044965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4871907845830673738786573 1826965442186502652044965)
      ·
        refine ⟨342556020409969247258431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1826965442186502652044965 342556020409969247258431)
        ·
          refine ⟨513834030614953870887647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342556020409969247258431 513834030614953870887647)
          ·
            refine ⟨770751045922430806331471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513834030614953870887647 770751045922430806331471)
            ·
              refine ⟨1156126568883646209497207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770751045922430806331471 1156126568883646209497207)
              ·
                refine ⟨1734189853325469314245811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156126568883646209497207 1734189853325469314245811)
                ·
                  refine ⟨2601284779988203971368717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734189853325469314245811 2601284779988203971368717)
                  ·
                    refine ⟨975481792495576489263269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2601284779988203971368717 975481792495576489263269)
                    ·
                      refine ⟨182902836092920591736863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 975481792495576489263269 182902836092920591736863)
                      ·
                        rfl

theorem cell23_356202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_356202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356202 prefixEnd_356202 := by exact prefixLift 356202
  have htrace : WordTrace (prefixWord ++ tailWord_356202) baseStart_356202 baseEnd_356202 := by
    simpa [prefixWord, tailWord_356202, baseEnd_356202] using wordTrace_append hprefix tailTrace_356202
  have hstable : (prefixWord ++ tailWord_356202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356202).length < 2 ^ (prefixWord ++ tailWord_356202).sum := by decide
  have hdescent : baseEnd_356202 < baseStart_356202 := by decide
  rcases family_descends (prefixWord ++ tailWord_356202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356228 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_356228 : Nat := 118140960795 + 356228 * 2 ^ 59
def prefixEnd_356228 : Nat := 4983230072969 + 3 ^ 40 * 356228 * 2
def baseEnd_356228 : Nat := 182916186589937490011743

theorem tailTrace_356228 : CollatzResearch.WordTrace tailWord_356228 prefixEnd_356228 182916186589937490011743 := by
  unfold tailWord_356228
  simp only [CollatzResearch.WordTrace]
  refine ⟨6496351276727134871938669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8661801702302846495918225 6496351276727134871938669)
  ·
    refine ⟨2436131728772675576977001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6496351276727134871938669 2436131728772675576977001)
    ·
      refine ⟨1827098796579506682732751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2436131728772675576977001 1827098796579506682732751)
      ·
        refine ⟨2740648194869260024099127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827098796579506682732751 2740648194869260024099127)
        ·
          refine ⟨4110972292303890036148691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2740648194869260024099127 4110972292303890036148691)
          ·
            refine ⟨6166458438455835054223037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110972292303890036148691 6166458438455835054223037)
            ·
              refine ⟨2312421914420938145333639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6166458438455835054223037 2312421914420938145333639)
              ·
                refine ⟨3468632871631407218000459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312421914420938145333639 3468632871631407218000459)
                ·
                  refine ⟨5202949307447110827000689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3468632871631407218000459 5202949307447110827000689)
                  ·
                    refine ⟨3902211980585333120250517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5202949307447110827000689 3902211980585333120250517)
                    ·
                      refine ⟨182916186589937490011743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3902211980585333120250517 182916186589937490011743)
                      ·
                        rfl

theorem cell23_356228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_356228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356228 prefixEnd_356228 := by exact prefixLift 356228
  have htrace : WordTrace (prefixWord ++ tailWord_356228) baseStart_356228 baseEnd_356228 := by
    simpa [prefixWord, tailWord_356228, baseEnd_356228] using wordTrace_append hprefix tailTrace_356228
  have hstable : (prefixWord ++ tailWord_356228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356228).length < 2 ^ (prefixWord ++ tailWord_356228).sum := by decide
  have hdescent : baseEnd_356228 < baseStart_356228 := by decide
  rcases family_descends (prefixWord ++ tailWord_356228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356245 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 3, 5, 2]
def baseStart_356245 : Nat := 118140960795 + 356245 * 2 ^ 59
def prefixEnd_356245 : Nat := 4983230072969 + 3 ^ 40 * 356245 * 2
def baseEnd_356245 : Nat := 182924915761063923499165

theorem tailTrace_356245 : CollatzResearch.WordTrace tailWord_356245 prefixEnd_356245 182924915761063923499165 := by
  unfold tailWord_356245
  simp only [CollatzResearch.WordTrace]
  refine ⟨12993322594392681647246189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8662215062928454431497459 12993322594392681647246189)
  ·
    refine ⟨4872495972897255617717321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12993322594392681647246189 4872495972897255617717321)
    ·
      refine ⟨3654371979672941713287991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4872495972897255617717321 3654371979672941713287991)
      ·
        refine ⟨5481557969509412569931987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654371979672941713287991 5481557969509412569931987)
        ·
          refine ⟨8222336954264118854897981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481557969509412569931987 8222336954264118854897981)
          ·
            refine ⟨3083376357849044570586743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8222336954264118854897981 3083376357849044570586743)
            ·
              refine ⟨4625064536773566855880115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083376357849044570586743 4625064536773566855880115)
              ·
                refine ⟨6937596805160350283820173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625064536773566855880115 6937596805160350283820173)
                ·
                  refine ⟨2601598801935131356432565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6937596805160350283820173 2601598801935131356432565)
                  ·
                    refine ⟨243899887681418564665553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2601598801935131356432565 243899887681418564665553)
                    ·
                      refine ⟨182924915761063923499165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 243899887681418564665553 182924915761063923499165)
                      ·
                        rfl

theorem cell23_356245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_356245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356245 prefixEnd_356245 := by exact prefixLift 356245
  have htrace : WordTrace (prefixWord ++ tailWord_356245) baseStart_356245 baseEnd_356245 := by
    simpa [prefixWord, tailWord_356245, baseEnd_356245] using wordTrace_append hprefix tailTrace_356245
  have hstable : (prefixWord ++ tailWord_356245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356245).length < 2 ^ (prefixWord ++ tailWord_356245).sum := by decide
  have hdescent : baseEnd_356245 < baseStart_356245 := by decide
  rcases family_descends (prefixWord ++ tailWord_356245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356275 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 4]
def baseStart_356275 : Nat := 118140960795 + 356275 * 2 ^ 59
def prefixEnd_356275 : Nat := 4983230072969 + 3 ^ 40 * 356275 * 2
def baseEnd_356275 : Nat := 182940320180698806124027

theorem tailTrace_356275 : CollatzResearch.WordTrace tailWord_356275 prefixEnd_356275 182940320180698806124027 := by
  unfold tailWord_356275
  simp only [CollatzResearch.WordTrace]
  refine ⟨12994416784283996770838279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8662944522855997847225519 12994416784283996770838279)
  ·
    refine ⟨19491625176425995156257419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12994416784283996770838279 19491625176425995156257419)
    ·
      refine ⟨29237437764638992734386129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19491625176425995156257419 29237437764638992734386129)
      ·
        refine ⟨21928078323479244550789597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29237437764638992734386129 21928078323479244550789597)
        ·
          refine ⟨8223029371304716706546099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21928078323479244550789597 8223029371304716706546099)
          ·
            refine ⟨12334544056957075059819149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8223029371304716706546099 12334544056957075059819149)
            ·
              refine ⟨4625454021358903147432181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12334544056957075059819149 4625454021358903147432181)
              ·
                refine ⟨433636314502397170071767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4625454021358903147432181 433636314502397170071767)
                ·
                  refine ⟨650454471753595755107651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433636314502397170071767 650454471753595755107651)
                  ·
                    refine ⟨975681707630393632661477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 650454471753595755107651 975681707630393632661477)
                    ·
                      refine ⟨182940320180698806124027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 975681707630393632661477 182940320180698806124027)
                      ·
                        rfl

theorem cell23_356275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 4].length) (baseStart_356275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356275 prefixEnd_356275 := by exact prefixLift 356275
  have htrace : WordTrace (prefixWord ++ tailWord_356275) baseStart_356275 baseEnd_356275 := by
    simpa [prefixWord, tailWord_356275, baseEnd_356275] using wordTrace_append hprefix tailTrace_356275
  have hstable : (prefixWord ++ tailWord_356275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356275).length < 2 ^ (prefixWord ++ tailWord_356275).sum := by decide
  have hdescent : baseEnd_356275 < baseStart_356275 := by decide
  rcases family_descends (prefixWord ++ tailWord_356275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356288 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_356288 : Nat := 118140960795 + 356288 * 2 ^ 59
def prefixEnd_356288 : Nat := 4983230072969 + 3 ^ 40 * 356288 * 2
def baseEnd_356288 : Nat := 182946995429207255261467

theorem tailTrace_356288 : CollatzResearch.WordTrace tailWord_356288 prefixEnd_356288 182946995429207255261467 := by
  unfold tailWord_356288
  simp only [CollatzResearch.WordTrace]
  refine ⟨6497445466618449995530759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8663260622157933327374345 6497445466618449995530759)
  ·
    refine ⟨9746168199927674993296139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6497445466618449995530759 9746168199927674993296139)
    ·
      refine ⟨14619252299891512489944209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9746168199927674993296139 14619252299891512489944209)
      ·
        refine ⟨10964439224918634367458157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14619252299891512489944209 10964439224918634367458157)
        ·
          refine ⟨4111664709344487887796809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10964439224918634367458157 4111664709344487887796809)
          ·
            refine ⟨3083748532008365915847607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4111664709344487887796809 3083748532008365915847607)
            ·
              refine ⟨4625622798012548873771411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083748532008365915847607 4625622798012548873771411)
              ·
                refine ⟨6938434197018823310657117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625622798012548873771411 6938434197018823310657117)
                ·
                  refine ⟨2601912823882058741496419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6938434197018823310657117 2601912823882058741496419)
                  ·
                    refine ⟨3902869235823088112244629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2601912823882058741496419 3902869235823088112244629)
                    ·
                      refine ⟨182946995429207255261467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3902869235823088112244629 182946995429207255261467)
                      ·
                        rfl

theorem cell23_356288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_356288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356288 prefixEnd_356288 := by exact prefixLift 356288
  have htrace : WordTrace (prefixWord ++ tailWord_356288) baseStart_356288 baseEnd_356288 := by
    simpa [prefixWord, tailWord_356288, baseEnd_356288] using wordTrace_append hprefix tailTrace_356288
  have hstable : (prefixWord ++ tailWord_356288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356288).length < 2 ^ (prefixWord ++ tailWord_356288).sum := by decide
  have hdescent : baseEnd_356288 < baseStart_356288 := by decide
  rcases family_descends (prefixWord ++ tailWord_356288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356295 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_356295 : Nat := 118140960795 + 356295 * 2 ^ 59
def prefixEnd_356295 : Nat := 4983230072969 + 3 ^ 40 * 356295 * 2
def baseEnd_356295 : Nat := 182950589793788727873935

theorem tailTrace_356295 : CollatzResearch.WordTrace tailWord_356295 prefixEnd_356295 182950589793788727873935 := by
  unfold tailWord_356295
  simp only [CollatzResearch.WordTrace]
  refine ⟨12995146244211540186566339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8663430829474360124377559 12995146244211540186566339)
  ·
    refine ⟨19492719366317310279849509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12995146244211540186566339 19492719366317310279849509)
    ·
      refine ⟨3654884881184495677471783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19492719366317310279849509 3654884881184495677471783)
      ·
        refine ⟨5482327321776743516207675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654884881184495677471783 5482327321776743516207675)
        ·
          refine ⟨8223490982665115274311513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5482327321776743516207675 8223490982665115274311513)
          ·
            refine ⟨6167618236998836455733635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8223490982665115274311513 6167618236998836455733635)
            ·
              refine ⟨9251427355498254683600453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6167618236998836455733635 9251427355498254683600453)
              ·
                refine ⟨1734642629155922753175085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9251427355498254683600453 1734642629155922753175085)
                ·
                  refine ⟨650490985933471032440657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1734642629155922753175085 650490985933471032440657)
                  ·
                    refine ⟨487868239450103274330493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 650490985933471032440657 487868239450103274330493)
                    ·
                      refine ⟨182950589793788727873935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 487868239450103274330493 182950589793788727873935)
                      ·
                        rfl

theorem cell23_356295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_356295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356295 prefixEnd_356295 := by exact prefixLift 356295
  have htrace : WordTrace (prefixWord ++ tailWord_356295) baseStart_356295 baseEnd_356295 := by
    simpa [prefixWord, tailWord_356295, baseEnd_356295] using wordTrace_append hprefix tailTrace_356295
  have hstable : (prefixWord ++ tailWord_356295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356295).length < 2 ^ (prefixWord ++ tailWord_356295).sum := by decide
  have hdescent : baseEnd_356295 < baseStart_356295 := by decide
  rcases family_descends (prefixWord ++ tailWord_356295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356298 : List Nat := [3, 1, 2, 1, 2, 1, 3, 10]
def baseStart_356298 : Nat := 118140960795 + 356298 * 2 ^ 59
def prefixEnd_356298 : Nat := 4983230072969 + 3 ^ 40 * 356298 * 2
def baseEnd_356298 : Nat := 6776004823546378375423

theorem tailTrace_356298 : CollatzResearch.WordTrace tailWord_356298 prefixEnd_356298 6776004823546378375423 := by
  unfold tailWord_356298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248813915800167924731387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8663503775467114465950365 3248813915800167924731387)
  ·
    refine ⟨4873220873700251887097081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3248813915800167924731387 4873220873700251887097081)
    ·
      refine ⟨3654915655275188915322811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4873220873700251887097081 3654915655275188915322811)
      ·
        refine ⟨5482373482912783372984217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654915655275188915322811 5482373482912783372984217)
        ·
          refine ⟨4111780112184587529738163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5482373482912783372984217 4111780112184587529738163)
          ·
            refine ⟨6167670168276881294607245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4111780112184587529738163 6167670168276881294607245)
            ·
              refine ⟨2312876313103830485477717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6167670168276881294607245 2312876313103830485477717)
              ·
                refine ⟨6776004823546378375423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2312876313103830485477717 6776004823546378375423)
                ·
                  rfl

theorem cell23_356298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 10].length) (baseStart_356298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356298 prefixEnd_356298 := by exact prefixLift 356298
  have htrace : WordTrace (prefixWord ++ tailWord_356298) baseStart_356298 baseEnd_356298 := by
    simpa [prefixWord, tailWord_356298, baseEnd_356298] using wordTrace_append hprefix tailTrace_356298
  have hstable : (prefixWord ++ tailWord_356298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356298).length < 2 ^ (prefixWord ++ tailWord_356298).sum := by decide
  have hdescent : baseEnd_356298 < baseStart_356298 := by decide
  rcases family_descends (prefixWord ++ tailWord_356298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356302 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_356302 : Nat := 118140960795 + 356302 * 2 ^ 59
def prefixEnd_356302 : Nat := 4983230072969 + 3 ^ 40 * 356302 * 2
def baseEnd_356302 : Nat := 60984728052790066828801

theorem tailTrace_356302 : CollatzResearch.WordTrace tailWord_356302 prefixEnd_356302 60984728052790066828801 := by
  unfold tailWord_356302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624425194398272547758895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8663601036790786921380773 1624425194398272547758895)
  ·
    refine ⟨2436637791597408821638343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1624425194398272547758895 2436637791597408821638343)
    ·
      refine ⟨3654956687396113232457515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2436637791597408821638343 3654956687396113232457515)
      ·
        refine ⟨5482435031094169848686273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654956687396113232457515 5482435031094169848686273)
        ·
          refine ⟨4111826273320627386514705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5482435031094169848686273 4111826273320627386514705)
          ·
            refine ⟨3083869704990470539886029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4111826273320627386514705 3083869704990470539886029)
            ·
              refine ⟨1156451139371426452457261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3083869704990470539886029 1156451139371426452457261)
              ·
                refine ⟨433669177264284919671473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1156451139371426452457261 433669177264284919671473)
                ·
                  refine ⟨325251882948213689753605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433669177264284919671473 325251882948213689753605)
                  ·
                    refine ⟨60984728052790066828801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 325251882948213689753605 60984728052790066828801)
                    ·
                      rfl

theorem cell23_356302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_356302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356302 prefixEnd_356302 := by exact prefixLift 356302
  have htrace : WordTrace (prefixWord ++ tailWord_356302) baseStart_356302 baseEnd_356302 := by
    simpa [prefixWord, tailWord_356302, baseEnd_356302] using wordTrace_append hprefix tailTrace_356302
  have hstable : (prefixWord ++ tailWord_356302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356302).length < 2 ^ (prefixWord ++ tailWord_356302).sum := by decide
  have hdescent : baseEnd_356302 < baseStart_356302 := by decide
  rcases family_descends (prefixWord ++ tailWord_356302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356306 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_356306 : Nat := 118140960795 + 356306 * 2 ^ 59
def prefixEnd_356306 : Nat := 4983230072969 + 3 ^ 40 * 356306 * 2
def baseEnd_356306 : Nat := 60985412693662728278795

theorem tailTrace_356306 : CollatzResearch.WordTrace tailWord_356306 prefixEnd_356306 60985412693662728278795 := by
  unfold tailWord_356306
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248886861792922266304193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8663698298114459376811181 3248886861792922266304193)
  ·
    refine ⟨2436665146344691699728145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3248886861792922266304193 2436665146344691699728145)
    ·
      refine ⟨1827498859758518774796109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2436665146344691699728145 1827498859758518774796109)
      ·
        refine ⟨685312072409444540548541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1827498859758518774796109 685312072409444540548541)
        ·
          refine ⟨256992027153541702705703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 685312072409444540548541 256992027153541702705703)
          ·
            refine ⟨385488040730312554058555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256992027153541702705703 385488040730312554058555)
            ·
              refine ⟨578232061095468831087833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385488040730312554058555 578232061095468831087833)
              ·
                refine ⟨433674045821601623315875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578232061095468831087833 433674045821601623315875)
                ·
                  refine ⟨650511068732402434973813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433674045821601623315875 650511068732402434973813)
                  ·
                    refine ⟨60985412693662728278795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 650511068732402434973813 60985412693662728278795)
                    ·
                      rfl

theorem cell23_356306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_356306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356306 prefixEnd_356306 := by exact prefixLift 356306
  have htrace : WordTrace (prefixWord ++ tailWord_356306) baseStart_356306 baseEnd_356306 := by
    simpa [prefixWord, tailWord_356306, baseEnd_356306] using wordTrace_append hprefix tailTrace_356306
  have hstable : (prefixWord ++ tailWord_356306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356306).length < 2 ^ (prefixWord ++ tailWord_356306).sum := by decide
  have hdescent : baseEnd_356306 < baseStart_356306 := by decide
  rcases family_descends (prefixWord ++ tailWord_356306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356309 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_356309 : Nat := 118140960795 + 356309 * 2 ^ 59
def prefixEnd_356309 : Nat := 4983230072969 + 3 ^ 40 * 356309 * 2
def baseEnd_356309 : Nat := 182957778522951673098871

theorem tailTrace_356309 : CollatzResearch.WordTrace tailWord_356309 prefixEnd_356309 182957778522951673098871 := by
  unfold tailWord_356309
  simp only [CollatzResearch.WordTrace]
  refine ⟨12995656866160820577575981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8663771244107213718383987 12995656866160820577575981)
  ·
    refine ⟨4873371324810307716590993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12995656866160820577575981 4873371324810307716590993)
    ·
      refine ⟨3655028493607730787443245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4873371324810307716590993 3655028493607730787443245)
      ·
        refine ⟨1370635685102899045291217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3655028493607730787443245 1370635685102899045291217)
        ·
          refine ⟨1027976763827174283968413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1370635685102899045291217 1027976763827174283968413)
          ·
            refine ⟨385491286435190356488155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1027976763827174283968413 385491286435190356488155)
            ·
              refine ⟨578236929652785534732233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385491286435190356488155 578236929652785534732233)
              ·
                refine ⟨433677697239589151049175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578236929652785534732233 433677697239589151049175)
                ·
                  refine ⟨650516545859383726573763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433677697239589151049175 650516545859383726573763)
                  ·
                    refine ⟨975774818789075589860645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 650516545859383726573763 975774818789075589860645)
                    ·
                      refine ⟨182957778522951673098871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 975774818789075589860645 182957778522951673098871)
                      ·
                        rfl

theorem cell23_356309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_356309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356309 prefixEnd_356309 := by exact prefixLift 356309
  have htrace : WordTrace (prefixWord ++ tailWord_356309) baseStart_356309 baseEnd_356309 := by
    simpa [prefixWord, tailWord_356309, baseEnd_356309] using wordTrace_append hprefix tailTrace_356309
  have hstable : (prefixWord ++ tailWord_356309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356309).length < 2 ^ (prefixWord ++ tailWord_356309).sum := by decide
  have hdescent : baseEnd_356309 < baseStart_356309 := by decide
  rcases family_descends (prefixWord ++ tailWord_356309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356359 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_356359 : Nat := 118140960795 + 356359 * 2 ^ 59
def prefixEnd_356359 : Nat := 4983230072969 + 3 ^ 40 * 356359 * 2
def baseEnd_356359 : Nat := 182983452555676477473641

theorem tailTrace_356359 : CollatzResearch.WordTrace tailWord_356359 prefixEnd_356359 182983452555676477473641 := by
  unfold tailWord_356359
  simp only [CollatzResearch.WordTrace]
  refine ⟨12997480515979679116896131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8664987010653119411264087 12997480515979679116896131)
  ·
    refine ⟨19496220773969518675344197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12997480515979679116896131 19496220773969518675344197)
    ·
      refine ⟨3655541395119284751627037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19496220773969518675344197 3655541395119284751627037)
      ·
        refine ⟨1370828023169731781860139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3655541395119284751627037 1370828023169731781860139)
        ·
          refine ⟨2056242034754597672790209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370828023169731781860139 2056242034754597672790209)
          ·
            refine ⟨1542181526065948254592657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2056242034754597672790209 1542181526065948254592657)
            ·
              refine ⟨1156636144549461190944493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1542181526065948254592657 1156636144549461190944493)
              ·
                refine ⟨433738554206047946604185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1156636144549461190944493 433738554206047946604185)
                ·
                  refine ⟨325303915654535959953139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433738554206047946604185 325303915654535959953139)
                  ·
                    refine ⟨487955873481803939929709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 325303915654535959953139 487955873481803939929709)
                    ·
                      refine ⟨182983452555676477473641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 487955873481803939929709 182983452555676477473641)
                      ·
                        rfl

theorem cell23_356359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_356359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356359 prefixEnd_356359 := by exact prefixLift 356359
  have htrace : WordTrace (prefixWord ++ tailWord_356359) baseStart_356359 baseEnd_356359 := by
    simpa [prefixWord, tailWord_356359, baseEnd_356359] using wordTrace_append hprefix tailTrace_356359
  have hstable : (prefixWord ++ tailWord_356359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356359).length < 2 ^ (prefixWord ++ tailWord_356359).sum := by decide
  have hdescent : baseEnd_356359 < baseStart_356359 := by decide
  rcases family_descends (prefixWord ++ tailWord_356359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356399 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 2, 2, 2]
def baseStart_356399 : Nat := 118140960795 + 356399 * 2 ^ 59
def prefixEnd_356399 : Nat := 4983230072969 + 3 ^ 40 * 356399 * 2
def baseEnd_356399 : Nat := 183003991781856320973457

theorem tailTrace_356399 : CollatzResearch.WordTrace tailWord_356399 prefixEnd_356399 183003991781856320973457 := by
  unfold tailWord_356399
  simp only [CollatzResearch.WordTrace]
  refine ⟨12998939435834765948352251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8665959623889843965568167 12998939435834765948352251)
  ·
    refine ⟨19498409153752148922528377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12998939435834765948352251 19498409153752148922528377)
    ·
      refine ⟨14623806865314111691896283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19498409153752148922528377 14623806865314111691896283)
      ·
        refine ⟨21935710297971167537844425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14623806865314111691896283 21935710297971167537844425)
        ·
          refine ⟨16451782723478375653383319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21935710297971167537844425 16451782723478375653383319)
          ·
            refine ⟨24677674085217563480074979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16451782723478375653383319 24677674085217563480074979)
            ·
              refine ⟨37016511127826345220112469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24677674085217563480074979 37016511127826345220112469)
              ·
                refine ⟨433787239779214983048193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 37016511127826345220112469 433787239779214983048193)
                ·
                  refine ⟨325340429834411237286145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433787239779214983048193 325340429834411237286145)
                  ·
                    refine ⟨244005322375808427964609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 325340429834411237286145 244005322375808427964609)
                    ·
                      refine ⟨183003991781856320973457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244005322375808427964609 183003991781856320973457)
                      ·
                        rfl

theorem cell23_356399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 2, 2].length) (baseStart_356399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356399 prefixEnd_356399 := by exact prefixLift 356399
  have htrace : WordTrace (prefixWord ++ tailWord_356399) baseStart_356399 baseEnd_356399 := by
    simpa [prefixWord, tailWord_356399, baseEnd_356399] using wordTrace_append hprefix tailTrace_356399
  have hstable : (prefixWord ++ tailWord_356399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356399).length < 2 ^ (prefixWord ++ tailWord_356399).sum := by decide
  have hdescent : baseEnd_356399 < baseStart_356399 := by decide
  rcases family_descends (prefixWord ++ tailWord_356399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356405 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 7]
def baseStart_356405 : Nat := 118140960795 + 356405 * 2 ^ 59
def prefixEnd_356405 : Nat := 4983230072969 + 3 ^ 40 * 356405 * 2
def baseEnd_356405 : Nat := 20334119185087033055381

theorem tailTrace_356405 : CollatzResearch.WordTrace tailWord_356405 prefixEnd_356405 20334119185087033055381 := by
  unfold tailWord_356405
  simp only [CollatzResearch.WordTrace]
  refine ⟨12999158273813028973070669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8666105515875352648713779 12999158273813028973070669)
  ·
    refine ⟨4874684352679885864901501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12999158273813028973070669 4874684352679885864901501)
    ·
      refine ⟨1828006632254957199338063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4874684352679885864901501 1828006632254957199338063)
      ·
        refine ⟨2742009948382435799007095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828006632254957199338063 2742009948382435799007095)
        ·
          refine ⟨4113014922573653698510643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742009948382435799007095 4113014922573653698510643)
          ·
            refine ⟨6169522383860480547765965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113014922573653698510643 6169522383860480547765965)
            ·
              refine ⟨2313570893947680205412237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6169522383860480547765965 2313570893947680205412237)
              ·
                refine ⟨867589085230380077029589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2313570893947680205412237 867589085230380077029589)
                ·
                  refine ⟨20334119185087033055381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 867589085230380077029589 20334119185087033055381)
                  ·
                    rfl

theorem cell23_356405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_356405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356405 prefixEnd_356405 := by exact prefixLift 356405
  have htrace : WordTrace (prefixWord ++ tailWord_356405) baseStart_356405 baseEnd_356405 := by
    simpa [prefixWord, tailWord_356405, baseEnd_356405] using wordTrace_append hprefix tailTrace_356405
  have hstable : (prefixWord ++ tailWord_356405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356405).length < 2 ^ (prefixWord ++ tailWord_356405).sum := by decide
  have hdescent : baseEnd_356405 < baseStart_356405 := by decide
  rcases family_descends (prefixWord ++ tailWord_356405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356462 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_356462 : Nat := 118140960795 + 356462 * 2 ^ 59
def prefixEnd_356462 : Nat := 4983230072969 + 3 ^ 40 * 356462 * 2
def baseEnd_356462 : Nat := 183036341063089574485667

theorem tailTrace_356462 : CollatzResearch.WordTrace tailWord_356462 prefixEnd_356462 183036341063089574485667 := by
  unfold tailWord_356462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625154654325815963486955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8667491489737685138597093 1625154654325815963486955)
  ·
    refine ⟨2437731981488723945230433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1625154654325815963486955 2437731981488723945230433)
    ·
      refine ⟨1828298986116542958922825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2437731981488723945230433 1828298986116542958922825)
      ·
        refine ⟨1371224239587407219192119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1828298986116542958922825 1371224239587407219192119)
        ·
          refine ⟨2056836359381110828788179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371224239587407219192119 2056836359381110828788179)
          ·
            refine ⟨3085254539071666243182269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056836359381110828788179 3085254539071666243182269)
            ·
              refine ⟨1156970452151874841193351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3085254539071666243182269 1156970452151874841193351)
              ·
                refine ⟨1735455678227812261790027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156970452151874841193351 1735455678227812261790027)
                ·
                  refine ⟨2603183517341718392685041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735455678227812261790027 2603183517341718392685041)
                  ·
                    refine ⟨1952387638006288794513781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2603183517341718392685041 1952387638006288794513781)
                    ·
                      refine ⟨183036341063089574485667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1952387638006288794513781 183036341063089574485667)
                      ·
                        rfl

theorem cell23_356462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_356462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356462 prefixEnd_356462 := by exact prefixLift 356462
  have htrace : WordTrace (prefixWord ++ tailWord_356462) baseStart_356462 baseEnd_356462 := by
    simpa [prefixWord, tailWord_356462, baseEnd_356462] using wordTrace_append hprefix tailTrace_356462
  have hstable : (prefixWord ++ tailWord_356462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356462).length < 2 ^ (prefixWord ++ tailWord_356462).sum := by decide
  have hdescent : baseEnd_356462 < baseStart_356462 := by decide
  rcases family_descends (prefixWord ++ tailWord_356462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356472 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 1, 6, 2]
def baseStart_356472 : Nat := 118140960795 + 356472 * 2 ^ 59
def prefixEnd_356472 : Nat := 4983230072969 + 3 ^ 40 * 356472 * 2
def baseEnd_356472 : Nat := 183041475869634535360621

theorem tailTrace_356472 : CollatzResearch.WordTrace tailWord_356472 prefixEnd_356472 183041475869634535360621 := by
  unfold tailWord_356472
  simp only [CollatzResearch.WordTrace]
  refine ⟨6500800982285149707879835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8667734643046866277173113 6500800982285149707879835)
  ·
    refine ⟨9751201473427724561819753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6500800982285149707879835 9751201473427724561819753)
    ·
      refine ⟨7313401105070793421364815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9751201473427724561819753 7313401105070793421364815)
      ·
        refine ⟨10970101657606190132047223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7313401105070793421364815 10970101657606190132047223)
        ·
          refine ⟨16455152486409285198070835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10970101657606190132047223 16455152486409285198070835)
          ·
            refine ⟨24682728729613927797106253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16455152486409285198070835 24682728729613927797106253)
            ·
              refine ⟨9256023273605222923914845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24682728729613927797106253 9256023273605222923914845)
              ·
                refine ⟨3471008727601958596468067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9256023273605222923914845 3471008727601958596468067)
                ·
                  refine ⟨5206513091402937894702101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471008727601958596468067 5206513091402937894702101)
                  ·
                    refine ⟨244055301159512713814161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5206513091402937894702101 244055301159512713814161)
                    ·
                      refine ⟨183041475869634535360621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244055301159512713814161 183041475869634535360621)
                      ·
                        rfl

theorem cell23_356472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_356472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356472 prefixEnd_356472 := by exact prefixLift 356472
  have htrace : WordTrace (prefixWord ++ tailWord_356472) baseStart_356472 baseEnd_356472 := by
    simpa [prefixWord, tailWord_356472, baseEnd_356472] using wordTrace_append hprefix tailTrace_356472
  have hstable : (prefixWord ++ tailWord_356472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356472).length < 2 ^ (prefixWord ++ tailWord_356472).sum := by decide
  have hdescent : baseEnd_356472 < baseStart_356472 := by decide
  rcases family_descends (prefixWord ++ tailWord_356472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356499 : List Nat := [1, 1, 1, 2, 1, 2, 3, 7, 1, 4]
def baseStart_356499 : Nat := 118140960795 + 356499 * 2 ^ 59
def prefixEnd_356499 : Nat := 4983230072969 + 3 ^ 40 * 356499 * 2
def baseEnd_356499 : Nat := 61018446615768643240999

theorem tailTrace_356499 : CollatzResearch.WordTrace tailWord_356499 prefixEnd_356499 61018446615768643240999 := by
  unfold tailWord_356499
  simp only [CollatzResearch.WordTrace]
  refine ⟨13002586735472483026992551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8668391156981655351328367 13002586735472483026992551)
  ·
    refine ⟨19503880103208724540488827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13002586735472483026992551 19503880103208724540488827)
    ·
      refine ⟨29255820154813086810733241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19503880103208724540488827 29255820154813086810733241)
      ·
        refine ⟨21941865116109815108049931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29255820154813086810733241 21941865116109815108049931)
        ·
          refine ⟨32912797674164722662074897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21941865116109815108049931 32912797674164722662074897)
          ·
            refine ⟨24684598255623541996556173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32912797674164722662074897 24684598255623541996556173)
            ·
              refine ⟨9256724345858828248708565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24684598255623541996556173 9256724345858828248708565)
              ·
                refine ⟨216954476856066287079107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9256724345858828248708565 216954476856066287079107)
                ·
                  refine ⟨325431715284099430618661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216954476856066287079107 325431715284099430618661)
                  ·
                    refine ⟨61018446615768643240999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 325431715284099430618661 61018446615768643240999)
                    ·
                      rfl

theorem cell23_356499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 1, 4].length) (baseStart_356499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356499 prefixEnd_356499 := by exact prefixLift 356499
  have htrace : WordTrace (prefixWord ++ tailWord_356499) baseStart_356499 baseEnd_356499 := by
    simpa [prefixWord, tailWord_356499, baseEnd_356499] using wordTrace_append hprefix tailTrace_356499
  have hstable : (prefixWord ++ tailWord_356499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356499).length < 2 ^ (prefixWord ++ tailWord_356499).sum := by decide
  have hdescent : baseEnd_356499 < baseStart_356499 := by decide
  rcases family_descends (prefixWord ++ tailWord_356499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356509 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_356509 : Nat := 118140960795 + 356509 * 2 ^ 59
def prefixEnd_356509 : Nat := 4983230072969 + 3 ^ 40 * 356509 * 2
def baseEnd_356509 : Nat := 183060474653850890597951

theorem tailTrace_356509 : CollatzResearch.WordTrace tailWord_356509 prefixEnd_356509 183060474653850890597951 := by
  unfold tailWord_356509
  simp only [CollatzResearch.WordTrace]
  refine ⟨13002951465436254734856581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8668634310290836489904387 13002951465436254734856581)
  ·
    refine ⟨2438053399769297762785609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13002951465436254734856581 2438053399769297762785609)
    ·
      refine ⟨1828540049826973322089207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2438053399769297762785609 1828540049826973322089207)
      ·
        refine ⟨2742810074740459983133811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828540049826973322089207 2742810074740459983133811)
        ·
          refine ⟨4114215112110689974700717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742810074740459983133811 4114215112110689974700717)
          ·
            refine ⟨1542830667041508740512769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4114215112110689974700717 1542830667041508740512769)
            ·
              refine ⟨1157123000281131555384577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1542830667041508740512769 1157123000281131555384577)
              ·
                refine ⟨867842250210848666538433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1157123000281131555384577 867842250210848666538433)
                ·
                  refine ⟨650881687658136499903825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 867842250210848666538433 650881687658136499903825)
                  ·
                    refine ⟨488161265743602374927869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 650881687658136499903825 488161265743602374927869)
                    ·
                      refine ⟨183060474653850890597951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 488161265743602374927869 183060474653850890597951)
                      ·
                        rfl

theorem cell23_356509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_356509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356509 prefixEnd_356509 := by exact prefixLift 356509
  have htrace : WordTrace (prefixWord ++ tailWord_356509) baseStart_356509 baseEnd_356509 := by
    simpa [prefixWord, tailWord_356509, baseEnd_356509] using wordTrace_append hprefix tailTrace_356509
  have hstable : (prefixWord ++ tailWord_356509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356509).length < 2 ^ (prefixWord ++ tailWord_356509).sum := by decide
  have hdescent : baseEnd_356509 < baseStart_356509 := by decide
  rcases family_descends (prefixWord ++ tailWord_356509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356512 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 6]
def baseStart_356512 : Nat := 118140960795 + 356512 * 2 ^ 59
def prefixEnd_356512 : Nat := 4983230072969 + 3 ^ 40 * 356512 * 2
def baseEnd_356512 : Nat := 20340223899534930984493

theorem tailTrace_356512 : CollatzResearch.WordTrace tailWord_356512 prefixEnd_356512 20340223899534930984493 := by
  unfold tailWord_356512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6501530442212693123607895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8668707256283590831477193 6501530442212693123607895)
  ·
    refine ⟨9752295663319039685411843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6501530442212693123607895 9752295663319039685411843)
    ·
      refine ⟨14628443494978559528117765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9752295663319039685411843 14628443494978559528117765)
      ·
        refine ⟨2742833155308479911522081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14628443494978559528117765 2742833155308479911522081)
        ·
          refine ⟨2057124866481359933641561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2742833155308479911522081 2057124866481359933641561)
          ·
            refine ⟨1542843649861019950231171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2057124866481359933641561 1542843649861019950231171)
            ·
              refine ⟨2314265474791529925346757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1542843649861019950231171 2314265474791529925346757)
              ·
                refine ⟨433924776523411861002517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2314265474791529925346757 433924776523411861002517)
                ·
                  refine ⟨20340223899534930984493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 433924776523411861002517 20340223899534930984493)
                  ·
                    rfl

theorem cell23_356512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 6].length) (baseStart_356512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356512 prefixEnd_356512 := by exact prefixLift 356512
  have htrace : WordTrace (prefixWord ++ tailWord_356512) baseStart_356512 baseEnd_356512 := by
    simpa [prefixWord, tailWord_356512, baseEnd_356512] using wordTrace_append hprefix tailTrace_356512
  have hstable : (prefixWord ++ tailWord_356512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356512).length < 2 ^ (prefixWord ++ tailWord_356512).sum := by decide
  have hdescent : baseEnd_356512 < baseStart_356512 := by decide
  rcases family_descends (prefixWord ++ tailWord_356512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356539 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 3, 1, 3]
def baseStart_356539 : Nat := 118140960795 + 356539 * 2 ^ 59
def prefixEnd_356539 : Nat := 4983230072969 + 3 ^ 40 * 356539 * 2
def baseEnd_356539 : Nat := 183075879073485773222813

theorem tailTrace_356539 : CollatzResearch.WordTrace tailWord_356539 prefixEnd_356539 183075879073485773222813 := by
  unfold tailWord_356539
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004045655327569858448671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8669363770218379905632447 13004045655327569858448671)
  ·
    refine ⟨19506068482991354787673007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13004045655327569858448671 19506068482991354787673007)
    ·
      refine ⟨29259102724487032181509511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19506068482991354787673007 29259102724487032181509511)
      ·
        refine ⟨43888654086730548272264267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29259102724487032181509511 43888654086730548272264267)
        ·
          refine ⟨65832981130095822408396401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43888654086730548272264267 65832981130095822408396401)
          ·
            refine ⟨49374735847571866806297301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65832981130095822408396401 49374735847571866806297301)
            ·
              refine ⟨1157220371427465628272593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49374735847571866806297301 1157220371427465628272593)
              ·
                refine ⟨867915278570599221204445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1157220371427465628272593 867915278570599221204445)
                ·
                  refine ⟨325468229463974707951667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867915278570599221204445 325468229463974707951667)
                  ·
                    refine ⟨488202344195962061927501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 325468229463974707951667 488202344195962061927501)
                    ·
                      refine ⟨183075879073485773222813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 488202344195962061927501 183075879073485773222813)
                      ·
                        rfl

theorem cell23_356539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 1, 3].length) (baseStart_356539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356539 prefixEnd_356539 := by exact prefixLift 356539
  have htrace : WordTrace (prefixWord ++ tailWord_356539) baseStart_356539 baseEnd_356539 := by
    simpa [prefixWord, tailWord_356539, baseEnd_356539] using wordTrace_append hprefix tailTrace_356539
  have hstable : (prefixWord ++ tailWord_356539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356539).length < 2 ^ (prefixWord ++ tailWord_356539).sum := by decide
  have hdescent : baseEnd_356539 < baseStart_356539 := by decide
  rcases family_descends (prefixWord ++ tailWord_356539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356573 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_356573 : Nat := 118140960795 + 356573 * 2 ^ 59
def prefixEnd_356573 : Nat := 4983230072969 + 3 ^ 40 * 356573 * 2
def baseEnd_356573 : Nat := 183093337415738640197657

theorem tailTrace_356573 : CollatzResearch.WordTrace tailWord_356573 prefixEnd_356573 183093337415738640197657 := by
  unfold tailWord_356573
  simp only [CollatzResearch.WordTrace]
  refine ⟨13005285737204393665186373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8670190491469595776790915 13005285737204393665186373)
  ·
    refine ⟨2438491075725823812222445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13005285737204393665186373 2438491075725823812222445)
    ·
      refine ⟨914434153397183929583417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2438491075725823812222445 914434153397183929583417)
      ·
        refine ⟨685825615047887947187563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 914434153397183929583417 685825615047887947187563)
        ·
          refine ⟨1028738422571831920781345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685825615047887947187563 1028738422571831920781345)
          ·
            refine ⟨771553816928873940586009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028738422571831920781345 771553816928873940586009)
            ·
              refine ⟨578665362696655455439507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771553816928873940586009 578665362696655455439507)
              ·
                refine ⟨867998044044983183159261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578665362696655455439507 867998044044983183159261)
                ·
                  refine ⟨325499266516868693684723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 867998044044983183159261 325499266516868693684723)
                  ·
                    refine ⟨488248899775303040527085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 325499266516868693684723 488248899775303040527085)
                    ·
                      refine ⟨183093337415738640197657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 488248899775303040527085 183093337415738640197657)
                      ·
                        rfl

theorem cell23_356573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_356573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356573 prefixEnd_356573 := by exact prefixLift 356573
  have htrace : WordTrace (prefixWord ++ tailWord_356573) baseStart_356573 baseEnd_356573 := by
    simpa [prefixWord, tailWord_356573, baseEnd_356573] using wordTrace_append hprefix tailTrace_356573
  have hstable : (prefixWord ++ tailWord_356573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356573).length < 2 ^ (prefixWord ++ tailWord_356573).sum := by decide
  have hdescent : baseEnd_356573 < baseStart_356573 := by decide
  rcases family_descends (prefixWord ++ tailWord_356573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356602 : List Nat := [3, 1, 1, 1, 1, 6, 1, 9]
def baseStart_356602 : Nat := 118140960795 + 356602 * 2 ^ 59
def prefixEnd_356602 : Nat := 4983230072969 + 3 ^ 40 * 356602 * 2
def baseEnd_356602 : Nat := 6781786235359963953149

theorem tailTrace_356602 : CollatzResearch.WordTrace tailWord_356602 prefixEnd_356602 6781786235359963953149 := by
  unfold tailWord_356602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3251585863524832904498015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8670895636066221078661373 3251585863524832904498015)
  ·
    refine ⟨4877378795287249356747023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3251585863524832904498015 4877378795287249356747023)
    ·
      refine ⟨7316068192930874035120535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4877378795287249356747023 7316068192930874035120535)
      ·
        refine ⟨10974102289396311052680803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7316068192930874035120535 10974102289396311052680803)
        ·
          refine ⟨16461153434094466579021205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10974102289396311052680803 16461153434094466579021205)
          ·
            refine ⟨771616567223178120891619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16461153434094466579021205 771616567223178120891619)
            ·
              refine ⟨1157424850834767181337429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771616567223178120891619 1157424850834767181337429)
              ·
                refine ⟨6781786235359963953149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1157424850834767181337429 6781786235359963953149)
                ·
                  rfl

theorem cell23_356602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 9].length) (baseStart_356602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356602 prefixEnd_356602 := by exact prefixLift 356602
  have htrace : WordTrace (prefixWord ++ tailWord_356602) baseStart_356602 baseEnd_356602 := by
    simpa [prefixWord, tailWord_356602, baseEnd_356602] using wordTrace_append hprefix tailTrace_356602
  have hstable : (prefixWord ++ tailWord_356602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356602).length < 2 ^ (prefixWord ++ tailWord_356602).sum := by decide
  have hdescent : baseEnd_356602 < baseStart_356602 := by decide
  rcases family_descends (prefixWord ++ tailWord_356602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356613 : List Nat := [1, 3, 1, 1, 2, 1, 2, 7, 1, 2, 2]
def baseStart_356613 : Nat := 118140960795 + 356613 * 2 ^ 59
def prefixEnd_356613 : Nat := 4983230072969 + 3 ^ 40 * 356613 * 2
def baseEnd_356613 : Nat := 183113876641918483697473

theorem tailTrace_356613 : CollatzResearch.WordTrace tailWord_356613 prefixEnd_356613 183113876641918483697473 := by
  unfold tailWord_356613
  simp only [CollatzResearch.WordTrace]
  refine ⟨13006744657059480496642493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8671163104706320331094995 13006744657059480496642493)
  ·
    refine ⟨4877529246397305186240935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13006744657059480496642493 4877529246397305186240935)
    ·
      refine ⟨7316293869595957779361403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4877529246397305186240935 7316293869595957779361403)
      ·
        refine ⟨10974440804393936669042105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7316293869595957779361403 10974440804393936669042105)
        ·
          refine ⟨8230830603295452501781579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10974440804393936669042105 8230830603295452501781579)
          ·
            refine ⟨12346245904943178752672369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8230830603295452501781579 12346245904943178752672369)
            ·
              refine ⟨9259684428707384064504277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12346245904943178752672369 9259684428707384064504277)
              ·
                refine ⟨217023853797829314011819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9259684428707384064504277 217023853797829314011819)
                ·
                  refine ⟨325535780696743971017729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217023853797829314011819 325535780696743971017729)
                  ·
                    refine ⟨244151835522557978263297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 325535780696743971017729 244151835522557978263297)
                    ·
                      refine ⟨183113876641918483697473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244151835522557978263297 183113876641918483697473)
                      ·
                        rfl

theorem cell23_356613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 1, 2, 2].length) (baseStart_356613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356613 prefixEnd_356613 := by exact prefixLift 356613
  have htrace : WordTrace (prefixWord ++ tailWord_356613) baseStart_356613 baseEnd_356613 := by
    simpa [prefixWord, tailWord_356613, baseEnd_356613] using wordTrace_append hprefix tailTrace_356613
  have hstable : (prefixWord ++ tailWord_356613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356613).length < 2 ^ (prefixWord ++ tailWord_356613).sum := by decide
  have hdescent : baseEnd_356613 < baseStart_356613 := by decide
  rcases family_descends (prefixWord ++ tailWord_356613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356616 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_356616 : Nat := 118140960795 + 356616 * 2 ^ 59
def prefixEnd_356616 : Nat := 4983230072969 + 3 ^ 40 * 356616 * 2
def baseEnd_356616 : Nat := 183115417083881971959959

theorem tailTrace_356616 : CollatzResearch.WordTrace tailWord_356616 prefixEnd_356616 183115417083881971959959 := by
  unfold tailWord_356616
  simp only [CollatzResearch.WordTrace]
  refine ⟨6503427038024306004500851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8671236050699074672667801 6503427038024306004500851)
  ·
    refine ⟨9755140557036459006751277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6503427038024306004500851 9755140557036459006751277)
    ·
      refine ⟨3658177708888672127531729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9755140557036459006751277 3658177708888672127531729)
      ·
        refine ⟨2743633281666504095648797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3658177708888672127531729 2743633281666504095648797)
        ·
          refine ⟨1028862480624939035868299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2743633281666504095648797 1028862480624939035868299)
          ·
            refine ⟨1543293720937408553802449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028862480624939035868299 1543293720937408553802449)
            ·
              refine ⟨1157470290703056415351837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543293720937408553802449 1157470290703056415351837)
              ·
                refine ⟨434051359013646155756939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1157470290703056415351837 434051359013646155756939)
                ·
                  refine ⟨651077038520469233635409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434051359013646155756939 651077038520469233635409)
                  ·
                    refine ⟨488307778890351925226557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 651077038520469233635409 488307778890351925226557)
                    ·
                      refine ⟨183115417083881971959959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 488307778890351925226557 183115417083881971959959)
                      ·
                        rfl

theorem cell23_356616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_356616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356616 prefixEnd_356616 := by exact prefixLift 356616
  have htrace : WordTrace (prefixWord ++ tailWord_356616) baseStart_356616 baseEnd_356616 := by
    simpa [prefixWord, tailWord_356616, baseEnd_356616] using wordTrace_append hprefix tailTrace_356616
  have hstable : (prefixWord ++ tailWord_356616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356616).length < 2 ^ (prefixWord ++ tailWord_356616).sum := by decide
  have hdescent : baseEnd_356616 < baseStart_356616 := by decide
  rcases family_descends (prefixWord ++ tailWord_356616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356632 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 2, 7]
def baseStart_356632 : Nat := 118140960795 + 356632 * 2 ^ 59
def prefixEnd_356632 : Nat := 4983230072969 + 3 ^ 40 * 356632 * 2
def baseEnd_356632 : Nat := 61041210924784636453295

theorem tailTrace_356632 : CollatzResearch.WordTrace tailWord_356632 prefixEnd_356632 61041210924784636453295 := by
  unfold tailWord_356632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6503718821995323370792075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8671625095993764494389433 6503718821995323370792075)
  ·
    refine ⟨9755578232992985056188113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6503718821995323370792075 9755578232992985056188113)
    ·
      refine ⟨7316683674744738792141085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9755578232992985056188113 7316683674744738792141085)
      ·
        refine ⟨2743756378029277047052907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7316683674744738792141085 2743756378029277047052907)
        ·
          refine ⟨4115634567043915570579361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743756378029277047052907 4115634567043915570579361)
          ·
            refine ⟨3086725925282936677934521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4115634567043915570579361 3086725925282936677934521)
            ·
              refine ⟨2315044443962202508450891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3086725925282936677934521 2315044443962202508450891)
              ·
                refine ⟨3472566665943303762676337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2315044443962202508450891 3472566665943303762676337)
                ·
                  refine ⟨2604424999457477822007253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472566665943303762676337 2604424999457477822007253)
                  ·
                    refine ⟨61041210924784636453295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2604424999457477822007253 61041210924784636453295)
                    ·
                      rfl

theorem cell23_356632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_356632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356632 prefixEnd_356632 := by exact prefixLift 356632
  have htrace : WordTrace (prefixWord ++ tailWord_356632) baseStart_356632 baseEnd_356632 := by
    simpa [prefixWord, tailWord_356632, baseEnd_356632] using wordTrace_append hprefix tailTrace_356632
  have hstable : (prefixWord ++ tailWord_356632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356632).length < 2 ^ (prefixWord ++ tailWord_356632).sum := by decide
  have hdescent : baseEnd_356632 < baseStart_356632 := by decide
  rcases family_descends (prefixWord ++ tailWord_356632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356647 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_356647 : Nat := 118140960795 + 356647 * 2 ^ 59
def prefixEnd_356647 : Nat := 4983230072969 + 3 ^ 40 * 356647 * 2
def baseEnd_356647 : Nat := 183131334984171350672317

theorem tailTrace_356647 : CollatzResearch.WordTrace tailWord_356647 prefixEnd_356647 183131334984171350672317 := by
  unfold tailWord_356647
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007984738936304303380195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8671989825957536202253463 13007984738936304303380195)
  ·
    refine ⟨19511977108404456455070293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13007984738936304303380195 19511977108404456455070293)
    ·
      refine ⟨228655981739114724082855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 19511977108404456455070293 228655981739114724082855)
      ·
        refine ⟨342983972608672086124283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228655981739114724082855 342983972608672086124283)
        ·
          refine ⟨514475958913008129186425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342983972608672086124283 514475958913008129186425)
          ·
            refine ⟨385856969184756096889819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514475958913008129186425 385856969184756096889819)
            ·
              refine ⟨578785453777134145334729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385856969184756096889819 578785453777134145334729)
              ·
                refine ⟨434089090332850609001047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578785453777134145334729 434089090332850609001047)
                ·
                  refine ⟨651133635499275913501571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434089090332850609001047 651133635499275913501571)
                  ·
                    refine ⟨976700453248913870252357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 651133635499275913501571 976700453248913870252357)
                    ·
                      refine ⟨183131334984171350672317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 976700453248913870252357 183131334984171350672317)
                      ·
                        rfl

theorem cell23_356647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_356647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356647 prefixEnd_356647 := by exact prefixLift 356647
  have htrace : WordTrace (prefixWord ++ tailWord_356647) baseStart_356647 baseEnd_356647 := by
    simpa [prefixWord, tailWord_356647, baseEnd_356647] using wordTrace_append hprefix tailTrace_356647
  have hstable : (prefixWord ++ tailWord_356647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356647).length < 2 ^ (prefixWord ++ tailWord_356647).sum := by decide
  have hdescent : baseEnd_356647 < baseStart_356647 := by decide
  rcases family_descends (prefixWord ++ tailWord_356647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356650 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_356650 : Nat := 118140960795 + 356650 * 2 ^ 59
def prefixEnd_356650 : Nat := 4983230072969 + 3 ^ 40 * 356650 * 2
def baseEnd_356650 : Nat := 183132875426134838934803

theorem tailTrace_356650 : CollatzResearch.WordTrace tailWord_356650 prefixEnd_356650 183132875426134838934803 := by
  unfold tailWord_356650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3252023539481358953934851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8672062771950290543826269 3252023539481358953934851)
  ·
    refine ⟨4878035309222038430902277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3252023539481358953934851 4878035309222038430902277)
    ·
      refine ⟨914631620479132205794177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4878035309222038430902277 914631620479132205794177)
      ·
        refine ⟨685973715359349154345633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 914631620479132205794177 685973715359349154345633)
        ·
          refine ⟨514480286519511865759225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685973715359349154345633 514480286519511865759225)
          ·
            refine ⟨385860214889633899319419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514480286519511865759225 385860214889633899319419)
            ·
              refine ⟨578790322334450848979129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385860214889633899319419 578790322334450848979129)
              ·
                refine ⟨434092741750838136734347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578790322334450848979129 434092741750838136734347)
                ·
                  refine ⟨651139112626257205101521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434092741750838136734347 651139112626257205101521)
                  ·
                    refine ⟨488354334469692903826141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 651139112626257205101521 488354334469692903826141)
                    ·
                      refine ⟨183132875426134838934803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 488354334469692903826141 183132875426134838934803)
                      ·
                        rfl

theorem cell23_356650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_356650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356650 prefixEnd_356650 := by exact prefixLift 356650
  have htrace : WordTrace (prefixWord ++ tailWord_356650) baseStart_356650 baseEnd_356650 := by
    simpa [prefixWord, tailWord_356650, baseEnd_356650] using wordTrace_append hprefix tailTrace_356650
  have hstable : (prefixWord ++ tailWord_356650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356650).length < 2 ^ (prefixWord ++ tailWord_356650).sum := by decide
  have hdescent : baseEnd_356650 < baseStart_356650 := by decide
  rcases family_descends (prefixWord ++ tailWord_356650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356656 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 1, 3, 2]
def baseStart_356656 : Nat := 118140960795 + 356656 * 2 ^ 59
def prefixEnd_356656 : Nat := 4983230072969 + 3 ^ 40 * 356656 * 2
def baseEnd_356656 : Nat := 183135956310061815459775

theorem tailTrace_356656 : CollatzResearch.WordTrace tailWord_356656 prefixEnd_356656 183135956310061815459775 := by
  unfold tailWord_356656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504156497951849420228911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8672208663935799226971881 6504156497951849420228911)
  ·
    refine ⟨9756234746927774130343367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6504156497951849420228911 9756234746927774130343367)
    ·
      refine ⟨14634352120391661195515051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9756234746927774130343367 14634352120391661195515051)
      ·
        refine ⟨21951528180587491793272577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14634352120391661195515051 21951528180587491793272577)
        ·
          refine ⟨16463646135440618844954433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21951528180587491793272577 16463646135440618844954433)
          ·
            refine ⟨12347734601580464133715825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16463646135440618844954433 12347734601580464133715825)
            ·
              refine ⟨9260800951185348100286869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12347734601580464133715825 9260800951185348100286869)
              ·
                refine ⟨434100044586813192200947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9260800951185348100286869 434100044586813192200947)
                ·
                  refine ⟨651150066880219788301421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434100044586813192200947 651150066880219788301421)
                  ·
                    refine ⟨244181275080082420613033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 651150066880219788301421 244181275080082420613033)
                    ·
                      refine ⟨183135956310061815459775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244181275080082420613033 183135956310061815459775)
                      ·
                        rfl

theorem cell23_356656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 3, 2].length) (baseStart_356656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356656 prefixEnd_356656 := by exact prefixLift 356656
  have htrace : WordTrace (prefixWord ++ tailWord_356656) baseStart_356656 baseEnd_356656 := by
    simpa [prefixWord, tailWord_356656, baseEnd_356656] using wordTrace_append hprefix tailTrace_356656
  have hstable : (prefixWord ++ tailWord_356656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356656).length < 2 ^ (prefixWord ++ tailWord_356656).sum := by decide
  have hdescent : baseEnd_356656 < baseStart_356656 := by decide
  rcases family_descends (prefixWord ++ tailWord_356656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356672 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_356672 : Nat := 118140960795 + 356672 * 2 ^ 59
def prefixEnd_356672 : Nat := 4983230072969 + 3 ^ 40 * 356672 * 2
def baseEnd_356672 : Nat := 183144172000533752859701

theorem tailTrace_356672 : CollatzResearch.WordTrace tailWord_356672 prefixEnd_356672 183144172000533752859701 := by
  unfold tailWord_356672
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504448281922866786520135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8672597709230489048693513 6504448281922866786520135)
  ·
    refine ⟨9756672422884300179780203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6504448281922866786520135 9756672422884300179780203)
    ·
      refine ⟨14635008634326450269670305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9756672422884300179780203 14635008634326450269670305)
      ·
        refine ⟨10976256475744837702252729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14635008634326450269670305 10976256475744837702252729)
        ·
          refine ⟨8232192356808628276689547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10976256475744837702252729 8232192356808628276689547)
          ·
            refine ⟨12348288535212942415034321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8232192356808628276689547 12348288535212942415034321)
            ·
              refine ⟨9261216401409706811275741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12348288535212942415034321 9261216401409706811275741)
              ·
                refine ⟨3472956150528640054228403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9261216401409706811275741 3472956150528640054228403)
                ·
                  refine ⟨5209434225792960081342605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472956150528640054228403 5209434225792960081342605)
                  ·
                    refine ⟨1953537834672360030503477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5209434225792960081342605 1953537834672360030503477)
                    ·
                      refine ⟨183144172000533752859701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1953537834672360030503477 183144172000533752859701)
                      ·
                        rfl

theorem cell23_356672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_356672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356672 prefixEnd_356672 := by exact prefixLift 356672
  have htrace : WordTrace (prefixWord ++ tailWord_356672) baseStart_356672 baseEnd_356672 := by
    simpa [prefixWord, tailWord_356672, baseEnd_356672] using wordTrace_append hprefix tailTrace_356672
  have hstable : (prefixWord ++ tailWord_356672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356672).length < 2 ^ (prefixWord ++ tailWord_356672).sum := by decide
  have hdescent : baseEnd_356672 < baseStart_356672 := by decide
  rcases family_descends (prefixWord ++ tailWord_356672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356682 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_356682 : Nat := 118140960795 + 356682 * 2 ^ 59
def prefixEnd_356682 : Nat := 4983230072969 + 3 ^ 40 * 356682 * 2
def baseEnd_356682 : Nat := 183149306807078713734655

theorem tailTrace_356682 : CollatzResearch.WordTrace tailWord_356682 prefixEnd_356682 183149306807078713734655 := by
  unfold tailWord_356682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3252315323452376320226075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8672840862539670187269533 3252315323452376320226075)
  ·
    refine ⟨4878472985178564480339113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3252315323452376320226075 4878472985178564480339113)
    ·
      refine ⟨3658854738883923360254335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4878472985178564480339113 3658854738883923360254335)
      ·
        refine ⟨5488282108325885040381503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3658854738883923360254335 5488282108325885040381503)
        ·
          refine ⟨8232423162488827560572255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5488282108325885040381503 8232423162488827560572255)
          ·
            refine ⟨12348634743733241340858383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8232423162488827560572255 12348634743733241340858383)
            ·
              refine ⟨18522952115599862011287575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12348634743733241340858383 18522952115599862011287575)
              ·
                refine ⟨27784428173399793016931363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18522952115599862011287575 27784428173399793016931363)
                ·
                  refine ⟨41676642260099689525397045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27784428173399793016931363 41676642260099689525397045)
                  ·
                    refine ⟨3907185211884345893005973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41676642260099689525397045 3907185211884345893005973)
                    ·
                      refine ⟨183149306807078713734655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3907185211884345893005973 183149306807078713734655)
                      ·
                        rfl

theorem cell23_356682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_356682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356682 prefixEnd_356682 := by exact prefixLift 356682
  have htrace : WordTrace (prefixWord ++ tailWord_356682) baseStart_356682 baseEnd_356682 := by
    simpa [prefixWord, tailWord_356682, baseEnd_356682] using wordTrace_append hprefix tailTrace_356682
  have hstable : (prefixWord ++ tailWord_356682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356682).length < 2 ^ (prefixWord ++ tailWord_356682).sum := by decide
  have hdescent : baseEnd_356682 < baseStart_356682 := by decide
  rcases family_descends (prefixWord ++ tailWord_356682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356689 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 2, 4, 3]
def baseStart_356689 : Nat := 118140960795 + 356689 * 2 ^ 59
def prefixEnd_356689 : Nat := 4983230072969 + 3 ^ 40 * 356689 * 2
def baseEnd_356689 : Nat := 183152901171660186347123

theorem tailTrace_356689 : CollatzResearch.WordTrace tailWord_356689 prefixEnd_356689 183152901171660186347123 := by
  unfold tailWord_356689
  simp only [CollatzResearch.WordTrace]
  refine ⟨13009516604784145476409121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8673011069856096984272747 13009516604784145476409121)
  ·
    refine ⟨9757137453588109107306841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13009516604784145476409121 9757137453588109107306841)
    ·
      refine ⟨7317853090191081830480131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9757137453588109107306841 7317853090191081830480131)
      ·
        refine ⟨10976779635286622745720197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7317853090191081830480131 10976779635286622745720197)
        ·
          refine ⟨2058146181616241764822537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10976779635286622745720197 2058146181616241764822537)
          ·
            refine ⟨1543609636212181323616903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2058146181616241764822537 1543609636212181323616903)
            ·
              refine ⟨2315414454318271985425355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543609636212181323616903 2315414454318271985425355)
              ·
                refine ⟨3473121681477407978138033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2315414454318271985425355 3473121681477407978138033)
                ·
                  refine ⟨2604841261108055983603525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3473121681477407978138033 2604841261108055983603525)
                  ·
                    refine ⟨488407736457760496925661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2604841261108055983603525 488407736457760496925661)
                    ·
                      refine ⟨183152901171660186347123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 488407736457760496925661 183152901171660186347123)
                      ·
                        rfl

theorem cell23_356689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_356689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356689 prefixEnd_356689 := by exact prefixLift 356689
  have htrace : WordTrace (prefixWord ++ tailWord_356689) baseStart_356689 baseEnd_356689 := by
    simpa [prefixWord, tailWord_356689, baseEnd_356689] using wordTrace_append hprefix tailTrace_356689
  have hstable : (prefixWord ++ tailWord_356689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356689).length < 2 ^ (prefixWord ++ tailWord_356689).sum := by decide
  have hdescent : baseEnd_356689 < baseStart_356689 := by decide
  rcases family_descends (prefixWord ++ tailWord_356689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356703 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 2, 2, 2]
def baseStart_356703 : Nat := 118140960795 + 356703 * 2 ^ 59
def prefixEnd_356703 : Nat := 4983230072969 + 3 ^ 40 * 356703 * 2
def baseEnd_356703 : Nat := 183160089900823131572059

theorem tailTrace_356703 : CollatzResearch.WordTrace tailWord_356703 prefixEnd_356703 183160089900823131572059 := by
  unfold tailWord_356703
  simp only [CollatzResearch.WordTrace]
  refine ⟨13010027226733425867418763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8673351484488950578279175 13010027226733425867418763)
  ·
    refine ⟨19515040840100138801128145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13010027226733425867418763 19515040840100138801128145)
    ·
      refine ⟨14636280630075104100846109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19515040840100138801128145 14636280630075104100846109)
      ·
        refine ⟨5488605236278164037817291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14636280630075104100846109 5488605236278164037817291)
        ·
          refine ⟨8232907854417246056725937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5488605236278164037817291 8232907854417246056725937)
          ·
            refine ⟨6174680890812934542544453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8232907854417246056725937 6174680890812934542544453)
            ·
              refine ⟨1157752667027425226727085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6174680890812934542544453 1157752667027425226727085)
              ·
                refine ⟨434157250135284460022657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1157752667027425226727085 434157250135284460022657)
                ·
                  refine ⟨325617937601463345016993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434157250135284460022657 325617937601463345016993)
                  ·
                    refine ⟨244213453201097508762745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 325617937601463345016993 244213453201097508762745)
                    ·
                      refine ⟨183160089900823131572059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244213453201097508762745 183160089900823131572059)
                      ·
                        rfl

theorem cell23_356703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_356703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356703 prefixEnd_356703 := by exact prefixLift 356703
  have htrace : WordTrace (prefixWord ++ tailWord_356703) baseStart_356703 baseEnd_356703 := by
    simpa [prefixWord, tailWord_356703, baseEnd_356703] using wordTrace_append hprefix tailTrace_356703
  have hstable : (prefixWord ++ tailWord_356703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356703).length < 2 ^ (prefixWord ++ tailWord_356703).sum := by decide
  have hdescent : baseEnd_356703 < baseStart_356703 := by decide
  rcases family_descends (prefixWord ++ tailWord_356703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356709 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 7]
def baseStart_356709 : Nat := 118140960795 + 356709 * 2 ^ 59
def prefixEnd_356709 : Nat := 4983230072969 + 3 ^ 40 * 356709 * 2
def baseEnd_356709 : Nat := 20351463420527789788559

theorem tailTrace_356709 : CollatzResearch.WordTrace tailWord_356709 prefixEnd_356709 20351463420527789788559 := by
  unfold tailWord_356709
  simp only [CollatzResearch.WordTrace]
  refine ⟨13010246064711688892137181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8673497376474459261424787 13010246064711688892137181)
  ·
    refine ⟨4878842274266883334551443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13010246064711688892137181 4878842274266883334551443)
    ·
      refine ⟨7318263411400325001827165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4878842274266883334551443 7318263411400325001827165)
      ·
        refine ⟨2744348779275121875685187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7318263411400325001827165 2744348779275121875685187)
        ·
          refine ⟨4116523168912682813527781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2744348779275121875685187 4116523168912682813527781)
          ·
            refine ⟨771848094171128027536459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4116523168912682813527781 771848094171128027536459)
            ·
              refine ⟨1157772141256692041304689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771848094171128027536459 1157772141256692041304689)
              ·
                refine ⟨868329105942519030978517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1157772141256692041304689 868329105942519030978517)
                ·
                  refine ⟨20351463420527789788559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 868329105942519030978517 20351463420527789788559)
                  ·
                    rfl

theorem cell23_356709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_356709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356709 prefixEnd_356709 := by exact prefixLift 356709
  have htrace : WordTrace (prefixWord ++ tailWord_356709) baseStart_356709 baseEnd_356709 := by
    simpa [prefixWord, tailWord_356709, baseEnd_356709] using wordTrace_append hprefix tailTrace_356709
  have hstable : (prefixWord ++ tailWord_356709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356709).length < 2 ^ (prefixWord ++ tailWord_356709).sum := by decide
  have hdescent : baseEnd_356709 < baseStart_356709 := by decide
  rcases family_descends (prefixWord ++ tailWord_356709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356737 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_356737 : Nat := 118140960795 + 356737 * 2 ^ 59
def prefixEnd_356737 : Nat := 4983230072969 + 3 ^ 40 * 356737 * 2
def baseEnd_356737 : Nat := 183177548243075998546903

theorem tailTrace_356737 : CollatzResearch.WordTrace tailWord_356737 prefixEnd_356737 183177548243075998546903 := by
  unfold tailWord_356737
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011267308610249674156465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8674178205740166449437643 13011267308610249674156465)
  ·
    refine ⟨9758450481457687255617349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13011267308610249674156465 9758450481457687255617349)
    ·
      refine ⟨1829709465273316360428253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9758450481457687255617349 1829709465273316360428253)
      ·
        refine ⟨686141049477493635160595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1829709465273316360428253 686141049477493635160595)
        ·
          refine ⟨1029211574216240452740893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686141049477493635160595 1029211574216240452740893)
          ·
            refine ⟨385954340331090169777835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1029211574216240452740893 385954340331090169777835)
            ·
              refine ⟨578931510496635254666753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385954340331090169777835 578931510496635254666753)
              ·
                refine ⟨434198632872476441000065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578931510496635254666753 434198632872476441000065)
                ·
                  refine ⟨325648974654357330750049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434198632872476441000065 325648974654357330750049)
                  ·
                    refine ⟨244236730990767998062537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 325648974654357330750049 244236730990767998062537)
                    ·
                      refine ⟨183177548243075998546903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244236730990767998062537 183177548243075998546903)
                      ·
                        rfl

theorem cell23_356737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_356737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356737 prefixEnd_356737 := by exact prefixLift 356737
  have htrace : WordTrace (prefixWord ++ tailWord_356737) baseStart_356737 baseEnd_356737 := by
    simpa [prefixWord, tailWord_356737, baseEnd_356737] using wordTrace_append hprefix tailTrace_356737
  have hstable : (prefixWord ++ tailWord_356737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356737).length < 2 ^ (prefixWord ++ tailWord_356737).sum := by decide
  have hdescent : baseEnd_356737 < baseStart_356737 := by decide
  rcases family_descends (prefixWord ++ tailWord_356737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356759 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_356759 : Nat := 118140960795 + 356759 * 2 ^ 59
def prefixEnd_356759 : Nat := 4983230072969 + 3 ^ 40 * 356759 * 2
def baseEnd_356759 : Nat := 183188844817474912471801

theorem tailTrace_356759 : CollatzResearch.WordTrace tailWord_356759 prefixEnd_356759 183188844817474912471801 := by
  unfold tailWord_356759
  simp only [CollatzResearch.WordTrace]
  refine ⟨13012069714530547431457331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8674713143020364954304887 13012069714530547431457331)
  ·
    refine ⟨19518104571795821147185997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13012069714530547431457331 19518104571795821147185997)
    ·
      refine ⟨7319289214423432930194749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19518104571795821147185997 7319289214423432930194749)
      ·
        refine ⟨2744733455408787348823031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7319289214423432930194749 2744733455408787348823031)
        ·
          refine ⟨4117100183113181023234547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2744733455408787348823031 4117100183113181023234547)
          ·
            refine ⟨6175650274669771534851821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117100183113181023234547 6175650274669771534851821)
            ·
              refine ⟨2315868853001164325569433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6175650274669771534851821 2315868853001164325569433)
              ·
                refine ⟨1736901639750873244177075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2315868853001164325569433 1736901639750873244177075)
                ·
                  refine ⟨2605352459626309866265613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736901639750873244177075 2605352459626309866265613)
                  ·
                    refine ⟨977007172359866199849605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2605352459626309866265613 977007172359866199849605)
                    ·
                      refine ⟨183188844817474912471801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 977007172359866199849605 183188844817474912471801)
                      ·
                        rfl

theorem cell23_356759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_356759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356759 prefixEnd_356759 := by exact prefixLift 356759
  have htrace : WordTrace (prefixWord ++ tailWord_356759) baseStart_356759 baseEnd_356759 := by
    simpa [prefixWord, tailWord_356759, baseEnd_356759] using wordTrace_append hprefix tailTrace_356759
  have hstable : (prefixWord ++ tailWord_356759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356759).length < 2 ^ (prefixWord ++ tailWord_356759).sum := by decide
  have hdescent : baseEnd_356759 < baseStart_356759 := by decide
  rcases family_descends (prefixWord ++ tailWord_356759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356876 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_356876 : Nat := 118140960795 + 356876 * 2 ^ 59
def prefixEnd_356876 : Nat := 4983230072969 + 3 ^ 40 * 356876 * 2
def baseEnd_356876 : Nat := 61082974018016984902921

theorem tailTrace_356876 : CollatzResearch.WordTrace tailWord_356876 prefixEnd_356876 61082974018016984902921 := by
  unfold tailWord_356876
  simp only [CollatzResearch.WordTrace]
  refine ⟨6508168527553338206733241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8677558036737784275644321 6508168527553338206733241)
  ·
    refine ⟨4881126395665003655049931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6508168527553338206733241 4881126395665003655049931)
    ·
      refine ⟨7321689593497505482574897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4881126395665003655049931 7321689593497505482574897)
      ·
        refine ⟨5491267195123129111931173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7321689593497505482574897 5491267195123129111931173)
        ·
          refine ⟨1029612599085586708487095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5491267195123129111931173 1029612599085586708487095)
          ·
            refine ⟨1544418898628380062730643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029612599085586708487095 1544418898628380062730643)
            ·
              refine ⟨2316628347942570094095965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544418898628380062730643 2316628347942570094095965)
              ·
                refine ⟨868735630478463785285987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2316628347942570094095965 868735630478463785285987)
                ·
                  refine ⟨1303103445717695677928981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868735630478463785285987 1303103445717695677928981)
                  ·
                    refine ⟨61082974018016984902921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1303103445717695677928981 61082974018016984902921)
                    ·
                      rfl

theorem cell23_356876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_356876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356876 prefixEnd_356876 := by exact prefixLift 356876
  have htrace : WordTrace (prefixWord ++ tailWord_356876) baseStart_356876 baseEnd_356876 := by
    simpa [prefixWord, tailWord_356876, baseEnd_356876] using wordTrace_append hprefix tailTrace_356876
  have hstable : (prefixWord ++ tailWord_356876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356876).length < 2 ^ (prefixWord ++ tailWord_356876).sum := by decide
  have hdescent : baseEnd_356876 < baseStart_356876 := by decide
  rcases family_descends (prefixWord ++ tailWord_356876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356877 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_356877 : Nat := 118140960795 + 356877 * 2 ^ 59
def prefixEnd_356877 : Nat := 4983230072969 + 3 ^ 40 * 356877 * 2
def baseEnd_356877 : Nat := 183249435534705450796259

theorem tailTrace_356877 : CollatzResearch.WordTrace tailWord_356877 prefixEnd_356877 183249435534705450796259 := by
  unfold tailWord_356877
  simp only [CollatzResearch.WordTrace]
  refine ⟨13016373528103053584252885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8677582352068702389501923 13016373528103053584252885)
  ·
    refine ⟨305071254564915318380927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13016373528103053584252885 305071254564915318380927)
    ·
      refine ⟨457606881847372977571391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305071254564915318380927 457606881847372977571391)
      ·
        refine ⟨686410322771059466357087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457606881847372977571391 686410322771059466357087)
        ·
          refine ⟨1029615484156589199535631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686410322771059466357087 1029615484156589199535631)
          ·
            refine ⟨1544423226234883799303447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029615484156589199535631 1544423226234883799303447)
            ·
              refine ⟨2316634839352325698955171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544423226234883799303447 2316634839352325698955171)
              ·
                refine ⟨3474952259028488548432757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316634839352325698955171 3474952259028488548432757)
                ·
                  refine ⟨325776774283920801415571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3474952259028488548432757 325776774283920801415571)
                  ·
                    refine ⟨488665161425881202123357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 325776774283920801415571 488665161425881202123357)
                    ·
                      refine ⟨183249435534705450796259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 488665161425881202123357 183249435534705450796259)
                      ·
                        rfl

theorem cell23_356877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_356877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356877 prefixEnd_356877 := by exact prefixLift 356877
  have htrace : WordTrace (prefixWord ++ tailWord_356877) baseStart_356877 baseEnd_356877 := by
    simpa [prefixWord, tailWord_356877, baseEnd_356877] using wordTrace_append hprefix tailTrace_356877
  have hstable : (prefixWord ++ tailWord_356877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356877).length < 2 ^ (prefixWord ++ tailWord_356877).sum := by decide
  have hdescent : baseEnd_356877 < baseStart_356877 := by decide
  rcases family_descends (prefixWord ++ tailWord_356877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356906 : List Nat := [3, 1, 4, 1, 1, 3, 10]
def baseStart_356906 : Nat := 118140960795 + 356906 * 2 ^ 59
def prefixEnd_356906 : Nat := 4983230072969 + 3 ^ 40 * 356906 * 2
def baseEnd_356906 : Nat := 2262522549057849843625

theorem tailTrace_356906 : CollatzResearch.WordTrace tailWord_356906 prefixEnd_356906 2262522549057849843625 := by
  unfold tailWord_356906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254357811249497884264643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8678287496665327691372381 3254357811249497884264643)
  ·
    refine ⟨4881536716874246826396965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254357811249497884264643 4881536716874246826396965)
    ·
      refine ⟨915288134413921279949431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4881536716874246826396965 915288134413921279949431)
      ·
        refine ⟨1372932201620881919924147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915288134413921279949431 1372932201620881919924147)
        ·
          refine ⟨2059398302431322879886221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372932201620881919924147 2059398302431322879886221)
          ·
            refine ⟨772274363411746079957333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2059398302431322879886221 772274363411746079957333)
            ·
              refine ⟨2262522549057849843625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 772274363411746079957333 2262522549057849843625)
              ·
                rfl

theorem cell23_356906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 10].length) (baseStart_356906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356906 prefixEnd_356906 := by exact prefixLift 356906
  have htrace : WordTrace (prefixWord ++ tailWord_356906) baseStart_356906 baseEnd_356906 := by
    simpa [prefixWord, tailWord_356906, baseEnd_356906] using wordTrace_append hprefix tailTrace_356906
  have hstable : (prefixWord ++ tailWord_356906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356906).length < 2 ^ (prefixWord ++ tailWord_356906).sum := by decide
  have hdescent : baseEnd_356906 < baseStart_356906 := by decide
  rcases family_descends (prefixWord ++ tailWord_356906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356910 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_356910 : Nat := 118140960795 + 356910 * 2 ^ 59
def prefixEnd_356910 : Nat := 4983230072969 + 3 ^ 40 * 356910 * 2
def baseEnd_356910 : Nat := 61088793465434607227869

theorem tailTrace_356910 : CollatzResearch.WordTrace tailWord_356910 prefixEnd_356910 61088793465434607227869 := by
  unfold tailWord_356910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1627197142122937527525523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8678384757989000146802789 1627197142122937527525523)
  ·
    refine ⟨2440795713184406291288285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1627197142122937527525523 2440795713184406291288285)
    ·
      refine ⟨915298392444152359233107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2440795713184406291288285 915298392444152359233107)
      ·
        refine ⟨1372947588666228538849661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915298392444152359233107 1372947588666228538849661)
        ·
          refine ⟨514855345749835702068623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1372947588666228538849661 514855345749835702068623)
          ·
            refine ⟨772283018624753553102935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514855345749835702068623 772283018624753553102935)
            ·
              refine ⟨1158424527937130329654403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772283018624753553102935 1158424527937130329654403)
              ·
                refine ⟨1737636791905695494481605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158424527937130329654403 1737636791905695494481605)
                ·
                  refine ⟨325806898482317905215301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1737636791905695494481605 325806898482317905215301)
                  ·
                    refine ⟨61088793465434607227869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 325806898482317905215301 61088793465434607227869)
                    ·
                      rfl

theorem cell23_356910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_356910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356910 prefixEnd_356910 := by exact prefixLift 356910
  have htrace : WordTrace (prefixWord ++ tailWord_356910) baseStart_356910 baseEnd_356910 := by
    simpa [prefixWord, tailWord_356910, baseEnd_356910] using wordTrace_append hprefix tailTrace_356910
  have hstable : (prefixWord ++ tailWord_356910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356910).length < 2 ^ (prefixWord ++ tailWord_356910).sum := by decide
  have hdescent : baseEnd_356910 < baseStart_356910 := by decide
  rcases family_descends (prefixWord ++ tailWord_356910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356917 : List Nat := [1, 3, 3, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_356917 : Nat := 118140960795 + 356917 * 2 ^ 59
def prefixEnd_356917 : Nat := 4983230072969 + 3 ^ 40 * 356917 * 2
def baseEnd_356917 : Nat := 183269974760885294296075

theorem tailTrace_356917 : CollatzResearch.WordTrace tailWord_356917 prefixEnd_356917 183269974760885294296075 := by
  unfold tailWord_356917
  simp only [CollatzResearch.WordTrace]
  refine ⟨13017832447958140415709005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8678554965305426943806003 13017832447958140415709005)
  ·
    refine ⟨4881687167984302655890877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13017832447958140415709005 4881687167984302655890877)
    ·
      refine ⟨1830632687994113495959079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4881687167984302655890877 1830632687994113495959079)
      ·
        refine ⟨2745949031991170243938619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1830632687994113495959079 2745949031991170243938619)
        ·
          refine ⟨4118923547986755365907929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2745949031991170243938619 4118923547986755365907929)
          ·
            refine ⟨3089192660990066524430947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4118923547986755365907929 3089192660990066524430947)
            ·
              refine ⟨4633788991485099786646421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089192660990066524430947 4633788991485099786646421)
              ·
                refine ⟨217208858975864052499051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4633788991485099786646421 217208858975864052499051)
                ·
                  refine ⟨325813288463796078748577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217208858975864052499051 325813288463796078748577)
                  ·
                    refine ⟨244359966347847059061433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 325813288463796078748577 244359966347847059061433)
                    ·
                      refine ⟨183269974760885294296075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244359966347847059061433 183269974760885294296075)
                      ·
                        rfl

theorem cell23_356917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_356917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356917 prefixEnd_356917 := by exact prefixLift 356917
  have htrace : WordTrace (prefixWord ++ tailWord_356917) baseStart_356917 baseEnd_356917 := by
    simpa [prefixWord, tailWord_356917, baseEnd_356917] using wordTrace_append hprefix tailTrace_356917
  have hstable : (prefixWord ++ tailWord_356917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356917).length < 2 ^ (prefixWord ++ tailWord_356917).sum := by decide
  have hdescent : baseEnd_356917 < baseStart_356917 := by decide
  rcases family_descends (prefixWord ++ tailWord_356917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356933 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 3]
def baseStart_356933 : Nat := 118140960795 + 356933 * 2 ^ 59
def prefixEnd_356933 : Nat := 4983230072969 + 3 ^ 40 * 356933 * 2
def baseEnd_356933 : Nat := 183278190451357231696001

theorem tailTrace_356933 : CollatzResearch.WordTrace tailWord_356933 prefixEnd_356933 183278190451357231696001 := by
  unfold tailWord_356933
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018416015900175148291453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8678944010600116765527635 13018416015900175148291453)
  ·
    refine ⟨4881906005962565680609295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13018416015900175148291453 4881906005962565680609295)
    ·
      refine ⟨7322859008943848520913943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4881906005962565680609295 7322859008943848520913943)
      ·
        refine ⟨10984288513415772781370915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7322859008943848520913943 10984288513415772781370915)
        ·
          refine ⟨16476432770123659172056373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10984288513415772781370915 16476432770123659172056373)
          ·
            refine ⟨1544665572199093047380285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16476432770123659172056373 1544665572199093047380285)
            ·
              refine ⟨579249589574659892767607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1544665572199093047380285 579249589574659892767607)
              ·
                refine ⟨868874384361989839151411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579249589574659892767607 868874384361989839151411)
                ·
                  refine ⟨1303311576542984758727117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868874384361989839151411 1303311576542984758727117)
                  ·
                    refine ⟨488741841203619284522669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1303311576542984758727117 488741841203619284522669)
                    ·
                      refine ⟨183278190451357231696001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 488741841203619284522669 183278190451357231696001)
                      ·
                        rfl

theorem cell23_356933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_356933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356933 prefixEnd_356933 := by exact prefixLift 356933
  have htrace : WordTrace (prefixWord ++ tailWord_356933) baseStart_356933 baseEnd_356933 := by
    simpa [prefixWord, tailWord_356933, baseEnd_356933] using wordTrace_append hprefix tailTrace_356933
  have hstable : (prefixWord ++ tailWord_356933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356933).length < 2 ^ (prefixWord ++ tailWord_356933).sum := by decide
  have hdescent : baseEnd_356933 < baseStart_356933 := by decide
  rcases family_descends (prefixWord ++ tailWord_356933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356934 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_356934 : Nat := 118140960795 + 356934 * 2 ^ 59
def prefixEnd_356934 : Nat := 4983230072969 + 3 ^ 40 * 356934 * 2
def baseEnd_356934 : Nat := 183278703932011727783497

theorem tailTrace_356934 : CollatzResearch.WordTrace tailWord_356934 prefixEnd_356934 183278703932011727783497 := by
  unfold tailWord_356934
  simp only [CollatzResearch.WordTrace]
  refine ⟨406826640278017259971183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8678968325931034879385237 406826640278017259971183)
  ·
    refine ⟨610239960417025889956775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 406826640278017259971183 610239960417025889956775)
    ·
      refine ⟨915359940625538834935163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610239960417025889956775 915359940625538834935163)
      ·
        refine ⟨1373039910938308252402745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915359940625538834935163 1373039910938308252402745)
        ·
          refine ⟨1029779933203731189302059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1373039910938308252402745 1029779933203731189302059)
          ·
            refine ⟨1544669899805596783953089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029779933203731189302059 1544669899805596783953089)
            ·
              refine ⟨1158502424854197587964817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1544669899805596783953089 1158502424854197587964817)
              ·
                refine ⟨868876818640648190973613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1158502424854197587964817 868876818640648190973613)
                ·
                  refine ⟨325828806990243071615105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 868876818640648190973613 325828806990243071615105)
                  ·
                    refine ⟨244371605242682303711329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 325828806990243071615105 244371605242682303711329)
                    ·
                      refine ⟨183278703932011727783497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244371605242682303711329 183278703932011727783497)
                      ·
                        rfl

theorem cell23_356934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_356934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356934 prefixEnd_356934 := by exact prefixLift 356934
  have htrace : WordTrace (prefixWord ++ tailWord_356934) baseStart_356934 baseEnd_356934 := by
    simpa [prefixWord, tailWord_356934, baseEnd_356934] using wordTrace_append hprefix tailTrace_356934
  have hstable : (prefixWord ++ tailWord_356934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356934).length < 2 ^ (prefixWord ++ tailWord_356934).sum := by decide
  have hdescent : baseEnd_356934 < baseStart_356934 := by decide
  rcases family_descends (prefixWord ++ tailWord_356934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356943 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 3, 3, 2]
def baseStart_356943 : Nat := 118140960795 + 356943 * 2 ^ 59
def prefixEnd_356943 : Nat := 4983230072969 + 3 ^ 40 * 356943 * 2
def baseEnd_356943 : Nat := 183283325257902192570955

theorem tailTrace_356943 : CollatzResearch.WordTrace tailWord_356943 prefixEnd_356943 183283325257902192570955 := by
  unfold tailWord_356943
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018780745863946856155483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8679187163909297904103655 13018780745863946856155483)
  ·
    refine ⟨19528171118795920284233225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13018780745863946856155483 19528171118795920284233225)
    ·
      refine ⟨14646128339096940213174919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19528171118795920284233225 14646128339096940213174919)
      ·
        refine ⟨21969192508645410319762379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14646128339096940213174919 21969192508645410319762379)
        ·
          refine ⟨32953788762968115479643569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21969192508645410319762379 32953788762968115479643569)
          ·
            refine ⟨24715341572226086609732677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32953788762968115479643569 24715341572226086609732677)
            ·
              refine ⟨4634126544792391239324877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24715341572226086609732677 4634126544792391239324877)
              ·
                refine ⟨1737797454297146714746829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4634126544792391239324877 1737797454297146714746829)
                ·
                  refine ⟨651674045361430018030061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1737797454297146714746829 651674045361430018030061)
                  ·
                    refine ⟨244377767010536256761273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 651674045361430018030061 244377767010536256761273)
                    ·
                      refine ⟨183283325257902192570955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244377767010536256761273 183283325257902192570955)
                      ·
                        rfl

theorem cell23_356943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 3, 2].length) (baseStart_356943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356943 prefixEnd_356943 := by exact prefixLift 356943
  have htrace : WordTrace (prefixWord ++ tailWord_356943) baseStart_356943 baseEnd_356943 := by
    simpa [prefixWord, tailWord_356943, baseEnd_356943] using wordTrace_append hprefix tailTrace_356943
  have hstable : (prefixWord ++ tailWord_356943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356943).length < 2 ^ (prefixWord ++ tailWord_356943).sum := by decide
  have hdescent : baseEnd_356943 < baseStart_356943 := by decide
  rcases family_descends (prefixWord ++ tailWord_356943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356946 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_356946 : Nat := 118140960795 + 356946 * 2 ^ 59
def prefixEnd_356946 : Nat := 4983230072969 + 3 ^ 40 * 356946 * 2
def baseEnd_356946 : Nat := 183284865699865680833441

theorem tailTrace_356946 : CollatzResearch.WordTrace tailWord_356946 prefixEnd_356946 183284865699865680833441 := by
  unfold tailWord_356946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254722541213269592128673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8679260109902052245676461 3254722541213269592128673)
  ·
    refine ⟨2441041905909952194096505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3254722541213269592128673 2441041905909952194096505)
    ·
      refine ⟨1830781429432464145572379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2441041905909952194096505 1830781429432464145572379)
      ·
        refine ⟨2746172144148696218358569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1830781429432464145572379 2746172144148696218358569)
        ·
          refine ⟨2059629108111522163768927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2746172144148696218358569 2059629108111522163768927)
          ·
            refine ⟨3089443662167283245653391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059629108111522163768927 3089443662167283245653391)
            ·
              refine ⟨4634165493250924868480087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089443662167283245653391 4634165493250924868480087)
              ·
                refine ⟨6951248239876387302720131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4634165493250924868480087 6951248239876387302720131)
                ·
                  refine ⟨10426872359814580954080197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6951248239876387302720131 10426872359814580954080197)
                  ·
                    refine ⟨1955038567465233928890037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10426872359814580954080197 1955038567465233928890037)
                    ·
                      refine ⟨183284865699865680833441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1955038567465233928890037 183284865699865680833441)
                      ·
                        rfl

theorem cell23_356946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_356946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356946 prefixEnd_356946 := by exact prefixLift 356946
  have htrace : WordTrace (prefixWord ++ tailWord_356946) baseStart_356946 baseEnd_356946 := by
    simpa [prefixWord, tailWord_356946, baseEnd_356946] using wordTrace_append hprefix tailTrace_356946
  have hstable : (prefixWord ++ tailWord_356946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356946).length < 2 ^ (prefixWord ++ tailWord_356946).sum := by decide
  have hdescent : baseEnd_356946 < baseStart_356946 := by decide
  rcases family_descends (prefixWord ++ tailWord_356946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356960 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 1, 3, 2]
def baseStart_356960 : Nat := 118140960795 + 356960 * 2 ^ 59
def prefixEnd_356960 : Nat := 4983230072969 + 3 ^ 40 * 356960 * 2
def baseEnd_356960 : Nat := 183292054429028626058377

theorem tailTrace_356960 : CollatzResearch.WordTrace tailWord_356960 prefixEnd_356960 183292054429028626058377 := by
  unfold tailWord_356960
  simp only [CollatzResearch.WordTrace]
  refine ⟨6509700393401179379762167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8679600524534905839682889 6509700393401179379762167)
  ·
    refine ⟨9764550590101769069643251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6509700393401179379762167 9764550590101769069643251)
    ·
      refine ⟨14646825885152653604464877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9764550590101769069643251 14646825885152653604464877)
      ·
        refine ⟨5492559706932245101674329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14646825885152653604464877 5492559706932245101674329)
        ·
          refine ⟨4119419780199183826255747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5492559706932245101674329 4119419780199183826255747)
          ·
            refine ⟨6179129670298775739383621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4119419780199183826255747 6179129670298775739383621)
            ·
              refine ⟨1158586813181020451134429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6179129670298775739383621 1158586813181020451134429)
              ·
                refine ⟨434470054942882669175411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1158586813181020451134429 434470054942882669175411)
                ·
                  refine ⟨651705082414324003763117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434470054942882669175411 651705082414324003763117)
                  ·
                    refine ⟨244389405905371501411169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 651705082414324003763117 244389405905371501411169)
                    ·
                      refine ⟨183292054429028626058377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244389405905371501411169 183292054429028626058377)
                      ·
                        rfl

theorem cell23_356960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_356960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356960 prefixEnd_356960 := by exact prefixLift 356960
  have htrace : WordTrace (prefixWord ++ tailWord_356960) baseStart_356960 baseEnd_356960 := by
    simpa [prefixWord, tailWord_356960, baseEnd_356960] using wordTrace_append hprefix tailTrace_356960
  have hstable : (prefixWord ++ tailWord_356960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356960).length < 2 ^ (prefixWord ++ tailWord_356960).sum := by decide
  have hdescent : baseEnd_356960 < baseStart_356960 := by decide
  rcases family_descends (prefixWord ++ tailWord_356960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356986 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_356986 : Nat := 118140960795 + 356986 * 2 ^ 59
def prefixEnd_356986 : Nat := 4983230072969 + 3 ^ 40 * 356986 * 2
def baseEnd_356986 : Nat := 183305404926045524333257

theorem tailTrace_356986 : CollatzResearch.WordTrace tailWord_356986 prefixEnd_356986 183305404926045524333257 := by
  unfold tailWord_356986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3255087271177041299992703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8680232723138776799980541 3255087271177041299992703)
  ·
    refine ⟨4882630906765561949989055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3255087271177041299992703 4882630906765561949989055)
    ·
      refine ⟨7323946360148342924983583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4882630906765561949989055 7323946360148342924983583)
      ·
        refine ⟨10985919540222514387475375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7323946360148342924983583 10985919540222514387475375)
        ·
          refine ⟨16478879310333771581213063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10985919540222514387475375 16478879310333771581213063)
          ·
            refine ⟨24718318965500657371819595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16478879310333771581213063 24718318965500657371819595)
            ·
              refine ⟨37077478448250986057729393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24718318965500657371819595 37077478448250986057729393)
              ·
                refine ⟨27808108836188239543297045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37077478448250986057729393 27808108836188239543297045)
                ·
                  refine ⟨1303505101696323728592049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27808108836188239543297045 1303505101696323728592049)
                  ·
                    refine ⟨977628826272242796444037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1303505101696323728592049 977628826272242796444037)
                    ·
                      refine ⟨183305404926045524333257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 977628826272242796444037 183305404926045524333257)
                      ·
                        rfl

theorem cell23_356986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_356986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_356986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_356986 prefixEnd_356986 := by exact prefixLift 356986
  have htrace : WordTrace (prefixWord ++ tailWord_356986) baseStart_356986 baseEnd_356986 := by
    simpa [prefixWord, tailWord_356986, baseEnd_356986] using wordTrace_append hprefix tailTrace_356986
  have hstable : (prefixWord ++ tailWord_356986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356986).length < 2 ^ (prefixWord ++ tailWord_356986).sum := by decide
  have hdescent : baseEnd_356986 < baseStart_356986 := by decide
  rcases family_descends (prefixWord ++ tailWord_356986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357024 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 2, 2, 2]
def baseStart_357024 : Nat := 118140960795 + 357024 * 2 ^ 59
def prefixEnd_357024 : Nat := 4983230072969 + 3 ^ 40 * 357024 * 2
def baseEnd_357024 : Nat := 183324917190916375658083

theorem tailTrace_357024 : CollatzResearch.WordTrace tailWord_357024 prefixEnd_357024 183324917190916375658083 := by
  unfold tailWord_357024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6510867529285248844927063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8681156705713665126569417 6510867529285248844927063)
  ·
    refine ⟨9766301293927873267390595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6510867529285248844927063 9766301293927873267390595)
    ·
      refine ⟨14649451940891809901085893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9766301293927873267390595 14649451940891809901085893)
      ·
        refine ⟨2746772238917214356453605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14649451940891809901085893 2746772238917214356453605)
        ·
          refine ⟨515019794796977691835051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2746772238917214356453605 515019794796977691835051)
          ·
            refine ⟨772529692195466537752577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515019794796977691835051 772529692195466537752577)
            ·
              refine ⟨579397269146599903314433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 772529692195466537752577 579397269146599903314433)
              ·
                refine ⟨434547951859949927485825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579397269146599903314433 434547951859949927485825)
                ·
                  refine ⟨325910963894962445614369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434547951859949927485825 325910963894962445614369)
                  ·
                    refine ⟨244433222921221834210777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 325910963894962445614369 244433222921221834210777)
                    ·
                      refine ⟨183324917190916375658083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244433222921221834210777 183324917190916375658083)
                      ·
                        rfl

theorem cell23_357024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_357024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357024 prefixEnd_357024 := by exact prefixLift 357024
  have htrace : WordTrace (prefixWord ++ tailWord_357024) baseStart_357024 baseEnd_357024 := by
    simpa [prefixWord, tailWord_357024, baseEnd_357024] using wordTrace_append hprefix tailTrace_357024
  have hstable : (prefixWord ++ tailWord_357024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357024).length < 2 ^ (prefixWord ++ tailWord_357024).sum := by decide
  have hdescent : baseEnd_357024 < baseStart_357024 := by decide
  rcases family_descends (prefixWord ++ tailWord_357024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357033 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 2, 5, 2]
def baseStart_357033 : Nat := 118140960795 + 357033 * 2 ^ 59
def prefixEnd_357033 : Nat := 4983230072969 + 3 ^ 40 * 357033 * 2
def baseEnd_357033 : Nat := 183329538516806840445541

theorem tailTrace_357033 : CollatzResearch.WordTrace tailWord_357033 prefixEnd_357033 183329538516806840445541 := by
  unfold tailWord_357033
  simp only [CollatzResearch.WordTrace]
  refine ⟨13022063315537892226931753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8681375543691928151287835 13022063315537892226931753)
  ·
    refine ⟨9766547486653419170198815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13022063315537892226931753 9766547486653419170198815)
    ·
      refine ⟨14649821229980128755298223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9766547486653419170198815 14649821229980128755298223)
      ·
        refine ⟨21974731844970193132947335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14649821229980128755298223 21974731844970193132947335)
        ·
          refine ⟨32962097767455289699421003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21974731844970193132947335 32962097767455289699421003)
          ·
            refine ⟨49443146651182934549131505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32962097767455289699421003 49443146651182934549131505)
            ·
              refine ⟨37082359988387200911848629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49443146651182934549131505 37082359988387200911848629)
              ·
                refine ⟨3476471248911300085485809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37082359988387200911848629 3476471248911300085485809)
                ·
                  refine ⟨2607353436683475064114357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3476471248911300085485809 2607353436683475064114357)
                  ·
                    refine ⟨244439384689075787260721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2607353436683475064114357 244439384689075787260721)
                    ·
                      refine ⟨183329538516806840445541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244439384689075787260721 183329538516806840445541)
                      ·
                        rfl

theorem cell23_357033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 5, 2].length) (baseStart_357033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357033 prefixEnd_357033 := by exact prefixLift 357033
  have htrace : WordTrace (prefixWord ++ tailWord_357033) baseStart_357033 baseEnd_357033 := by
    simpa [prefixWord, tailWord_357033, baseEnd_357033] using wordTrace_append hprefix tailTrace_357033
  have hstable : (prefixWord ++ tailWord_357033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357033).length < 2 ^ (prefixWord ++ tailWord_357033).sum := by decide
  have hdescent : baseEnd_357033 < baseStart_357033 := by decide
  rcases family_descends (prefixWord ++ tailWord_357033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357060 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_357060 : Nat := 118140960795 + 357060 * 2 ^ 59
def prefixEnd_357060 : Nat := 4983230072969 + 3 ^ 40 * 357060 * 2
def baseEnd_357060 : Nat := 61114467498159411602639

theorem tailTrace_357060 : CollatzResearch.WordTrace tailWord_357060 prefixEnd_357060 61114467498159411602639 := by
  unfold tailWord_357060
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511524043220037919082317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8682032057626717225443089 6511524043220037919082317)
  ·
    refine ⟨2441821516207514219655869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6511524043220037919082317 2441821516207514219655869)
    ·
      refine ⟨915683068577817832370951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2441821516207514219655869 915683068577817832370951)
      ·
        refine ⟨1373524602866726748556427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915683068577817832370951 1373524602866726748556427)
        ·
          refine ⟨2060286904300090122834641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373524602866726748556427 2060286904300090122834641)
          ·
            refine ⟨1545215178225067592125981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2060286904300090122834641 1545215178225067592125981)
            ·
              refine ⟨579455691834400347047243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1545215178225067592125981 579455691834400347047243)
              ·
                refine ⟨869183537751600520570865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579455691834400347047243 869183537751600520570865)
                ·
                  refine ⟨651887653313700390428149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 869183537751600520570865 651887653313700390428149)
                  ·
                    refine ⟨61114467498159411602639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 651887653313700390428149 61114467498159411602639)
                    ·
                      rfl

theorem cell23_357060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_357060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357060 prefixEnd_357060 := by exact prefixLift 357060
  have htrace : WordTrace (prefixWord ++ tailWord_357060) baseStart_357060 baseEnd_357060 := by
    simpa [prefixWord, tailWord_357060, baseEnd_357060] using wordTrace_append hprefix tailTrace_357060
  have hstable : (prefixWord ++ tailWord_357060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357060).length < 2 ^ (prefixWord ++ tailWord_357060).sum := by decide
  have hdescent : baseEnd_357060 < baseStart_357060 := by decide
  rcases family_descends (prefixWord ++ tailWord_357060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357063 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_357063 : Nat := 118140960795 + 357063 * 2 ^ 59
def prefixEnd_357063 : Nat := 4983230072969 + 3 ^ 40 * 357063 * 2
def baseEnd_357063 : Nat := 183344942936441723070403

theorem tailTrace_357063 : CollatzResearch.WordTrace tailWord_357063 prefixEnd_357063 183344942936441723070403 := by
  unfold tailWord_357063
  simp only [CollatzResearch.WordTrace]
  refine ⟨13023157505429207350523843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8682105003619471567015895 13023157505429207350523843)
  ·
    refine ⟨19534736258143811025785765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13023157505429207350523843 19534736258143811025785765)
    ·
      refine ⟨3662763048401964567334831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19534736258143811025785765 3662763048401964567334831)
      ·
        refine ⟨5494144572602946851002247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3662763048401964567334831 5494144572602946851002247)
        ·
          refine ⟨8241216858904420276503371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5494144572602946851002247 8241216858904420276503371)
          ·
            refine ⟨12361825288356630414755057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8241216858904420276503371 12361825288356630414755057)
            ·
              refine ⟨9271368966267472811066293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12361825288356630414755057 9271368966267472811066293)
              ·
                refine ⟨869190840587575576037465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9271368966267472811066293 869190840587575576037465)
                ·
                  refine ⟨651893130440681682028099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 869190840587575576037465 651893130440681682028099)
                  ·
                    refine ⟨977839695661022523042149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 651893130440681682028099 977839695661022523042149)
                    ·
                      refine ⟨183344942936441723070403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 977839695661022523042149 183344942936441723070403)
                      ·
                        rfl

theorem cell23_357063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_357063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357063 prefixEnd_357063 := by exact prefixLift 357063
  have htrace : WordTrace (prefixWord ++ tailWord_357063) baseStart_357063 baseEnd_357063 := by
    simpa [prefixWord, tailWord_357063, baseEnd_357063] using wordTrace_append hprefix tailTrace_357063
  have hstable : (prefixWord ++ tailWord_357063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357063).length < 2 ^ (prefixWord ++ tailWord_357063).sum := by decide
  have hdescent : baseEnd_357063 < baseStart_357063 := by decide
  rcases family_descends (prefixWord ++ tailWord_357063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357073 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 5, 4]
def baseStart_357073 : Nat := 118140960795 + 357073 * 2 ^ 59
def prefixEnd_357073 : Nat := 4983230072969 + 3 ^ 40 * 357073 * 2
def baseEnd_357073 : Nat := 61116692580995561315119

theorem tailTrace_357073 : CollatzResearch.WordTrace tailWord_357073 prefixEnd_357073 61116692580995561315119 := by
  unfold tailWord_357073
  simp only [CollatzResearch.WordTrace]
  refine ⟨13023522235392979058387873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8682348156928652705591915 13023522235392979058387873)
  ·
    refine ⟨9767641676544734293790905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13023522235392979058387873 9767641676544734293790905)
    ·
      refine ⟨7325731257408550720343179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9767641676544734293790905 7325731257408550720343179)
      ·
        refine ⟨10988596886112826080514769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7325731257408550720343179 10988596886112826080514769)
        ·
          refine ⟨8241447664584619560386077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10988596886112826080514769 8241447664584619560386077)
          ·
            refine ⟨3090542874219232335144779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8241447664584619560386077 3090542874219232335144779)
            ·
              refine ⟨4635814311328848502717169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3090542874219232335144779 4635814311328848502717169)
              ·
                refine ⟨3476860733496636377037877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4635814311328848502717169 3476860733496636377037877)
                ·
                  refine ⟨325955693765309660347301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3476860733496636377037877 325955693765309660347301)
                  ·
                    refine ⟨61116692580995561315119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 325955693765309660347301 61116692580995561315119)
                    ·
                      rfl

theorem cell23_357073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_357073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357073 prefixEnd_357073 := by exact prefixLift 357073
  have htrace : WordTrace (prefixWord ++ tailWord_357073) baseStart_357073 baseEnd_357073 := by
    simpa [prefixWord, tailWord_357073, baseEnd_357073] using wordTrace_append hprefix tailTrace_357073
  have hstable : (prefixWord ++ tailWord_357073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357073).length < 2 ^ (prefixWord ++ tailWord_357073).sum := by decide
  have hdescent : baseEnd_357073 < baseStart_357073 := by decide
  rcases family_descends (prefixWord ++ tailWord_357073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357080 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 2, 4, 2]
def baseStart_357080 : Nat := 118140960795 + 357080 * 2 ^ 59
def prefixEnd_357080 : Nat := 4983230072969 + 3 ^ 40 * 357080 * 2
def baseEnd_357080 : Nat := 183353672107568156557825

theorem tailTrace_357080 : CollatzResearch.WordTrace tailWord_357080 prefixEnd_357080 183353672107568156557825 := by
  unfold tailWord_357080
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511888773183809626946347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8682518364245079502595129 6511888773183809626946347)
  ·
    refine ⟨9767833159775714440419521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6511888773183809626946347 9767833159775714440419521)
    ·
      refine ⟨7325874869831785830314641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9767833159775714440419521 7325874869831785830314641)
      ·
        refine ⟨5494406152373839372735981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7325874869831785830314641 5494406152373839372735981)
        ·
          refine ⟨2060402307140189764775993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5494406152373839372735981 2060402307140189764775993)
          ·
            refine ⟨1545301730355142323581995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2060402307140189764775993 1545301730355142323581995)
            ·
              refine ⟨2317952595532713485372993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545301730355142323581995 2317952595532713485372993)
              ·
                refine ⟨1738464446649535114029745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317952595532713485372993 1738464446649535114029745)
                ·
                  refine ⟨1303848334987151335522309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1738464446649535114029745 1303848334987151335522309)
                  ·
                    refine ⟨244471562810090875410433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1303848334987151335522309 244471562810090875410433)
                    ·
                      refine ⟨183353672107568156557825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244471562810090875410433 183353672107568156557825)
                      ·
                        rfl

theorem cell23_357080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_357080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357080 prefixEnd_357080 := by exact prefixLift 357080
  have htrace : WordTrace (prefixWord ++ tailWord_357080) baseStart_357080 baseEnd_357080 := by
    simpa [prefixWord, tailWord_357080, baseEnd_357080] using wordTrace_append hprefix tailTrace_357080
  have hstable : (prefixWord ++ tailWord_357080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357080).length < 2 ^ (prefixWord ++ tailWord_357080).sum := by decide
  have hdescent : baseEnd_357080 < baseStart_357080 := by decide
  rcases family_descends (prefixWord ++ tailWord_357080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357170 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_357170 : Nat := 118140960795 + 357170 * 2 ^ 59
def prefixEnd_357170 : Nat := 4983230072969 + 3 ^ 40 * 357170 * 2
def baseEnd_357170 : Nat := 183399885366472804432411

theorem tailTrace_357170 : CollatzResearch.WordTrace tailWord_357170 prefixEnd_357170 183399885366472804432411 := by
  unfold tailWord_357170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3256765029010391156167241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8684706744027709749779309 3256765029010391156167241)
  ·
    refine ⟨2442573771757793367125431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3256765029010391156167241 2442573771757793367125431)
    ·
      refine ⟨3663860657636690050688147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2442573771757793367125431 3663860657636690050688147)
      ·
        refine ⟨5495790986455035076032221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3663860657636690050688147 5495790986455035076032221)
        ·
          refine ⟨2060921619920638153512083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5495790986455035076032221 2060921619920638153512083)
          ·
            refine ⟨3091382429880957230268125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060921619920638153512083 3091382429880957230268125)
            ·
              refine ⟨1159268411205358961350547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3091382429880957230268125 1159268411205358961350547)
              ·
                refine ⟨1738902616808038442025821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159268411205358961350547 1738902616808038442025821)
                ·
                  refine ⟨652088481303014415759683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1738902616808038442025821 652088481303014415759683)
                  ·
                    refine ⟨978132721954521623639525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 652088481303014415759683 978132721954521623639525)
                    ·
                      refine ⟨183399885366472804432411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 978132721954521623639525 183399885366472804432411)
                      ·
                        rfl

theorem cell23_357170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_357170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357170 prefixEnd_357170 := by exact prefixLift 357170
  have htrace : WordTrace (prefixWord ++ tailWord_357170) baseStart_357170 baseEnd_357170 := by
    simpa [prefixWord, tailWord_357170, baseEnd_357170] using wordTrace_append hprefix tailTrace_357170
  have hstable : (prefixWord ++ tailWord_357170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357170).length < 2 ^ (prefixWord ++ tailWord_357170).sum := by decide
  have hdescent : baseEnd_357170 < baseStart_357170 := by decide
  rcases family_descends (prefixWord ++ tailWord_357170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357187 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 1, 1, 4]
def baseStart_357187 : Nat := 118140960795 + 357187 * 2 ^ 59
def prefixEnd_357187 : Nat := 4983230072969 + 3 ^ 40 * 357187 * 2
def baseEnd_357187 : Nat := 183408614537599237919833

theorem tailTrace_357187 : CollatzResearch.WordTrace tailWord_357187 prefixEnd_357187 183408614537599237919833 := by
  unfold tailWord_357187
  simp only [CollatzResearch.WordTrace]
  refine ⟨13027680156979976528037815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8685120104653317685358543 13027680156979976528037815)
  ·
    refine ⟨19541520235469964792056723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13027680156979976528037815 19541520235469964792056723)
    ·
      refine ⟨29312280353204947188085085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19541520235469964792056723 29312280353204947188085085)
      ·
        refine ⟨10992105132451855195531907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29312280353204947188085085 10992105132451855195531907)
        ·
          refine ⟨16488157698677782793297861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10992105132451855195531907 16488157698677782793297861)
          ·
            refine ⟨3091529568502084273743349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16488157698677782793297861 3091529568502084273743349)
            ·
              refine ⟨289830897047070400663439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3091529568502084273743349 289830897047070400663439)
              ·
                refine ⟨434746345570605600995159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289830897047070400663439 434746345570605600995159)
                ·
                  refine ⟨652119518355908401492739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434746345570605600995159 652119518355908401492739)
                  ·
                    refine ⟨978179277533862602239109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 652119518355908401492739 978179277533862602239109)
                    ·
                      refine ⟨183408614537599237919833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 978179277533862602239109 183408614537599237919833)
                      ·
                        rfl

theorem cell23_357187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_357187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357187 prefixEnd_357187 := by exact prefixLift 357187
  have htrace : WordTrace (prefixWord ++ tailWord_357187) baseStart_357187 baseEnd_357187 := by
    simpa [prefixWord, tailWord_357187, baseEnd_357187] using wordTrace_append hprefix tailTrace_357187
  have hstable : (prefixWord ++ tailWord_357187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357187).length < 2 ^ (prefixWord ++ tailWord_357187).sum := by decide
  have hdescent : baseEnd_357187 < baseStart_357187 := by decide
  rcases family_descends (prefixWord ++ tailWord_357187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357210 : List Nat := [3, 1, 1, 2, 1, 6, 1, 8]
def baseStart_357210 : Nat := 118140960795 + 357210 * 2 ^ 59
def prefixEnd_357210 : Nat := 4983230072969 + 3 ^ 40 * 357210 * 2
def baseEnd_357210 : Nat := 6793349058987135108601

theorem tailTrace_357210 : CollatzResearch.WordTrace tailWord_357210 prefixEnd_357210 6793349058987135108601 := by
  unfold tailWord_357210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257129758974162864031271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8685679357264434304083389 3257129758974162864031271)
  ·
    refine ⟨4885694638461244296046907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3257129758974162864031271 4885694638461244296046907)
    ·
      refine ⟨7328541957691866444070361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4885694638461244296046907 7328541957691866444070361)
      ·
        refine ⟨5496406468268899833052771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7328541957691866444070361 5496406468268899833052771)
        ·
          refine ⟨8244609702403349749579157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496406468268899833052771 8244609702403349749579157)
          ·
            refine ⟨386466079800157019511523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8244609702403349749579157 386466079800157019511523)
            ·
              refine ⟨579699119700235529267285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386466079800157019511523 579699119700235529267285)
              ·
                refine ⟨6793349058987135108601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 579699119700235529267285 6793349058987135108601)
                ·
                  rfl

theorem cell23_357210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 8].length) (baseStart_357210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357210 prefixEnd_357210 := by exact prefixLift 357210
  have htrace : WordTrace (prefixWord ++ tailWord_357210) baseStart_357210 baseEnd_357210 := by
    simpa [prefixWord, tailWord_357210, baseEnd_357210] using wordTrace_append hprefix tailTrace_357210
  have hstable : (prefixWord ++ tailWord_357210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357210).length < 2 ^ (prefixWord ++ tailWord_357210).sum := by decide
  have hdescent : baseEnd_357210 < baseStart_357210 := by decide
  rcases family_descends (prefixWord ++ tailWord_357210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357237 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_357237 : Nat := 118140960795 + 357237 * 2 ^ 59
def prefixEnd_357237 : Nat := 4983230072969 + 3 ^ 40 * 357237 * 2
def baseEnd_357237 : Nat := 183434288570324042294603

theorem tailTrace_357237 : CollatzResearch.WordTrace tailWord_357237 prefixEnd_357237 183434288570324042294603 := by
  unfold tailWord_357237
  simp only [CollatzResearch.WordTrace]
  refine ⟨13029503806798835067357965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8686335871199223378238643 13029503806798835067357965)
  ·
    refine ⟨4886063927549563150259237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13029503806798835067357965 4886063927549563150259237)
    ·
      refine ⟨916136986415543090673607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4886063927549563150259237 916136986415543090673607)
      ·
        refine ⟨1374205479623314636010411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916136986415543090673607 1374205479623314636010411)
        ·
          refine ⟨2061308219434971954015617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374205479623314636010411 2061308219434971954015617)
          ·
            refine ⟨1545981164576228965511713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2061308219434971954015617 1545981164576228965511713)
            ·
              refine ⟨1159485873432171724133785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1545981164576228965511713 1159485873432171724133785)
              ·
                refine ⟨869614405074128793100339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1159485873432171724133785 869614405074128793100339)
                ·
                  refine ⟨1304421607611193189650509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869614405074128793100339 1304421607611193189650509)
                  ·
                    refine ⟨489158102854197446118941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1304421607611193189650509 489158102854197446118941)
                    ·
                      refine ⟨183434288570324042294603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489158102854197446118941 183434288570324042294603)
                      ·
                        rfl

theorem cell23_357237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_357237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357237 prefixEnd_357237 := by exact prefixLift 357237
  have htrace : WordTrace (prefixWord ++ tailWord_357237) baseStart_357237 baseEnd_357237 := by
    simpa [prefixWord, tailWord_357237, baseEnd_357237] using wordTrace_append hprefix tailTrace_357237
  have hstable : (prefixWord ++ tailWord_357237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357237).length < 2 ^ (prefixWord ++ tailWord_357237).sum := by decide
  have hdescent : baseEnd_357237 < baseStart_357237 := by decide
  rcases family_descends (prefixWord ++ tailWord_357237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357238 : List Nat := [5, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_357238 : Nat := 118140960795 + 357238 * 2 ^ 59
def prefixEnd_357238 : Nat := 4983230072969 + 3 ^ 40 * 357238 * 2
def baseEnd_357238 : Nat := 183434802050978538382099

theorem tailTrace_357238 : CollatzResearch.WordTrace tailWord_357238 prefixEnd_357238 183434802050978538382099 := by
  unfold tailWord_357238
  simp only [CollatzResearch.WordTrace]
  refine ⟨814346267487200764884023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8686360186530141492096245 814346267487200764884023)
  ·
    refine ⟨1221519401230801147326035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 814346267487200764884023 1221519401230801147326035)
    ·
      refine ⟨1832279101846201720989053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1221519401230801147326035 1832279101846201720989053)
      ·
        refine ⟨687104663192325645370895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1832279101846201720989053 687104663192325645370895)
        ·
          refine ⟨1030656994788488468056343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687104663192325645370895 1030656994788488468056343)
          ·
            refine ⟨1545985492182732702084515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030656994788488468056343 1545985492182732702084515)
            ·
              refine ⟨2318978238274099053126773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545985492182732702084515 2318978238274099053126773)
              ·
                refine ⟨217404209838196786230635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2318978238274099053126773 217404209838196786230635)
                ·
                  refine ⟨326106314757295179345953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217404209838196786230635 326106314757295179345953)
                  ·
                    refine ⟨244579736067971384509465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 326106314757295179345953 244579736067971384509465)
                    ·
                      refine ⟨183434802050978538382099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244579736067971384509465 183434802050978538382099)
                      ·
                        rfl

theorem cell23_357238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_357238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357238 prefixEnd_357238 := by exact prefixLift 357238
  have htrace : WordTrace (prefixWord ++ tailWord_357238) baseStart_357238 baseEnd_357238 := by
    simpa [prefixWord, tailWord_357238, baseEnd_357238] using wordTrace_append hprefix tailTrace_357238
  have hstable : (prefixWord ++ tailWord_357238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357238).length < 2 ^ (prefixWord ++ tailWord_357238).sum := by decide
  have hdescent : baseEnd_357238 < baseStart_357238 := by decide
  rcases family_descends (prefixWord ++ tailWord_357238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357280 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 3]
def baseStart_357280 : Nat := 118140960795 + 357280 * 2 ^ 59
def prefixEnd_357280 : Nat := 4983230072969 + 3 ^ 40 * 357280 * 2
def baseEnd_357280 : Nat := 183456368238467374056905

theorem tailTrace_357280 : CollatzResearch.WordTrace tailWord_357280 prefixEnd_357280 183456368238467374056905 := by
  unfold tailWord_357280
  simp only [CollatzResearch.WordTrace]
  refine ⟨6515536072821526705586647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8687381430428702274115529 6515536072821526705586647)
  ·
    refine ⟨9773304109232290058379971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6515536072821526705586647 9773304109232290058379971)
    ·
      refine ⟨14659956163848435087569957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9773304109232290058379971 14659956163848435087569957)
      ·
        refine ⟨2748741780721581578919367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14659956163848435087569957 2748741780721581578919367)
        ·
          refine ⟨4123112671082372368379051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2748741780721581578919367 4123112671082372368379051)
          ·
            refine ⟨6184669006623558552568577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123112671082372368379051 6184669006623558552568577)
            ·
              refine ⟨4638501754967668914426433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6184669006623558552568577 4638501754967668914426433)
              ·
                refine ⟨3478876316225751685819825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4638501754967668914426433 3478876316225751685819825)
                ·
                  refine ⟨2609157237169313764364869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3478876316225751685819825 2609157237169313764364869)
                  ·
                    refine ⟨489216981969246330818413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2609157237169313764364869 489216981969246330818413)
                    ·
                      refine ⟨183456368238467374056905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489216981969246330818413 183456368238467374056905)
                      ·
                        rfl

theorem cell23_357280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_357280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357280 prefixEnd_357280 := by exact prefixLift 357280
  have htrace : WordTrace (prefixWord ++ tailWord_357280) baseStart_357280 baseEnd_357280 := by
    simpa [prefixWord, tailWord_357280, baseEnd_357280] using wordTrace_append hprefix tailTrace_357280
  have hstable : (prefixWord ++ tailWord_357280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357280).length < 2 ^ (prefixWord ++ tailWord_357280).sum := by decide
  have hdescent : baseEnd_357280 < baseStart_357280 := by decide
  rcases family_descends (prefixWord ++ tailWord_357280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357281 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 1, 3, 2]
def baseStart_357281 : Nat := 118140960795 + 357281 * 2 ^ 59
def prefixEnd_357281 : Nat := 4983230072969 + 3 ^ 40 * 357281 * 2
def baseEnd_357281 : Nat := 183456881719121870144401

theorem tailTrace_357281 : CollatzResearch.WordTrace tailWord_357281 prefixEnd_357281 183456881719121870144401 := by
  unfold tailWord_357281
  simp only [CollatzResearch.WordTrace]
  refine ⟨13031108618639430581959697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8687405745759620387973131 13031108618639430581959697)
  ·
    refine ⟨9773331463979572936469773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13031108618639430581959697 9773331463979572936469773)
    ·
      refine ⟨3664999298992339851176165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9773331463979572936469773 3664999298992339851176165)
      ·
        refine ⟨687187368561063722095531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3664999298992339851176165 687187368561063722095531)
        ·
          refine ⟨1030781052841595583143297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687187368561063722095531 1030781052841595583143297)
          ·
            refine ⟨773085789631196687357473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1030781052841595583143297 773085789631196687357473)
            ·
              refine ⟨579814342223397515518105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773085789631196687357473 579814342223397515518105)
              ·
                refine ⟨434860756667548136638579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579814342223397515518105 434860756667548136638579)
                ·
                  refine ⟨652291135001322204957869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434860756667548136638579 652291135001322204957869)
                  ·
                    refine ⟨244609175625495826859201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 652291135001322204957869 244609175625495826859201)
                    ·
                      refine ⟨183456881719121870144401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244609175625495826859201 183456881719121870144401)
                      ·
                        rfl

theorem cell23_357281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_357281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357281 prefixEnd_357281 := by exact prefixLift 357281
  have htrace : WordTrace (prefixWord ++ tailWord_357281) baseStart_357281 baseEnd_357281 := by
    simpa [prefixWord, tailWord_357281, baseEnd_357281] using wordTrace_append hprefix tailTrace_357281
  have hstable : (prefixWord ++ tailWord_357281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357281).length < 2 ^ (prefixWord ++ tailWord_357281).sum := by decide
  have hdescent : baseEnd_357281 < baseStart_357281 := by decide
  rcases family_descends (prefixWord ++ tailWord_357281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357297 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 5]
def baseStart_357297 : Nat := 118140960795 + 357297 * 2 ^ 59
def prefixEnd_357297 : Nat := 4983230072969 + 3 ^ 40 * 357297 * 2
def baseEnd_357297 : Nat := 183465097409593807544327

theorem tailTrace_357297 : CollatzResearch.WordTrace tailWord_357297 prefixEnd_357297 183465097409593807544327 := by
  unfold tailWord_357297
  simp only [CollatzResearch.WordTrace]
  refine ⟨13031692186581465314542145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8687794791054310209694763 13031692186581465314542145)
  ·
    refine ⟨9773769139936098985906609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13031692186581465314542145 9773769139936098985906609)
    ·
      refine ⟨7330326854952074239429957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9773769139936098985906609 7330326854952074239429957)
      ·
        refine ⟨1374436285303513919893117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7330326854952074239429957 1374436285303513919893117)
        ·
          refine ⟨515413606988817719959919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1374436285303513919893117 515413606988817719959919)
          ·
            refine ⟨773120410483226579939879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515413606988817719959919 773120410483226579939879)
            ·
              refine ⟨1159680615724839869909819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773120410483226579939879 1159680615724839869909819)
              ·
                refine ⟨1739520923587259804864729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159680615724839869909819 1739520923587259804864729)
                ·
                  refine ⟨1304640692690444853648547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1739520923587259804864729 1304640692690444853648547)
                  ·
                    refine ⟨1956961039035667280472821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1304640692690444853648547 1956961039035667280472821)
                    ·
                      refine ⟨183465097409593807544327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1956961039035667280472821 183465097409593807544327)
                      ·
                        rfl

theorem cell23_357297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_357297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357297 prefixEnd_357297 := by exact prefixLift 357297
  have htrace : WordTrace (prefixWord ++ tailWord_357297) baseStart_357297 baseEnd_357297 := by
    simpa [prefixWord, tailWord_357297, baseEnd_357297] using wordTrace_append hprefix tailTrace_357297
  have hstable : (prefixWord ++ tailWord_357297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357297).length < 2 ^ (prefixWord ++ tailWord_357297).sum := by decide
  have hdescent : baseEnd_357297 < baseStart_357297 := by decide
  rcases family_descends (prefixWord ++ tailWord_357297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357310 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_357310 : Nat := 118140960795 + 357310 * 2 ^ 59
def prefixEnd_357310 : Nat := 4983230072969 + 3 ^ 40 * 357310 * 2
def baseEnd_357310 : Nat := 183471772658102256681767

theorem tailTrace_357310 : CollatzResearch.WordTrace tailWord_357310 prefixEnd_357310 183471772658102256681767 := by
  unfold tailWord_357310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629020791941796066845673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8688110890356245689843589 1629020791941796066845673)
  ·
    refine ⟨1221765593956347050134255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1629020791941796066845673 1221765593956347050134255)
    ·
      refine ⟨1832648390934520575201383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1221765593956347050134255 1832648390934520575201383)
      ·
        refine ⟨2748972586401780862802075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1832648390934520575201383 2748972586401780862802075)
        ·
          refine ⟨4123458879602671294203113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2748972586401780862802075 4123458879602671294203113)
          ·
            refine ⟨3092594159702003470652335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4123458879602671294203113 3092594159702003470652335)
            ·
              refine ⟨4638891239553005205978503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092594159702003470652335 4638891239553005205978503)
              ·
                refine ⟨6958336859329507808967755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4638891239553005205978503 6958336859329507808967755)
                ·
                  refine ⟨10437505288994261713451633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6958336859329507808967755 10437505288994261713451633)
                  ·
                    refine ⟨7828128966745696285088725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10437505288994261713451633 7828128966745696285088725)
                    ·
                      refine ⟨183471772658102256681767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7828128966745696285088725 183471772658102256681767)
                      ·
                        rfl

theorem cell23_357310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_357310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357310 prefixEnd_357310 := by exact prefixLift 357310
  have htrace : WordTrace (prefixWord ++ tailWord_357310) baseStart_357310 baseEnd_357310 := by
    simpa [prefixWord, tailWord_357310, baseEnd_357310] using wordTrace_append hprefix tailTrace_357310
  have hstable : (prefixWord ++ tailWord_357310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357310).length < 2 ^ (prefixWord ++ tailWord_357310).sum := by decide
  have hdescent : baseEnd_357310 < baseStart_357310 := by decide
  rcases family_descends (prefixWord ++ tailWord_357310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357347 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 2, 5]
def baseStart_357347 : Nat := 118140960795 + 357347 * 2 ^ 59
def prefixEnd_357347 : Nat := 4983230072969 + 3 ^ 40 * 357347 * 2
def baseEnd_357347 : Nat := 61163590480772870639699

theorem tailTrace_357347 : CollatzResearch.WordTrace tailWord_357347 prefixEnd_357347 61163590480772870639699 := by
  unfold tailWord_357347
  simp only [CollatzResearch.WordTrace]
  refine ⟨13033515836400323853862295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8689010557600215902574863 13033515836400323853862295)
  ·
    refine ⟨19550273754600485780793443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13033515836400323853862295 19550273754600485780793443)
    ·
      refine ⟨29325410631900728671190165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19550273754600485780793443 29325410631900728671190165)
      ·
        refine ⟨1374628623370346656462039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29325410631900728671190165 1374628623370346656462039)
        ·
          refine ⟨2061942935055519984693059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374628623370346656462039 2061942935055519984693059)
          ·
            refine ⟨3092914402583279977039589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061942935055519984693059 3092914402583279977039589)
            ·
              refine ⟨579921450484364995694923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3092914402583279977039589 579921450484364995694923)
              ·
                refine ⟨869882175726547493542385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579921450484364995694923 869882175726547493542385)
                ·
                  refine ⟨652411631794910620156789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 869882175726547493542385 652411631794910620156789)
                  ·
                    refine ⟨61163590480772870639699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 652411631794910620156789 61163590480772870639699)
                    ·
                      rfl

theorem cell23_357347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 5].length) (baseStart_357347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357347 prefixEnd_357347 := by exact prefixLift 357347
  have htrace : WordTrace (prefixWord ++ tailWord_357347) baseStart_357347 baseEnd_357347 := by
    simpa [prefixWord, tailWord_357347, baseEnd_357347] using wordTrace_append hprefix tailTrace_357347
  have hstable : (prefixWord ++ tailWord_357347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357347).length < 2 ^ (prefixWord ++ tailWord_357347).sum := by decide
  have hdescent : baseEnd_357347 < baseStart_357347 := by decide
  rcases family_descends (prefixWord ++ tailWord_357347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357384 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 2, 4, 2]
def baseStart_357384 : Nat := 118140960795 + 357384 * 2 ^ 59
def prefixEnd_357384 : Nat := 4983230072969 + 3 ^ 40 * 357384 * 2
def baseEnd_357384 : Nat := 183509770226534967156427

theorem tailTrace_357384 : CollatzResearch.WordTrace tailWord_357384 prefixEnd_357384 183509770226534967156427 := by
  unfold tailWord_357384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517432668633139586479603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8689910224844186115306137 6517432668633139586479603)
  ·
    refine ⟨9776149002949709379719405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6517432668633139586479603 9776149002949709379719405)
    ·
      refine ⟨3666055876106141017394777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9776149002949709379719405 3666055876106141017394777)
      ·
        refine ⟨2749541907079605763046083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3666055876106141017394777 2749541907079605763046083)
        ·
          refine ⟨4124312860619408644569125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749541907079605763046083 4124312860619408644569125)
          ·
            refine ⟨773308661366139120856711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4124312860619408644569125 773308661366139120856711)
            ·
              refine ⟨1159962992049208681285067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773308661366139120856711 1159962992049208681285067)
              ·
                refine ⟨1739944488073813021927601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159962992049208681285067 1739944488073813021927601)
                ·
                  refine ⟨1304958366055359766445701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1739944488073813021927601 1304958366055359766445701)
                  ·
                    refine ⟨244679693635379956208569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1304958366055359766445701 244679693635379956208569)
                    ·
                      refine ⟨183509770226534967156427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244679693635379956208569 183509770226534967156427)
                      ·
                        rfl

theorem cell23_357384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_357384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357384 prefixEnd_357384 := by exact prefixLift 357384
  have htrace : WordTrace (prefixWord ++ tailWord_357384) baseStart_357384 baseEnd_357384 := by
    simpa [prefixWord, tailWord_357384, baseEnd_357384] using wordTrace_append hprefix tailTrace_357384
  have hstable : (prefixWord ++ tailWord_357384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357384).length < 2 ^ (prefixWord ++ tailWord_357384).sum := by decide
  have hdescent : baseEnd_357384 < baseStart_357384 := by decide
  rcases family_descends (prefixWord ++ tailWord_357384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357404 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_357404 : Nat := 118140960795 + 357404 * 2 ^ 59
def prefixEnd_357404 : Nat := 4983230072969 + 3 ^ 40 * 357404 * 2
def baseEnd_357404 : Nat := 183520039839624888906335

theorem tailTrace_357404 : CollatzResearch.WordTrace tailWord_357404 prefixEnd_357404 183520039839624888906335 := by
  unfold tailWord_357404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517797398596911294343633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8690396531462548392458177 6517797398596911294343633)
  ·
    refine ⟨4888348048947683470757725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6517797398596911294343633 4888348048947683470757725)
    ·
      refine ⟨1833130518355381301534147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4888348048947683470757725 1833130518355381301534147)
      ·
        refine ⟨2749695777533071952301221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833130518355381301534147 2749695777533071952301221)
        ·
          refine ⟨515567958287450991056479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2749695777533071952301221 515567958287450991056479)
          ·
            refine ⟨773351937431176486584719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515567958287450991056479 773351937431176486584719)
            ·
              refine ⟨1160027906146764729877079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773351937431176486584719 1160027906146764729877079)
              ·
                refine ⟨1740041859220147094815619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160027906146764729877079 1740041859220147094815619)
                ·
                  refine ⟨2610062788830220642223429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740041859220147094815619 2610062788830220642223429)
                  ·
                    refine ⟨489386772905666370416893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2610062788830220642223429 489386772905666370416893)
                    ·
                      refine ⟨183520039839624888906335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489386772905666370416893 183520039839624888906335)
                      ·
                        rfl

theorem cell23_357404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_357404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357404 prefixEnd_357404 := by exact prefixLift 357404
  have htrace : WordTrace (prefixWord ++ tailWord_357404) baseStart_357404 baseEnd_357404 := by
    simpa [prefixWord, tailWord_357404, baseEnd_357404] using wordTrace_append hprefix tailTrace_357404
  have hstable : (prefixWord ++ tailWord_357404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357404).length < 2 ^ (prefixWord ++ tailWord_357404).sum := by decide
  have hdescent : baseEnd_357404 < baseStart_357404 := by decide
  rcases family_descends (prefixWord ++ tailWord_357404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357411 : List Nat := [1, 1, 1, 4, 3, 3, 2, 3, 1, 4]
def baseStart_357411 : Nat := 118140960795 + 357411 * 2 ^ 59
def prefixEnd_357411 : Nat := 4983230072969 + 3 ^ 40 * 357411 * 2
def baseEnd_357411 : Nat := 61174544734735453839601

theorem tailTrace_357411 : CollatzResearch.WordTrace tailWord_357411 prefixEnd_357411 61174544734735453839601 := by
  unfold tailWord_357411
  simp only [CollatzResearch.WordTrace]
  refine ⟨13035850108168462784192087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8690566738778975189461391 13035850108168462784192087)
  ·
    refine ⟨19553775162252694176288131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13035850108168462784192087 19553775162252694176288131)
    ·
      refine ⟨29330662743379041264432197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19553775162252694176288131 29330662743379041264432197)
      ·
        refine ⟨5499499264383570237081037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29330662743379041264432197 5499499264383570237081037)
        ·
          refine ⟨2062312224143838838905389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5499499264383570237081037 2062312224143838838905389)
          ·
            refine ⟨773367084053939564589521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2062312224143838838905389 773367084053939564589521)
            ·
              refine ⟨580025313040454673442141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773367084053939564589521 580025313040454673442141)
              ·
                refine ⟨217509492390170502540803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 580025313040454673442141 217509492390170502540803)
                ·
                  refine ⟨326264238585255753811205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217509492390170502540803 326264238585255753811205)
                  ·
                    refine ⟨61174544734735453839601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326264238585255753811205 61174544734735453839601)
                    ·
                      rfl

theorem cell23_357411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 1, 4].length) (baseStart_357411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357411 prefixEnd_357411 := by exact prefixLift 357411
  have htrace : WordTrace (prefixWord ++ tailWord_357411) baseStart_357411 baseEnd_357411 := by
    simpa [prefixWord, tailWord_357411, baseEnd_357411] using wordTrace_append hprefix tailTrace_357411
  have hstable : (prefixWord ++ tailWord_357411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357411).length < 2 ^ (prefixWord ++ tailWord_357411).sum := by decide
  have hdescent : baseEnd_357411 < baseStart_357411 := by decide
  rcases family_descends (prefixWord ++ tailWord_357411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357428 : List Nat := [2, 5, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_357428 : Nat := 118140960795 + 357428 * 2 ^ 59
def prefixEnd_357428 : Nat := 4983230072969 + 3 ^ 40 * 357428 * 2
def baseEnd_357428 : Nat := 61177454458444265002075

theorem tailTrace_357428 : CollatzResearch.WordTrace tailWord_357428 prefixEnd_357428 61177454458444265002075 := by
  unfold tailWord_357428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6518235074553437343780469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8690980099404583125040625 6518235074553437343780469)
  ·
    refine ⟨611084538239384750979419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6518235074553437343780469 611084538239384750979419)
    ·
      refine ⟨916626807359077126469129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611084538239384750979419 916626807359077126469129)
      ·
        refine ⟨687470105519307844851847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 916626807359077126469129 687470105519307844851847)
        ·
          refine ⟨1031205158278961767277771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687470105519307844851847 1031205158278961767277771)
          ·
            refine ⟨1546807737418442650916657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031205158278961767277771 1546807737418442650916657)
            ·
              refine ⟨1160105803063831988187493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546807737418442650916657 1160105803063831988187493)
              ·
                refine ⟨217519838074468497785155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1160105803063831988187493 217519838074468497785155)
                ·
                  refine ⟨326279757111702746677733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217519838074468497785155 326279757111702746677733)
                  ·
                    refine ⟨61177454458444265002075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326279757111702746677733 61177454458444265002075)
                    ·
                      rfl

theorem cell23_357428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_357428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357428 prefixEnd_357428 := by exact prefixLift 357428
  have htrace : WordTrace (prefixWord ++ tailWord_357428) baseStart_357428 baseEnd_357428 := by
    simpa [prefixWord, tailWord_357428, baseEnd_357428] using wordTrace_append hprefix tailTrace_357428
  have hstable : (prefixWord ++ tailWord_357428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357428).length < 2 ^ (prefixWord ++ tailWord_357428).sum := by decide
  have hdescent : baseEnd_357428 < baseStart_357428 := by decide
  rcases family_descends (prefixWord ++ tailWord_357428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357434 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3]
def baseStart_357434 : Nat := 118140960795 + 357434 * 2 ^ 59
def prefixEnd_357434 : Nat := 4983230072969 + 3 ^ 40 * 357434 * 2
def baseEnd_357434 : Nat := 183535444259259771531197

theorem tailTrace_357434 : CollatzResearch.WordTrace tailWord_357434 prefixEnd_357434 183535444259259771531197 := by
  unfold tailWord_357434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3259172246771284428069839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8691125991390091808186237 3259172246771284428069839)
  ·
    refine ⟨4888758370156926642104759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3259172246771284428069839 4888758370156926642104759)
    ·
      refine ⟨7333137555235389963157139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4888758370156926642104759 7333137555235389963157139)
      ·
        refine ⟨10999706332853084944735709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7333137555235389963157139 10999706332853084944735709)
        ·
          refine ⟨4124889874819906854275891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10999706332853084944735709 4124889874819906854275891)
          ·
            refine ⟨6187334812229860281413837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124889874819906854275891 6187334812229860281413837)
            ·
              refine ⟨2320250554586197605530189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6187334812229860281413837 2320250554586197605530189)
              ·
                refine ⟨870093957969824102073821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2320250554586197605530189 870093957969824102073821)
                ·
                  refine ⟨326285234238684038277683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870093957969824102073821 326285234238684038277683)
                  ·
                    refine ⟨489427851358026057416525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326285234238684038277683 489427851358026057416525)
                    ·
                      refine ⟨183535444259259771531197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489427851358026057416525 183535444259259771531197)
                      ·
                        rfl

theorem cell23_357434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_357434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357434 prefixEnd_357434 := by exact prefixLift 357434
  have htrace : WordTrace (prefixWord ++ tailWord_357434) baseStart_357434 baseEnd_357434 := by
    simpa [prefixWord, tailWord_357434, baseEnd_357434] using wordTrace_append hprefix tailTrace_357434
  have hstable : (prefixWord ++ tailWord_357434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357434).length < 2 ^ (prefixWord ++ tailWord_357434).sum := by decide
  have hdescent : baseEnd_357434 < baseStart_357434 := by decide
  rcases family_descends (prefixWord ++ tailWord_357434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357441 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 6]
def baseStart_357441 : Nat := 118140960795 + 357441 * 2 ^ 59
def prefixEnd_357441 : Nat := 4983230072969 + 3 ^ 40 * 357441 * 2
def baseEnd_357441 : Nat := 20393226513760138238185

theorem tailTrace_357441 : CollatzResearch.WordTrace tailWord_357441 prefixEnd_357441 20393226513760138238185 := by
  unfold tailWord_357441
  simp only [CollatzResearch.WordTrace]
  refine ⟨13036944298059777907784177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8691296198706518605189451 13036944298059777907784177)
  ·
    refine ⟨9777708223544833430838133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13036944298059777907784177 9777708223544833430838133)
    ·
      refine ⟨916660145957328134141075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9777708223544833430838133 916660145957328134141075)
      ·
        refine ⟨1374990218935992201211613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916660145957328134141075 1374990218935992201211613)
        ·
          refine ⟨515621332100997075454355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1374990218935992201211613 515621332100997075454355)
          ·
            refine ⟨773431998151495613181533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515621332100997075454355 773431998151495613181533)
            ·
              refine ⟨290036999306810854943075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 773431998151495613181533 290036999306810854943075)
              ·
                refine ⟨435055498960216282414613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290036999306810854943075 435055498960216282414613)
                ·
                  refine ⟨20393226513760138238185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 435055498960216282414613 20393226513760138238185)
                  ·
                    rfl

theorem cell23_357441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 6].length) (baseStart_357441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357441 prefixEnd_357441 := by exact prefixLift 357441
  have htrace : WordTrace (prefixWord ++ tailWord_357441) baseStart_357441 baseEnd_357441 := by
    simpa [prefixWord, tailWord_357441, baseEnd_357441] using wordTrace_append hprefix tailTrace_357441
  have hstable : (prefixWord ++ tailWord_357441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357441).length < 2 ^ (prefixWord ++ tailWord_357441).sum := by decide
  have hdescent : baseEnd_357441 < baseStart_357441 := by decide
  rcases family_descends (prefixWord ++ tailWord_357441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357454 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_357454 : Nat := 118140960795 + 357454 * 2 ^ 59
def prefixEnd_357454 : Nat := 4983230072969 + 3 ^ 40 * 357454 * 2
def baseEnd_357454 : Nat := 61181904624116564427035

theorem tailTrace_357454 : CollatzResearch.WordTrace tailWord_357454 prefixEnd_357454 61181904624116564427035 := by
  unfold tailWord_357454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629677305876585141000927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8691612298008454085338277 1629677305876585141000927)
  ·
    refine ⟨2444515958814877711501391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1629677305876585141000927 2444515958814877711501391)
    ·
      refine ⟨3666773938222316567252087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2444515958814877711501391 3666773938222316567252087)
      ·
        refine ⟨5500160907333474850878131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3666773938222316567252087 5500160907333474850878131)
        ·
          refine ⟨8250241361000212276317197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5500160907333474850878131 8250241361000212276317197)
          ·
            refine ⟨3093840510375079603618949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8250241361000212276317197 3093840510375079603618949)
            ·
              refine ⟨580095095695327425678553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3093840510375079603618949 580095095695327425678553)
              ·
                refine ⟨435071321771495569258915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580095095695327425678553 435071321771495569258915)
                ·
                  refine ⟨652606982657243353888373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435071321771495569258915 652606982657243353888373)
                  ·
                    refine ⟨61181904624116564427035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 652606982657243353888373 61181904624116564427035)
                    ·
                      rfl

theorem cell23_357454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_357454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357454 prefixEnd_357454 := by exact prefixLift 357454
  have htrace : WordTrace (prefixWord ++ tailWord_357454) baseStart_357454 baseEnd_357454 := by
    simpa [prefixWord, tailWord_357454, baseEnd_357454] using wordTrace_append hprefix tailTrace_357454
  have hstable : (prefixWord ++ tailWord_357454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357454).length < 2 ^ (prefixWord ++ tailWord_357454).sum := by decide
  have hdescent : baseEnd_357454 < baseStart_357454 := by decide
  rcases family_descends (prefixWord ++ tailWord_357454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357457 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_357457 : Nat := 118140960795 + 357457 * 2 ^ 59
def prefixEnd_357457 : Nat := 4983230072969 + 3 ^ 40 * 357457 * 2
def baseEnd_357457 : Nat := 183547254314313181543591

theorem tailTrace_357457 : CollatzResearch.WordTrace tailWord_357457 prefixEnd_357457 183547254314313181543591 := by
  unfold tailWord_357457
  simp only [CollatzResearch.WordTrace]
  refine ⟨13037527866001812640366625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8691685244001208426911083 13037527866001812640366625)
  ·
    refine ⟨9778145899501359480274969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13037527866001812640366625 9778145899501359480274969)
    ·
      refine ⟨7333609424626019610206227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9778145899501359480274969 7333609424626019610206227)
      ·
        refine ⟨11000414136939029415309341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7333609424626019610206227 11000414136939029415309341)
        ·
          refine ⟨4125155301352136030741003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11000414136939029415309341 4125155301352136030741003)
          ·
            refine ⟨6187732952028204046111505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4125155301352136030741003 6187732952028204046111505)
            ·
              refine ⟨4640799714021153034583629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6187732952028204046111505 4640799714021153034583629)
              ·
                refine ⟨1740299892757932387968861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4640799714021153034583629 1740299892757932387968861)
                ·
                  refine ⟨652612459784224645488323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1740299892757932387968861 652612459784224645488323)
                  ·
                    refine ⟨978918689676336968232485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 652612459784224645488323 978918689676336968232485)
                    ·
                      refine ⟨183547254314313181543591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 978918689676336968232485 183547254314313181543591)
                      ·
                        rfl

theorem cell23_357457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_357457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357457 prefixEnd_357457 := by exact prefixLift 357457
  have htrace : WordTrace (prefixWord ++ tailWord_357457) baseStart_357457 baseEnd_357457 := by
    simpa [prefixWord, tailWord_357457, baseEnd_357457] using wordTrace_append hprefix tailTrace_357457
  have hstable : (prefixWord ++ tailWord_357457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357457).length < 2 ^ (prefixWord ++ tailWord_357457).sum := by decide
  have hdescent : baseEnd_357457 < baseStart_357457 := by decide
  rcases family_descends (prefixWord ++ tailWord_357457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357462 : List Nat := [5, 2, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_357462 : Nat := 118140960795 + 357462 * 2 ^ 59
def prefixEnd_357462 : Nat := 4983230072969 + 3 ^ 40 * 357462 * 2
def baseEnd_357462 : Nat := 61183273905861887327023

theorem tailTrace_357462 : CollatzResearch.WordTrace tailWord_357462 prefixEnd_357462 61183273905861887327023 := by
  unfold tailWord_357462
  simp only [CollatzResearch.WordTrace]
  refine ⟨814856889436481155893665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8691806820655798996199093 814856889436481155893665)
  ·
    refine ⟨611142667077360866920249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 814856889436481155893665 611142667077360866920249)
    ·
      refine ⟨458357000308020650190187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 611142667077360866920249 458357000308020650190187)
      ·
        refine ⟨687535500462030975285281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458357000308020650190187 687535500462030975285281)
        ·
          refine ⟨515651625346523231463961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 687535500462030975285281 515651625346523231463961)
          ·
            refine ⟨386738719009892423597971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515651625346523231463961 386738719009892423597971)
            ·
              refine ⟨580108078514838635396957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386738719009892423597971 580108078514838635396957)
              ·
                refine ⟨217540529443064488273859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 580108078514838635396957 217540529443064488273859)
                ·
                  refine ⟨326310794164596732410789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217540529443064488273859 326310794164596732410789)
                  ·
                    refine ⟨61183273905861887327023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326310794164596732410789 61183273905861887327023)
                    ·
                      rfl

theorem cell23_357462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_357462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357462 prefixEnd_357462 := by exact prefixLift 357462
  have htrace : WordTrace (prefixWord ++ tailWord_357462) baseStart_357462 baseEnd_357462 := by
    simpa [prefixWord, tailWord_357462, baseEnd_357462] using wordTrace_append hprefix tailTrace_357462
  have hstable : (prefixWord ++ tailWord_357462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357462).length < 2 ^ (prefixWord ++ tailWord_357462).sum := by decide
  have hdescent : baseEnd_357462 < baseStart_357462 := by decide
  rcases family_descends (prefixWord ++ tailWord_357462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357484 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_357484 : Nat := 118140960795 + 357484 * 2 ^ 59
def prefixEnd_357484 : Nat := 4983230072969 + 3 ^ 40 * 357484 * 2
def baseEnd_357484 : Nat := 61187039430661525301989

theorem tailTrace_357484 : CollatzResearch.WordTrace tailWord_357484 prefixEnd_357484 61187039430661525301989 := by
  unfold tailWord_357484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519256318451998125799753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8692341757935997501066337 6519256318451998125799753)
  ·
    refine ⟨4889442238838998594349815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6519256318451998125799753 4889442238838998594349815)
    ·
      refine ⟨7334163358258497891524723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4889442238838998594349815 7334163358258497891524723)
      ·
        refine ⟨11001245037387746837287085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7334163358258497891524723 11001245037387746837287085)
        ·
          refine ⟨4125466889020405063982657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11001245037387746837287085 4125466889020405063982657)
          ·
            refine ⟨3094100166765303797986993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4125466889020405063982657 3094100166765303797986993)
            ·
              refine ⟨2320575125073977848490245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3094100166765303797986993 2320575125073977848490245)
              ·
                refine ⟨435107835951370846591921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2320575125073977848490245 435107835951370846591921)
                ·
                  refine ⟨326330876963528134943941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435107835951370846591921 326330876963528134943941)
                  ·
                    refine ⟨61187039430661525301989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326330876963528134943941 61187039430661525301989)
                    ·
                      rfl

theorem cell23_357484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_357484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357484 prefixEnd_357484 := by exact prefixLift 357484
  have htrace : WordTrace (prefixWord ++ tailWord_357484) baseStart_357484 baseEnd_357484 := by
    simpa [prefixWord, tailWord_357484, baseEnd_357484] using wordTrace_append hprefix tailTrace_357484
  have hstable : (prefixWord ++ tailWord_357484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357484).length < 2 ^ (prefixWord ++ tailWord_357484).sum := by decide
  have hdescent : baseEnd_357484 < baseStart_357484 := by decide
  rcases family_descends (prefixWord ++ tailWord_357484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357485 : List Nat := [1, 5, 1, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_357485 : Nat := 118140960795 + 357485 * 2 ^ 59
def prefixEnd_357485 : Nat := 4983230072969 + 3 ^ 40 * 357485 * 2
def baseEnd_357485 : Nat := 183561631772639071993463

theorem tailTrace_357485 : CollatzResearch.WordTrace tailWord_357485 prefixEnd_357485 183561631772639071993463 := by
  unfold tailWord_357485
  simp only [CollatzResearch.WordTrace]
  refine ⟨13038549109900373422385909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8692366073266915614923939 13038549109900373422385909)
  ·
    refine ⟨1222363979053160008348679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13038549109900373422385909 1222363979053160008348679)
    ·
      refine ⟨1833545968579740012523019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1222363979053160008348679 1833545968579740012523019)
      ·
        refine ⟨2750318952869610018784529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833545968579740012523019 2750318952869610018784529)
        ·
          refine ⟨2062739214652207514088397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2750318952869610018784529 2062739214652207514088397)
          ·
            refine ⟨773527205494577817783149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2062739214652207514088397 773527205494577817783149)
            ·
              refine ⟨290072702060466681668681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 773527205494577817783149 290072702060466681668681)
              ·
                refine ⟨217554526545350011251511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290072702060466681668681 217554526545350011251511)
                ·
                  refine ⟨326331789818025016877267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217554526545350011251511 326331789818025016877267)
                  ·
                    refine ⟨489497684727037525315901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326331789818025016877267 489497684727037525315901)
                    ·
                      refine ⟨183561631772639071993463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489497684727037525315901 183561631772639071993463)
                      ·
                        rfl

theorem cell23_357485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_357485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357485 prefixEnd_357485 := by exact prefixLift 357485
  have htrace : WordTrace (prefixWord ++ tailWord_357485) baseStart_357485 baseEnd_357485 := by
    simpa [prefixWord, tailWord_357485, baseEnd_357485] using wordTrace_append hprefix tailTrace_357485
  have hstable : (prefixWord ++ tailWord_357485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357485).length < 2 ^ (prefixWord ++ tailWord_357485).sum := by decide
  have hdescent : baseEnd_357485 < baseStart_357485 := by decide
  rcases family_descends (prefixWord ++ tailWord_357485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357494 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_357494 : Nat := 118140960795 + 357494 * 2 ^ 59
def prefixEnd_357494 : Nat := 4983230072969 + 3 ^ 40 * 357494 * 2
def baseEnd_357494 : Nat := 183566253098529536780921

theorem tailTrace_357494 : CollatzResearch.WordTrace tailWord_357494 prefixEnd_357494 183566253098529536780921 := by
  unfold tailWord_357494
  simp only [CollatzResearch.WordTrace]
  refine ⟨814929835429235497466471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8692584911245178639642357 814929835429235497466471)
  ·
    refine ⟨1222394753143853246199707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 814929835429235497466471 1222394753143853246199707)
    ·
      refine ⟨1833592129715779869299561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1222394753143853246199707 1833592129715779869299561)
      ·
        refine ⟨1375194097286834901974671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1833592129715779869299561 1375194097286834901974671)
        ·
          refine ⟨2062791145930252352962007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375194097286834901974671 2062791145930252352962007)
          ·
            refine ⟨3094186718895378529443011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062791145930252352962007 3094186718895378529443011)
            ·
              refine ⟨4641280078343067794164517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3094186718895378529443011 4641280078343067794164517)
              ·
                refine ⟨870240014689325211405847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4641280078343067794164517 870240014689325211405847)
                ·
                  refine ⟨1305360022033987817108771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870240014689325211405847 1305360022033987817108771)
                  ·
                    refine ⟨1958040033050981725663157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1305360022033987817108771 1958040033050981725663157)
                    ·
                      refine ⟨183566253098529536780921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1958040033050981725663157 183566253098529536780921)
                      ·
                        rfl

theorem cell23_357494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_357494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357494 prefixEnd_357494 := by exact prefixLift 357494
  have htrace : WordTrace (prefixWord ++ tailWord_357494) baseStart_357494 baseEnd_357494 := by
    simpa [prefixWord, tailWord_357494, baseEnd_357494] using wordTrace_append hprefix tailTrace_357494
  have hstable : (prefixWord ++ tailWord_357494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357494).length < 2 ^ (prefixWord ++ tailWord_357494).sum := by decide
  have hdescent : baseEnd_357494 < baseStart_357494 := by decide
  rcases family_descends (prefixWord ++ tailWord_357494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357528 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 1, 2, 3]
def baseStart_357528 : Nat := 118140960795 + 357528 * 2 ^ 59
def prefixEnd_357528 : Nat := 4983230072969 + 3 ^ 40 * 357528 * 2
def baseEnd_357528 : Nat := 183583711440782403755765

theorem tailTrace_357528 : CollatzResearch.WordTrace tailWord_357528 prefixEnd_357528 183583711440782403755765 := by
  unfold tailWord_357528
  simp only [CollatzResearch.WordTrace]
  refine ⟨6520058724372295883100619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8693411632496394510800825 6520058724372295883100619)
  ·
    refine ⟨9780088086558443824650929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6520058724372295883100619 9780088086558443824650929)
    ·
      refine ⟨7335066064918832868488197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9780088086558443824650929 7335066064918832868488197)
      ·
        refine ⟨1375324887172281162841537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7335066064918832868488197 1375324887172281162841537)
        ·
          refine ⟨1031493665379210872131153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1375324887172281162841537 1031493665379210872131153)
          ·
            refine ⟨773620249034408154098365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031493665379210872131153 773620249034408154098365)
            ·
              refine ⟨290107593387903057786887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 773620249034408154098365 290107593387903057786887)
              ·
                refine ⟨435161390081854586680331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290107593387903057786887 435161390081854586680331)
                ·
                  refine ⟨652742085122781880020497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435161390081854586680331 652742085122781880020497)
                  ·
                    refine ⟨489556563842086410015373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 652742085122781880020497 489556563842086410015373)
                    ·
                      refine ⟨183583711440782403755765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489556563842086410015373 183583711440782403755765)
                      ·
                        rfl

theorem cell23_357528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_357528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357528 prefixEnd_357528 := by exact prefixLift 357528
  have htrace : WordTrace (prefixWord ++ tailWord_357528) baseStart_357528 baseEnd_357528 := by
    simpa [prefixWord, tailWord_357528, baseEnd_357528] using wordTrace_append hprefix tailTrace_357528
  have hstable : (prefixWord ++ tailWord_357528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357528).length < 2 ^ (prefixWord ++ tailWord_357528).sum := by decide
  have hdescent : baseEnd_357528 < baseStart_357528 := by decide
  rcases family_descends (prefixWord ++ tailWord_357528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357541 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 2, 1, 3]
def baseStart_357541 : Nat := 118140960795 + 357541 * 2 ^ 59
def prefixEnd_357541 : Nat := 4983230072969 + 3 ^ 40 * 357541 * 2
def baseEnd_357541 : Nat := 183590386689290852893205

theorem tailTrace_357541 : CollatzResearch.WordTrace tailWord_357541 prefixEnd_357541 183590386689290852893205 := by
  unfold tailWord_357541
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040591597697494986424477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8693727731798329990949651 13040591597697494986424477)
  ·
    refine ⟨4890221849136560619909179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13040591597697494986424477 4890221849136560619909179)
    ·
      refine ⟨7335332773704840929863769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4890221849136560619909179 7335332773704840929863769)
      ·
        refine ⟨5501499580278630697397827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7335332773704840929863769 5501499580278630697397827)
        ·
          refine ⟨8252249370417946046096741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501499580278630697397827 8252249370417946046096741)
          ·
            refine ⟨1547296756953364883643139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8252249370417946046096741 1547296756953364883643139)
            ·
              refine ⟨2320945135430047325464709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547296756953364883643139 2320945135430047325464709)
              ·
                refine ⟨435177212893133873524633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2320945135430047325464709 435177212893133873524633)
                ·
                  refine ⟨326382909669850405143475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435177212893133873524633 326382909669850405143475)
                  ·
                    refine ⟨489574364504775607715213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326382909669850405143475 489574364504775607715213)
                    ·
                      refine ⟨183590386689290852893205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489574364504775607715213 183590386689290852893205)
                      ·
                        rfl

theorem cell23_357541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_357541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357541 prefixEnd_357541 := by exact prefixLift 357541
  have htrace : WordTrace (prefixWord ++ tailWord_357541) baseStart_357541 baseEnd_357541 := by
    simpa [prefixWord, tailWord_357541, baseEnd_357541] using wordTrace_append hprefix tailTrace_357541
  have hstable : (prefixWord ++ tailWord_357541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357541).length < 2 ^ (prefixWord ++ tailWord_357541).sum := by decide
  have hdescent : baseEnd_357541 < baseStart_357541 := by decide
  rcases family_descends (prefixWord ++ tailWord_357541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357567 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_357567 : Nat := 118140960795 + 357567 * 2 ^ 59
def prefixEnd_357567 : Nat := 4983230072969 + 3 ^ 40 * 357567 * 2
def baseEnd_357567 : Nat := 183603737186307751168085

theorem tailTrace_357567 : CollatzResearch.WordTrace tailWord_357567 prefixEnd_357567 183603737186307751168085 := by
  unfold tailWord_357567
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041539895603301426870955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8694359930402200951247303 13041539895603301426870955)
  ·
    refine ⟨19562309843404952140306433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13041539895603301426870955 19562309843404952140306433)
    ·
      refine ⟨14671732382553714105229825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19562309843404952140306433 14671732382553714105229825)
      ·
        refine ⟨11003799286915285578922369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14671732382553714105229825 11003799286915285578922369)
        ·
          refine ⟨8252849465186464184191777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11003799286915285578922369 8252849465186464184191777)
          ·
            refine ⟨6189637098889848138143833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8252849465186464184191777 6189637098889848138143833)
            ·
              refine ⟨4642227824167386103607875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6189637098889848138143833 4642227824167386103607875)
              ·
                refine ⟨6963341736251079155411813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4642227824167386103607875 6963341736251079155411813)
                ·
                  refine ⟨1305626575547077341639715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6963341736251079155411813 1305626575547077341639715)
                  ·
                    refine ⟨1958439863320616012459573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1305626575547077341639715 1958439863320616012459573)
                    ·
                      refine ⟨183603737186307751168085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1958439863320616012459573 183603737186307751168085)
                      ·
                        rfl

theorem cell23_357567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_357567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357567 prefixEnd_357567 := by exact prefixLift 357567
  have htrace : WordTrace (prefixWord ++ tailWord_357567) baseStart_357567 baseEnd_357567 := by
    simpa [prefixWord, tailWord_357567, baseEnd_357567] using wordTrace_append hprefix tailTrace_357567
  have hstable : (prefixWord ++ tailWord_357567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357567).length < 2 ^ (prefixWord ++ tailWord_357567).sum := by decide
  have hdescent : baseEnd_357567 < baseStart_357567 := by decide
  rcases family_descends (prefixWord ++ tailWord_357567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357615 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 1, 4, 2]
def baseStart_357615 : Nat := 118140960795 + 357615 * 2 ^ 59
def prefixEnd_357615 : Nat := 4983230072969 + 3 ^ 40 * 357615 * 2
def baseEnd_357615 : Nat := 183628384257723563367865

theorem tailTrace_357615 : CollatzResearch.WordTrace tailWord_357615 prefixEnd_357615 183628384257723563367865 := by
  unfold tailWord_357615
  simp only [CollatzResearch.WordTrace]
  refine ⟨13043290599429405624618299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8695527066286270416412199 13043290599429405624618299)
  ·
    refine ⟨19564935899144108436927449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13043290599429405624618299 19564935899144108436927449)
    ·
      refine ⟨14673701924358081327695587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19564935899144108436927449 14673701924358081327695587)
      ·
        refine ⟨22010552886537121991543381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14673701924358081327695587 22010552886537121991543381)
        ·
          refine ⟨257936166639106898338399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 22010552886537121991543381 257936166639106898338399)
          ·
            refine ⟨386904249958660347507599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257936166639106898338399 386904249958660347507599)
            ·
              refine ⟨580356374937990521261399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386904249958660347507599 580356374937990521261399)
              ·
                refine ⟨870534562406985781892099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580356374937990521261399 870534562406985781892099)
                ·
                  refine ⟨1305801843610478672838149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870534562406985781892099 1305801843610478672838149)
                  ·
                    refine ⟨244837845676964751157153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1305801843610478672838149 244837845676964751157153)
                    ·
                      refine ⟨183628384257723563367865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 244837845676964751157153 183628384257723563367865)
                      ·
                        rfl

theorem cell23_357615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 4, 2].length) (baseStart_357615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357615 prefixEnd_357615 := by exact prefixLift 357615
  have htrace : WordTrace (prefixWord ++ tailWord_357615) baseStart_357615 baseEnd_357615 := by
    simpa [prefixWord, tailWord_357615, baseEnd_357615] using wordTrace_append hprefix tailTrace_357615
  have hstable : (prefixWord ++ tailWord_357615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357615).length < 2 ^ (prefixWord ++ tailWord_357615).sum := by decide
  have hdescent : baseEnd_357615 < baseStart_357615 := by decide
  rcases family_descends (prefixWord ++ tailWord_357615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357661 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_357661 : Nat := 118140960795 + 357661 * 2 ^ 59
def prefixEnd_357661 : Nat := 4983230072969 + 3 ^ 40 * 357661 * 2
def baseEnd_357661 : Nat := 183652004367830383392653

theorem tailTrace_357661 : CollatzResearch.WordTrace tailWord_357661 prefixEnd_357661 183652004367830383392653 := by
  unfold tailWord_357661
  simp only [CollatzResearch.WordTrace]
  refine ⟨13044968357262755480792837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8696645571508503653861891 13044968357262755480792837)
  ·
    refine ⟨2445931566986766652648657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13044968357262755480792837 2445931566986766652648657)
    ·
      refine ⟨1834448675240074989486493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2445931566986766652648657 1834448675240074989486493)
      ·
        refine ⟨687918253215028121057435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1834448675240074989486493 687918253215028121057435)
        ·
          refine ⟨1031877379822542181586153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687918253215028121057435 1031877379822542181586153)
          ·
            refine ⟨773908034866906636189615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031877379822542181586153 773908034866906636189615)
            ·
              refine ⟨1160862052300359954284423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773908034866906636189615 1160862052300359954284423)
              ·
                refine ⟨1741293078450539931426635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160862052300359954284423 1741293078450539931426635)
                ·
                  refine ⟨2611939617675809897139953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741293078450539931426635 2611939617675809897139953)
                  ·
                    refine ⟨1958954713256857422854965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2611939617675809897139953 1958954713256857422854965)
                    ·
                      refine ⟨183652004367830383392653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1958954713256857422854965 183652004367830383392653)
                      ·
                        rfl

theorem cell23_357661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_357661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357661 prefixEnd_357661 := by exact prefixLift 357661
  have htrace : WordTrace (prefixWord ++ tailWord_357661) baseStart_357661 baseEnd_357661 := by
    simpa [prefixWord, tailWord_357661, baseEnd_357661] using wordTrace_append hprefix tailTrace_357661
  have hstable : (prefixWord ++ tailWord_357661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357661).length < 2 ^ (prefixWord ++ tailWord_357661).sum := by decide
  have hdescent : baseEnd_357661 < baseStart_357661 := by decide
  rcases family_descends (prefixWord ++ tailWord_357661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357714 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_357714 : Nat := 118140960795 + 357714 * 2 ^ 59
def prefixEnd_357714 : Nat := 4983230072969 + 3 ^ 40 * 357714 * 2
def baseEnd_357714 : Nat := 183679218842518676029909

theorem tailTrace_357714 : CollatzResearch.WordTrace tailWord_357714 prefixEnd_357714 183679218842518676029909 := by
  unfold tailWord_357714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3261725356517686383118049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8697934284047163688314797 3261725356517686383118049)
  ·
    refine ⟨2446294017388264787338537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3261725356517686383118049 2446294017388264787338537)
    ·
      refine ⟨1834720513041198590503903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2446294017388264787338537 1834720513041198590503903)
      ·
        refine ⟨2752080769561797885755855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1834720513041198590503903 2752080769561797885755855)
        ·
          refine ⟨4128121154342696828633783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752080769561797885755855 4128121154342696828633783)
          ·
            refine ⟨6192181731514045242950675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4128121154342696828633783 6192181731514045242950675)
            ·
              refine ⟨9288272597271067864426013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192181731514045242950675 9288272597271067864426013)
              ·
                refine ⟨3483102223976650449159755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9288272597271067864426013 3483102223976650449159755)
                ·
                  refine ⟨5224653335964975673739633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483102223976650449159755 5224653335964975673739633)
                  ·
                    refine ⟨3918490001973731755304725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5224653335964975673739633 3918490001973731755304725)
                    ·
                      refine ⟨183679218842518676029909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3918490001973731755304725 183679218842518676029909)
                      ·
                        rfl

theorem cell23_357714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_357714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357714 prefixEnd_357714 := by exact prefixLift 357714
  have htrace : WordTrace (prefixWord ++ tailWord_357714) baseStart_357714 baseEnd_357714 := by
    simpa [prefixWord, tailWord_357714, baseEnd_357714] using wordTrace_append hprefix tailTrace_357714
  have hstable : (prefixWord ++ tailWord_357714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357714).length < 2 ^ (prefixWord ++ tailWord_357714).sum := by decide
  have hdescent : baseEnd_357714 < baseStart_357714 := by decide
  rcases family_descends (prefixWord ++ tailWord_357714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357741 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_357741 : Nat := 118140960795 + 357741 * 2 ^ 59
def prefixEnd_357741 : Nat := 4983230072969 + 3 ^ 40 * 357741 * 2
def baseEnd_357741 : Nat := 61231027606730023464095

theorem tailTrace_357741 : CollatzResearch.WordTrace tailWord_357741 prefixEnd_357741 61231027606730023464095 := by
  unfold tailWord_357741
  simp only [CollatzResearch.WordTrace]
  refine ⟨13047886196972929143705077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8698590797981952762470051 13047886196972929143705077)
  ·
    refine ⟨1223239330966212107222351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13047886196972929143705077 1223239330966212107222351)
    ·
      refine ⟨1834858996449318160833527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1223239330966212107222351 1834858996449318160833527)
      ·
        refine ⟨2752288494673977241250291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1834858996449318160833527 2752288494673977241250291)
        ·
          refine ⟨4128432742010965861875437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752288494673977241250291 4128432742010965861875437)
          ·
            refine ⟨1548162278254112198203289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4128432742010965861875437 1548162278254112198203289)
            ·
              refine ⟨1161121708690584148652467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548162278254112198203289 1161121708690584148652467)
              ·
                refine ⟨1741682563035876222978701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161121708690584148652467 1741682563035876222978701)
                ·
                  refine ⟨653130961138453583617013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1741682563035876222978701 653130961138453583617013)
                  ·
                    refine ⟨61231027606730023464095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 653130961138453583617013 61231027606730023464095)
                    ·
                      rfl

theorem cell23_357741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_357741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357741 prefixEnd_357741 := by exact prefixLift 357741
  have htrace : WordTrace (prefixWord ++ tailWord_357741) baseStart_357741 baseEnd_357741 := by
    simpa [prefixWord, tailWord_357741, baseEnd_357741] using wordTrace_append hprefix tailTrace_357741
  have hstable : (prefixWord ++ tailWord_357741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357741).length < 2 ^ (prefixWord ++ tailWord_357741).sum := by decide
  have hdescent : baseEnd_357741 < baseStart_357741 := by decide
  rcases family_descends (prefixWord ++ tailWord_357741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357742 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_357742 : Nat := 118140960795 + 357742 * 2 ^ 59
def prefixEnd_357742 : Nat := 4983230072969 + 3 ^ 40 * 357742 * 2
def baseEnd_357742 : Nat := 183693596300844566479781

theorem tailTrace_357742 : CollatzResearch.WordTrace tailWord_357742 prefixEnd_357742 183693596300844566479781 := by
  unfold tailWord_357742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630990333746163289311435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8698615113312870876327653 1630990333746163289311435)
  ·
    refine ⟨2446485500619244933967153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1630990333746163289311435 2446485500619244933967153)
    ·
      refine ⟨1834864125464433700475365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2446485500619244933967153 1834864125464433700475365)
      ·
        refine ⟨344037023524581318839131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1834864125464433700475365 344037023524581318839131)
        ·
          refine ⟨516055535286871978258697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344037023524581318839131 516055535286871978258697)
          ·
            refine ⟨387041651465153983694023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516055535286871978258697 387041651465153983694023)
            ·
              refine ⟨580562477197730975541035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387041651465153983694023 580562477197730975541035)
              ·
                refine ⟨870843715796596463311553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580562477197730975541035 870843715796596463311553)
                ·
                  refine ⟨653132786847447347483665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 870843715796596463311553 653132786847447347483665)
                  ·
                    refine ⟨489849590135585510612749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 653132786847447347483665 489849590135585510612749)
                    ·
                      refine ⟨183693596300844566479781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489849590135585510612749 183693596300844566479781)
                      ·
                        rfl

theorem cell23_357742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_357742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357742 prefixEnd_357742 := by exact prefixLift 357742
  have htrace : WordTrace (prefixWord ++ tailWord_357742) baseStart_357742 baseEnd_357742 := by
    simpa [prefixWord, tailWord_357742, baseEnd_357742] using wordTrace_append hprefix tailTrace_357742
  have hstable : (prefixWord ++ tailWord_357742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357742).length < 2 ^ (prefixWord ++ tailWord_357742).sum := by decide
  have hdescent : baseEnd_357742 < baseStart_357742 := by decide
  rcases family_descends (prefixWord ++ tailWord_357742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357755 : List Nat := [1, 1, 1, 1, 1, 6, 4, 3, 1, 1, 3]
def baseStart_357755 : Nat := 118140960795 + 357755 * 2 ^ 59
def prefixEnd_357755 : Nat := 4983230072969 + 3 ^ 40 * 357755 * 2
def baseEnd_357755 : Nat := 183700271549353015617221

theorem tailTrace_357755 : CollatzResearch.WordTrace tailWord_357755 prefixEnd_357755 183700271549353015617221 := by
  unfold tailWord_357755
  simp only [CollatzResearch.WordTrace]
  refine ⟨13048396818922209534714719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8698931212614806356476479 13048396818922209534714719)
  ·
    refine ⟨19572595228383314302072079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13048396818922209534714719 19572595228383314302072079)
    ·
      refine ⟨29358892842574971453108119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19572595228383314302072079 29358892842574971453108119)
      ·
        refine ⟨44038339263862457179662179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29358892842574971453108119 44038339263862457179662179)
        ·
          refine ⟨66057508895793685769493269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44038339263862457179662179 66057508895793685769493269)
          ·
            refine ⟨3096445729490329020444997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66057508895793685769493269 3096445729490329020444997)
            ·
              refine ⟨580583574279436691333437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3096445729490329020444997 580583574279436691333437)
              ·
                refine ⟨217718840354788759250039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 580583574279436691333437 217718840354788759250039)
                ·
                  refine ⟨326578260532183138875059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217718840354788759250039 326578260532183138875059)
                  ·
                    refine ⟨489867390798274708312589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326578260532183138875059 489867390798274708312589)
                    ·
                      refine ⟨183700271549353015617221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489867390798274708312589 183700271549353015617221)
                      ·
                        rfl

theorem cell23_357755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 1, 1, 3].length) (baseStart_357755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357755 prefixEnd_357755 := by exact prefixLift 357755
  have htrace : WordTrace (prefixWord ++ tailWord_357755) baseStart_357755 baseEnd_357755 := by
    simpa [prefixWord, tailWord_357755, baseEnd_357755] using wordTrace_append hprefix tailTrace_357755
  have hstable : (prefixWord ++ tailWord_357755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357755).length < 2 ^ (prefixWord ++ tailWord_357755).sum := by decide
  have hdescent : baseEnd_357755 < baseStart_357755 := by decide
  rcases family_descends (prefixWord ++ tailWord_357755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357771 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 4, 4]
def baseStart_357771 : Nat := 118140960795 + 357771 * 2 ^ 59
def prefixEnd_357771 : Nat := 4983230072969 + 3 ^ 40 * 357771 * 2
def baseEnd_357771 : Nat := 61236162413274984339049

theorem tailTrace_357771 : CollatzResearch.WordTrace tailWord_357771 prefixEnd_357771 61236162413274984339049 := by
  unfold tailWord_357771
  simp only [CollatzResearch.WordTrace]
  refine ⟨13048980386864244267297167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8699320257909496178198111 13048980386864244267297167)
  ·
    refine ⟨19573470580296366400945751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13048980386864244267297167 19573470580296366400945751)
    ·
      refine ⟨29360205870444549601418627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19573470580296366400945751 29360205870444549601418627)
      ·
        refine ⟨44040308805666824402127941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29360205870444549601418627 44040308805666824402127941)
        ·
          refine ⟨8257557901062529575398989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44040308805666824402127941 8257557901062529575398989)
          ·
            refine ⟨3096584212898448590774621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8257557901062529575398989 3096584212898448590774621)
            ·
              refine ⟨1161219079836918221540483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3096584212898448590774621 1161219079836918221540483)
              ·
                refine ⟨1741828619755377332310725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161219079836918221540483 1741828619755377332310725)
                ·
                  refine ⟨326592866204133249808261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1741828619755377332310725 326592866204133249808261)
                  ·
                    refine ⟨61236162413274984339049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326592866204133249808261 61236162413274984339049)
                    ·
                      rfl

theorem cell23_357771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 4].length) (baseStart_357771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357771 prefixEnd_357771 := by exact prefixLift 357771
  have htrace : WordTrace (prefixWord ++ tailWord_357771) baseStart_357771 baseEnd_357771 := by
    simpa [prefixWord, tailWord_357771, baseEnd_357771] using wordTrace_append hprefix tailTrace_357771
  have hstable : (prefixWord ++ tailWord_357771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357771).length < 2 ^ (prefixWord ++ tailWord_357771).sum := by decide
  have hdescent : baseEnd_357771 < baseStart_357771 := by decide
  rcases family_descends (prefixWord ++ tailWord_357771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357781 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_357781 : Nat := 118140960795 + 357781 * 2 ^ 59
def prefixEnd_357781 : Nat := 4983230072969 + 3 ^ 40 * 357781 * 2
def baseEnd_357781 : Nat := 183713622046369913892101

theorem tailTrace_357781 : CollatzResearch.WordTrace tailWord_357781 prefixEnd_357781 183713622046369913892101 := by
  unfold tailWord_357781
  simp only [CollatzResearch.WordTrace]
  refine ⟨13049345116828015975161197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8699563411218677316774131 13049345116828015975161197)
  ·
    refine ⟨4893504418810505990685449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13049345116828015975161197 4893504418810505990685449)
    ·
      refine ⟨3670128314107879493014087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4893504418810505990685449 3670128314107879493014087)
      ·
        refine ⟨5505192471161819239521131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670128314107879493014087 5505192471161819239521131)
        ·
          refine ⟨8257788706742728859281697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5505192471161819239521131 8257788706742728859281697)
          ·
            refine ⟨6193341530057046644461273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8257788706742728859281697 6193341530057046644461273)
            ·
              refine ⟨4645006147542784983345955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6193341530057046644461273 4645006147542784983345955)
              ·
                refine ⟨6967509221314177475018933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4645006147542784983345955 6967509221314177475018933)
                ·
                  refine ⟨653203989498204138283025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6967509221314177475018933 653203989498204138283025)
                  ·
                    refine ⟨489902992123653103712269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 653203989498204138283025 489902992123653103712269)
                    ·
                      refine ⟨183713622046369913892101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489902992123653103712269 183713622046369913892101)
                      ·
                        rfl

theorem cell23_357781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_357781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357781 prefixEnd_357781 := by exact prefixLift 357781
  have htrace : WordTrace (prefixWord ++ tailWord_357781) baseStart_357781 baseEnd_357781 := by
    simpa [prefixWord, tailWord_357781, baseEnd_357781] using wordTrace_append hprefix tailTrace_357781
  have hstable : (prefixWord ++ tailWord_357781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357781).length < 2 ^ (prefixWord ++ tailWord_357781).sum := by decide
  have hdescent : baseEnd_357781 < baseStart_357781 := by decide
  rcases family_descends (prefixWord ++ tailWord_357781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357791 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 6]
def baseStart_357791 : Nat := 118140960795 + 357791 * 2 ^ 59
def prefixEnd_357791 : Nat := 4983230072969 + 3 ^ 40 * 357791 * 2
def baseEnd_357791 : Nat := 183718756852914874767055

theorem tailTrace_357791 : CollatzResearch.WordTrace tailWord_357791 prefixEnd_357791 183718756852914874767055 := by
  unfold tailWord_357791
  simp only [CollatzResearch.WordTrace]
  refine ⟨13049709846791787683025227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8699806564527858455350151 13049709846791787683025227)
  ·
    refine ⟨19574564770187681524537841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13049709846791787683025227 19574564770187681524537841)
    ·
      refine ⟨14680923577640761143403381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19574564770187681524537841 14680923577640761143403381)
      ·
        refine ⟨1376336585403821357194067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14680923577640761143403381 1376336585403821357194067)
        ·
          refine ⟨2064504878105732035791101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376336585403821357194067 2064504878105732035791101)
          ·
            refine ⟨774189329289649513421663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2064504878105732035791101 774189329289649513421663)
            ·
              refine ⟨1161283993934474270132495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774189329289649513421663 1161283993934474270132495)
              ·
                refine ⟨1741925990901711405198743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161283993934474270132495 1741925990901711405198743)
                ·
                  refine ⟨2612888986352567107798115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741925990901711405198743 2612888986352567107798115)
                  ·
                    refine ⟨3919333479528850661697173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2612888986352567107798115 3919333479528850661697173)
                    ·
                      refine ⟨183718756852914874767055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3919333479528850661697173 183718756852914874767055)
                      ·
                        rfl

theorem cell23_357791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_357791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357791 prefixEnd_357791 := by exact prefixLift 357791
  have htrace : WordTrace (prefixWord ++ tailWord_357791) baseStart_357791 baseEnd_357791 := by
    simpa [prefixWord, tailWord_357791, baseEnd_357791] using wordTrace_append hprefix tailTrace_357791
  have hstable : (prefixWord ++ tailWord_357791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357791).length < 2 ^ (prefixWord ++ tailWord_357791).sum := by decide
  have hdescent : baseEnd_357791 < baseStart_357791 := by decide
  rcases family_descends (prefixWord ++ tailWord_357791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357811 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 3]
def baseStart_357811 : Nat := 118140960795 + 357811 * 2 ^ 59
def prefixEnd_357811 : Nat := 4983230072969 + 3 ^ 40 * 357811 * 2
def baseEnd_357811 : Nat := 183729026466004796516963

theorem tailTrace_357811 : CollatzResearch.WordTrace tailWord_357811 prefixEnd_357811 183729026466004796516963 := by
  unfold tailWord_357811
  simp only [CollatzResearch.WordTrace]
  refine ⟨13050439306719331098753287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8700292871146220732502191 13050439306719331098753287)
  ·
    refine ⟨19575658960078996648129931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13050439306719331098753287 19575658960078996648129931)
    ·
      refine ⟨29363488440118494972194897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19575658960078996648129931 29363488440118494972194897)
      ·
        refine ⟨22022616330088871229146173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29363488440118494972194897 22022616330088871229146173)
        ·
          refine ⟨8258481123783326710929815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22022616330088871229146173 8258481123783326710929815)
          ·
            refine ⟨12387721685674990066394723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8258481123783326710929815 12387721685674990066394723)
            ·
              refine ⟨18581582528512485099592085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12387721685674990066394723 18581582528512485099592085)
              ·
                refine ⟨871011681024022739043379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18581582528512485099592085 871011681024022739043379)
                ·
                  refine ⟨1306517521536034108565069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871011681024022739043379 1306517521536034108565069)
                  ·
                    refine ⟨489944070576012790711901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1306517521536034108565069 489944070576012790711901)
                    ·
                      refine ⟨183729026466004796516963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489944070576012790711901 183729026466004796516963)
                      ·
                        rfl

theorem cell23_357811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 3].length) (baseStart_357811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357811 prefixEnd_357811 := by exact prefixLift 357811
  have htrace : WordTrace (prefixWord ++ tailWord_357811) baseStart_357811 baseEnd_357811 := by
    simpa [prefixWord, tailWord_357811, baseEnd_357811] using wordTrace_append hprefix tailTrace_357811
  have hstable : (prefixWord ++ tailWord_357811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357811).length < 2 ^ (prefixWord ++ tailWord_357811).sum := by decide
  have hdescent : baseEnd_357811 < baseStart_357811 := by decide
  rcases family_descends (prefixWord ++ tailWord_357811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357845 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_357845 : Nat := 118140960795 + 357845 * 2 ^ 59
def prefixEnd_357845 : Nat := 4983230072969 + 3 ^ 40 * 357845 * 2
def baseEnd_357845 : Nat := 183746484808257663491807

theorem tailTrace_357845 : CollatzResearch.WordTrace tailWord_357845 prefixEnd_357845 183746484808257663491807 := by
  unfold tailWord_357845
  simp only [CollatzResearch.WordTrace]
  refine ⟨13051679388596154905490989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8701119592397436603660659 13051679388596154905490989)
  ·
    refine ⟨4894379770723558089559121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13051679388596154905490989 4894379770723558089559121)
    ·
      refine ⟨3670784828042668567169341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4894379770723558089559121 3670784828042668567169341)
      ·
        refine ⟨1376544310516000712688503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3670784828042668567169341 1376544310516000712688503)
        ·
          refine ⟨2064816465774001069032755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376544310516000712688503 2064816465774001069032755)
          ·
            refine ⟨3097224698661001603549133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064816465774001069032755 3097224698661001603549133)
            ·
              refine ⟨1161459261997875601330925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3097224698661001603549133 1161459261997875601330925)
              ·
                refine ⟨435547223249203350499097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1161459261997875601330925 435547223249203350499097)
                ·
                  refine ⟨326660417436902512874323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435547223249203350499097 326660417436902512874323)
                  ·
                    refine ⟨489990626155353769311485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326660417436902512874323 489990626155353769311485)
                    ·
                      refine ⟨183746484808257663491807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 489990626155353769311485 183746484808257663491807)
                      ·
                        rfl

theorem cell23_357845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_357845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357845 prefixEnd_357845 := by exact prefixLift 357845
  have htrace : WordTrace (prefixWord ++ tailWord_357845) baseStart_357845 baseEnd_357845 := by
    simpa [prefixWord, tailWord_357845, baseEnd_357845] using wordTrace_append hprefix tailTrace_357845
  have hstable : (prefixWord ++ tailWord_357845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357845).length < 2 ^ (prefixWord ++ tailWord_357845).sum := by decide
  have hdescent : baseEnd_357845 < baseStart_357845 := by decide
  rcases family_descends (prefixWord ++ tailWord_357845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357871 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_357871 : Nat := 118140960795 + 357871 * 2 ^ 59
def prefixEnd_357871 : Nat := 4983230072969 + 3 ^ 40 * 357871 * 2
def baseEnd_357871 : Nat := 183759835305274561766687

theorem tailTrace_357871 : CollatzResearch.WordTrace tailWord_357871 prefixEnd_357871 183759835305274561766687 := by
  unfold tailWord_357871
  simp only [CollatzResearch.WordTrace]
  refine ⟨13052627686501961345937467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8701751791001307563958311 13052627686501961345937467)
  ·
    refine ⟨19578941529752942018906201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13052627686501961345937467 19578941529752942018906201)
    ·
      refine ⟨14684206147314706514179651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19578941529752942018906201 14684206147314706514179651)
      ·
        refine ⟨22026309220972059771269477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14684206147314706514179651 22026309220972059771269477)
        ·
          refine ⟨4129932978932261207113027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22026309220972059771269477 4129932978932261207113027)
          ·
            refine ⟨6194899468398391810669541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129932978932261207113027 6194899468398391810669541)
            ·
              refine ⟨1161543650324698464500539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6194899468398391810669541 1161543650324698464500539)
              ·
                refine ⟨1742315475487047696750809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161543650324698464500539 1742315475487047696750809)
                ·
                  refine ⟨1306736606615285772563107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1742315475487047696750809 1306736606615285772563107)
                  ·
                    refine ⟨1960104909922928658844661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1306736606615285772563107 1960104909922928658844661)
                    ·
                      refine ⟨183759835305274561766687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1960104909922928658844661 183759835305274561766687)
                      ·
                        rfl

theorem cell23_357871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_357871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357871 prefixEnd_357871 := by exact prefixLift 357871
  have htrace : WordTrace (prefixWord ++ tailWord_357871) baseStart_357871 baseEnd_357871 := by
    simpa [prefixWord, tailWord_357871, baseEnd_357871] using wordTrace_append hprefix tailTrace_357871
  have hstable : (prefixWord ++ tailWord_357871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357871).length < 2 ^ (prefixWord ++ tailWord_357871).sum := by decide
  have hdescent : baseEnd_357871 < baseStart_357871 := by decide
  rcases family_descends (prefixWord ++ tailWord_357871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357872 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 1, 3, 2]
def baseStart_357872 : Nat := 118140960795 + 357872 * 2 ^ 59
def prefixEnd_357872 : Nat := 4983230072969 + 3 ^ 40 * 357872 * 2
def baseEnd_357872 : Nat := 183760348785929057854183

theorem tailTrace_357872 : CollatzResearch.WordTrace tailWord_357872 prefixEnd_357872 183760348785929057854183 := by
  unfold tailWord_357872
  simp only [CollatzResearch.WordTrace]
  refine ⟨6526332079749169258361935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8701776106332225677815913 6526332079749169258361935)
  ·
    refine ⟨9789498119623753887542903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6526332079749169258361935 9789498119623753887542903)
    ·
      refine ⟨14684247179435630831314355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9789498119623753887542903 14684247179435630831314355)
      ·
        refine ⟨22026370769153446246971533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14684247179435630831314355 22026370769153446246971533)
        ·
          refine ⟨8259889038432542342614325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22026370769153446246971533 8259889038432542342614325)
          ·
            refine ⟨774364597353050844620093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8259889038432542342614325 774364597353050844620093)
            ·
              refine ⟨290386724007394066732535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 774364597353050844620093 290386724007394066732535)
              ·
                refine ⟨435580086011091100098803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290386724007394066732535 435580086011091100098803)
                ·
                  refine ⟨653370129016636650148205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435580086011091100098803 653370129016636650148205)
                  ·
                    refine ⟨245013798381238743805577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653370129016636650148205 245013798381238743805577)
                    ·
                      refine ⟨183760348785929057854183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 245013798381238743805577 183760348785929057854183)
                      ·
                        rfl

theorem cell23_357872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 3, 2].length) (baseStart_357872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357872 prefixEnd_357872 := by exact prefixLift 357872
  have htrace : WordTrace (prefixWord ++ tailWord_357872) baseStart_357872 baseEnd_357872 := by
    simpa [prefixWord, tailWord_357872, baseEnd_357872] using wordTrace_append hprefix tailTrace_357872
  have hstable : (prefixWord ++ tailWord_357872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357872).length < 2 ^ (prefixWord ++ tailWord_357872).sum := by decide
  have hdescent : baseEnd_357872 < baseStart_357872 := by decide
  rcases family_descends (prefixWord ++ tailWord_357872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357881 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_357881 : Nat := 118140960795 + 357881 * 2 ^ 59
def prefixEnd_357881 : Nat := 4983230072969 + 3 ^ 40 * 357881 * 2
def baseEnd_357881 : Nat := 183764970111819522641641

theorem tailTrace_357881 : CollatzResearch.WordTrace tailWord_357881 prefixEnd_357881 183764970111819522641641 := by
  unfold tailWord_357881
  simp only [CollatzResearch.WordTrace]
  refine ⟨13052992416465733053801497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8701994944310488702534331 13052992416465733053801497)
  ·
    refine ⟨9789744312349299790351123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13052992416465733053801497 9789744312349299790351123)
    ·
      refine ⟨14684616468523949685526685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9789744312349299790351123 14684616468523949685526685)
      ·
        refine ⟨5506731175696481132072507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14684616468523949685526685 5506731175696481132072507)
        ·
          refine ⟨8260096763544721698108761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506731175696481132072507 8260096763544721698108761)
          ·
            refine ⟨6195072572658541273581571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8260096763544721698108761 6195072572658541273581571)
            ·
              refine ⟨9292608858987811910372357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6195072572658541273581571 9292608858987811910372357)
              ·
                refine ⟨1742364161060214733194817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9292608858987811910372357 1742364161060214733194817)
                ·
                  refine ⟨1306773120795161049896113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1742364161060214733194817 1306773120795161049896113)
                  ·
                    refine ⟨980079840596370787422085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1306773120795161049896113 980079840596370787422085)
                    ·
                      refine ⟨183764970111819522641641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 980079840596370787422085 183764970111819522641641)
                      ·
                        rfl

theorem cell23_357881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_357881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357881 prefixEnd_357881 := by exact prefixLift 357881
  have htrace : WordTrace (prefixWord ++ tailWord_357881) baseStart_357881 baseEnd_357881 := by
    simpa [prefixWord, tailWord_357881, baseEnd_357881] using wordTrace_append hprefix tailTrace_357881
  have hstable : (prefixWord ++ tailWord_357881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357881).length < 2 ^ (prefixWord ++ tailWord_357881).sum := by decide
  have hdescent : baseEnd_357881 < baseStart_357881 := by decide
  rcases family_descends (prefixWord ++ tailWord_357881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357898 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_357898 : Nat := 118140960795 + 357898 * 2 ^ 59
def prefixEnd_357898 : Nat := 4983230072969 + 3 ^ 40 * 357898 * 2
def baseEnd_357898 : Nat := 183773699282945956129063

theorem tailTrace_357898 : CollatzResearch.WordTrace tailWord_357898 prefixEnd_357898 183773699282945956129063 := by
  unfold tailWord_357898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3263403114351036239292587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8702408304936096638113565 3263403114351036239292587)
  ·
    refine ⟨4895104671526554358938881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3263403114351036239292587 4895104671526554358938881)
    ·
      refine ⟨3671328503644915769204161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4895104671526554358938881 3671328503644915769204161)
      ·
        refine ⟨2753496377733686826903121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3671328503644915769204161 2753496377733686826903121)
        ·
          refine ⟨2065122283300265120177341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2753496377733686826903121 2065122283300265120177341)
          ·
            refine ⟨774420856237599420066503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2065122283300265120177341 774420856237599420066503)
            ·
              refine ⟨1161631284356399130099755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774420856237599420066503 1161631284356399130099755)
              ·
                refine ⟨1742446926534598695149633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161631284356399130099755 1742446926534598695149633)
                ·
                  refine ⟨1306835194900949021362225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1742446926534598695149633 1306835194900949021362225)
                  ·
                    refine ⟨980126396175711766021669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1306835194900949021362225 980126396175711766021669)
                    ·
                      refine ⟨183773699282945956129063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 980126396175711766021669 183773699282945956129063)
                      ·
                        rfl

theorem cell23_357898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_357898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357898 prefixEnd_357898 := by exact prefixLift 357898
  have htrace : WordTrace (prefixWord ++ tailWord_357898) baseStart_357898 baseEnd_357898 := by
    simpa [prefixWord, tailWord_357898, baseEnd_357898] using wordTrace_append hprefix tailTrace_357898
  have hstable : (prefixWord ++ tailWord_357898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357898).length < 2 ^ (prefixWord ++ tailWord_357898).sum := by decide
  have hdescent : baseEnd_357898 < baseStart_357898 := by decide
  rcases family_descends (prefixWord ++ tailWord_357898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357902 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2]
def baseStart_357902 : Nat := 118140960795 + 357902 * 2 ^ 59
def prefixEnd_357902 : Nat := 4983230072969 + 3 ^ 40 * 357902 * 2
def baseEnd_357902 : Nat := 183775753205563940479045

theorem tailTrace_357902 : CollatzResearch.WordTrace tailWord_357902 prefixEnd_357902 183775753205563940479045 := by
  unfold tailWord_357902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631719793673706705039495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8702505566259769093543973 1631719793673706705039495)
  ·
    refine ⟨2447579690510560057559243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1631719793673706705039495 2447579690510560057559243)
    ·
      refine ⟨3671369535765840086338865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2447579690510560057559243 3671369535765840086338865)
      ·
        refine ⟨2753527151824380064754149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3671369535765840086338865 2753527151824380064754149)
        ·
          refine ⟨516286340967071262141403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2753527151824380064754149 516286340967071262141403)
          ·
            refine ⟨774429511450606893212105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516286340967071262141403 774429511450606893212105)
            ·
              refine ⟨580822133587955169909079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 774429511450606893212105 580822133587955169909079)
              ·
                refine ⟨871233200381932754863619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580822133587955169909079 871233200381932754863619)
                ·
                  refine ⟨1306849800572899132295429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871233200381932754863619 1306849800572899132295429)
                  ·
                    refine ⟨245034337607418587305393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1306849800572899132295429 245034337607418587305393)
                    ·
                      refine ⟨183775753205563940479045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 245034337607418587305393 183775753205563940479045)
                      ·
                        rfl

theorem cell23_357902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_357902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357902 prefixEnd_357902 := by exact prefixLift 357902
  have htrace : WordTrace (prefixWord ++ tailWord_357902) baseStart_357902 baseEnd_357902 := by
    simpa [prefixWord, tailWord_357902, baseEnd_357902] using wordTrace_append hprefix tailTrace_357902
  have hstable : (prefixWord ++ tailWord_357902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357902).length < 2 ^ (prefixWord ++ tailWord_357902).sum := by decide
  have hdescent : baseEnd_357902 < baseStart_357902 := by decide
  rcases family_descends (prefixWord ++ tailWord_357902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357968 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 3, 4]
def baseStart_357968 : Nat := 118140960795 + 357968 * 2 ^ 59
def prefixEnd_357968 : Nat := 4983230072969 + 3 ^ 40 * 357968 * 2
def baseEnd_357968 : Nat := 61269880976253560751247

theorem tailTrace_357968 : CollatzResearch.WordTrace tailWord_357968 prefixEnd_357968 61269880976253560751247 := by
  unfold tailWord_357968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6528082783575273456109279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8704110378100364608145705 6528082783575273456109279)
  ·
    refine ⟨9792124175362910184163919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6528082783575273456109279 9792124175362910184163919)
    ·
      refine ⟨14688186263044365276245879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9792124175362910184163919 14688186263044365276245879)
      ·
        refine ⟨22032279394566547914368819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14688186263044365276245879 22032279394566547914368819)
        ·
          refine ⟨33048419091849821871553229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22032279394566547914368819 33048419091849821871553229)
          ·
            refine ⟨12393157159443683201832461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33048419091849821871553229 12393157159443683201832461)
            ·
              refine ⟨4647433934791381200687173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12393157159443683201832461 4647433934791381200687173)
              ·
                refine ⟨871393862773383975128845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4647433934791381200687173 871393862773383975128845)
                ·
                  refine ⟨326772698540018990673317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871393862773383975128845 326772698540018990673317)
                  ·
                    refine ⟨61269880976253560751247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326772698540018990673317 61269880976253560751247)
                    ·
                      rfl

theorem cell23_357968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3, 4].length) (baseStart_357968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357968 prefixEnd_357968 := by exact prefixLift 357968
  have htrace : WordTrace (prefixWord ++ tailWord_357968) baseStart_357968 baseEnd_357968 := by
    simpa [prefixWord, tailWord_357968, baseEnd_357968] using wordTrace_append hprefix tailTrace_357968
  have hstable : (prefixWord ++ tailWord_357968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357968).length < 2 ^ (prefixWord ++ tailWord_357968).sum := by decide
  have hdescent : baseEnd_357968 < baseStart_357968 := by decide
  rcases family_descends (prefixWord ++ tailWord_357968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357978 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3]
def baseStart_357978 : Nat := 118140960795 + 357978 * 2 ^ 59
def prefixEnd_357978 : Nat := 4983230072969 + 3 ^ 40 * 357978 * 2
def baseEnd_357978 : Nat := 183814777735305643128695

theorem tailTrace_357978 : CollatzResearch.WordTrace tailWord_357978 prefixEnd_357978 183814777735305643128695 := by
  unfold tailWord_357978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3264132574278579655020647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8704353531409545746721725 3264132574278579655020647)
  ·
    refine ⟨4896198861417869482530971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3264132574278579655020647 4896198861417869482530971)
    ·
      refine ⟨7344298292126804223796457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4896198861417869482530971 7344298292126804223796457)
      ·
        refine ⟨5508223719095103167847343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7344298292126804223796457 5508223719095103167847343)
        ·
          refine ⟨8262335578642654751771015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5508223719095103167847343 8262335578642654751771015)
          ·
            refine ⟨12393503367963982127656523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8262335578642654751771015 12393503367963982127656523)
            ·
              refine ⟨18590255051945973191484785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12393503367963982127656523 18590255051945973191484785)
              ·
                refine ⟨13942691288959479893613589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18590255051945973191484785 13942691288959479893613589)
                ·
                  refine ⟨653563654169975620013137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13942691288959479893613589 653563654169975620013137)
                  ·
                    refine ⟨490172740627481715009853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 653563654169975620013137 490172740627481715009853)
                    ·
                      refine ⟨183814777735305643128695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 490172740627481715009853 183814777735305643128695)
                      ·
                        rfl

theorem cell23_357978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_357978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_357978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_357978 prefixEnd_357978 := by exact prefixLift 357978
  have htrace : WordTrace (prefixWord ++ tailWord_357978) baseStart_357978 baseEnd_357978 := by
    simpa [prefixWord, tailWord_357978, baseEnd_357978] using wordTrace_append hprefix tailTrace_357978
  have hstable : (prefixWord ++ tailWord_357978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357978).length < 2 ^ (prefixWord ++ tailWord_357978).sum := by decide
  have hdescent : baseEnd_357978 < baseStart_357978 := by decide
  rcases family_descends (prefixWord ++ tailWord_357978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358001 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_358001 : Nat := 118140960795 + 358001 * 2 ^ 59
def prefixEnd_358001 : Nat := 4983230072969 + 3 ^ 40 * 358001 * 2
def baseEnd_358001 : Nat := 183826587790359053141089

theorem tailTrace_358001 : CollatzResearch.WordTrace tailWord_358001 prefixEnd_358001 183826587790359053141089 := by
  unfold tailWord_358001
  simp only [CollatzResearch.WordTrace]
  refine ⟨13057369176030993548169857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8704912784020662365446571 13057369176030993548169857)
  ·
    refine ⟨9793026882023245161127393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13057369176030993548169857 9793026882023245161127393)
    ·
      refine ⟨7344770161517433870845545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9793026882023245161127393 7344770161517433870845545)
      ·
        refine ⟨5508577621138075403134159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7344770161517433870845545 5508577621138075403134159)
        ·
          refine ⟨8262866431707113104701239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5508577621138075403134159 8262866431707113104701239)
          ·
            refine ⟨12394299647560669657051859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8262866431707113104701239 12394299647560669657051859)
            ·
              refine ⟨18591449471341004485577789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12394299647560669657051859 18591449471341004485577789)
              ·
                refine ⟨6971793551752876682091671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18591449471341004485577789 6971793551752876682091671)
                ·
                  refine ⟨10457690327629315023137507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6971793551752876682091671 10457690327629315023137507)
                  ·
                    refine ⟨15686535491443972534706261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10457690327629315023137507 15686535491443972534706261)
                    ·
                      refine ⟨183826587790359053141089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 15686535491443972534706261 183826587790359053141089)
                      ·
                        rfl

theorem cell23_358001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_358001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358001 prefixEnd_358001 := by exact prefixLift 358001
  have htrace : WordTrace (prefixWord ++ tailWord_358001) baseStart_358001 baseEnd_358001 := by
    simpa [prefixWord, tailWord_358001, baseEnd_358001] using wordTrace_append hprefix tailTrace_358001
  have hstable : (prefixWord ++ tailWord_358001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358001).length < 2 ^ (prefixWord ++ tailWord_358001).sum := by decide
  have hdescent : baseEnd_358001 < baseStart_358001 := by decide
  rcases family_descends (prefixWord ++ tailWord_358001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358002 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_358002 : Nat := 118140960795 + 358002 * 2 ^ 59
def prefixEnd_358002 : Nat := 4983230072969 + 3 ^ 40 * 358002 * 2
def baseEnd_358002 : Nat := 61275700423671183076195

theorem tailTrace_358002 : CollatzResearch.WordTrace tailWord_358002 prefixEnd_358002 61275700423671183076195 := by
  unfold tailWord_358002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3264351412256842679739065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8704937099351580479304173 3264351412256842679739065)
  ·
    refine ⟨2448263559192632009804299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3264351412256842679739065 2448263559192632009804299)
    ·
      refine ⟨3672395338788948014706449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2448263559192632009804299 3672395338788948014706449)
      ·
        refine ⟨2754296504091711011029837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3672395338788948014706449 2754296504091711011029837)
        ·
          refine ⟨1032861189034391629136189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2754296504091711011029837 1032861189034391629136189)
          ·
            refine ⟨387322945887896860926071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1032861189034391629136189 387322945887896860926071)
            ·
              refine ⟨580984418831845291389107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387322945887896860926071 580984418831845291389107)
              ·
                refine ⟨871476628247767937083661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580984418831845291389107 871476628247767937083661)
                ·
                  refine ⟨326803735592912976406373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871476628247767937083661 326803735592912976406373)
                  ·
                    refine ⟨61275700423671183076195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326803735592912976406373 61275700423671183076195)
                    ·
                      rfl

theorem cell23_358002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_358002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358002 prefixEnd_358002 := by exact prefixLift 358002
  have htrace : WordTrace (prefixWord ++ tailWord_358002) baseStart_358002 baseEnd_358002 := by
    simpa [prefixWord, tailWord_358002, baseEnd_358002] using wordTrace_append hprefix tailTrace_358002
  have hstable : (prefixWord ++ tailWord_358002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358002).length < 2 ^ (prefixWord ++ tailWord_358002).sum := by decide
  have hdescent : baseEnd_358002 < baseStart_358002 := by decide
  rcases family_descends (prefixWord ++ tailWord_358002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358025 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 3, 1, 3]
def baseStart_358025 : Nat := 118140960795 + 358025 * 2 ^ 59
def prefixEnd_358025 : Nat := 4983230072969 + 3 ^ 40 * 358025 * 2
def baseEnd_358025 : Nat := 183838911326066959240979

theorem tailTrace_358025 : CollatzResearch.WordTrace tailWord_358025 prefixEnd_358025 183838911326066959240979 := by
  unfold tailWord_358025
  simp only [CollatzResearch.WordTrace]
  refine ⟨13058244527944045647043529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8705496351962697098029019 13058244527944045647043529)
  ·
    refine ⟨9793683395958034235282647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13058244527944045647043529 9793683395958034235282647)
    ·
      refine ⟨14690525093937051352923971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9793683395958034235282647 14690525093937051352923971)
      ·
        refine ⟨22035787640905577029385957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14690525093937051352923971 22035787640905577029385957)
        ·
          refine ⟨4131710182669795693009867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22035787640905577029385957 4131710182669795693009867)
          ·
            refine ⟨6197565274004693539514801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4131710182669795693009867 6197565274004693539514801)
            ·
              refine ⟨4648173955503520154636101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6197565274004693539514801 4648173955503520154636101)
              ·
                refine ⟨871532616656910028994269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4648173955503520154636101 871532616656910028994269)
                ·
                  refine ⟨326824731246341260872851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871532616656910028994269 326824731246341260872851)
                  ·
                    refine ⟨490237096869511891309277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326824731246341260872851 490237096869511891309277)
                    ·
                      refine ⟨183838911326066959240979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 490237096869511891309277 183838911326066959240979)
                      ·
                        rfl

theorem cell23_358025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 1, 3].length) (baseStart_358025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358025 prefixEnd_358025 := by exact prefixLift 358025
  have htrace : WordTrace (prefixWord ++ tailWord_358025) baseStart_358025 baseEnd_358025 := by
    simpa [prefixWord, tailWord_358025, baseEnd_358025] using wordTrace_append hprefix tailTrace_358025
  have hstable : (prefixWord ++ tailWord_358025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358025).length < 2 ^ (prefixWord ++ tailWord_358025).sum := by decide
  have hdescent : baseEnd_358025 < baseStart_358025 := by decide
  rcases family_descends (prefixWord ++ tailWord_358025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358028 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_358028 : Nat := 118140960795 + 358028 * 2 ^ 59
def prefixEnd_358028 : Nat := 4983230072969 + 3 ^ 40 * 358028 * 2
def baseEnd_358028 : Nat := 61280150589343482501155

theorem tailTrace_358028 : CollatzResearch.WordTrace tailWord_358028 prefixEnd_358028 61280150589343482501155 := by
  unfold tailWord_358028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6529176973466588579701369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8705569297955451439601825 6529176973466588579701369)
  ·
    refine ⟨4896882730099941434776027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6529176973466588579701369 4896882730099941434776027)
    ·
      refine ⟨7345324095149912152164041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4896882730099941434776027 7345324095149912152164041)
      ·
        refine ⟨5508993071362434114123031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7345324095149912152164041 5508993071362434114123031)
        ·
          refine ⟨8263489607043651171184547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5508993071362434114123031 8263489607043651171184547)
          ·
            refine ⟨12395234410565476756776821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8263489607043651171184547 12395234410565476756776821)
            ·
              refine ⟨1162053225990513445947827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12395234410565476756776821 1162053225990513445947827)
              ·
                refine ⟨1743079838985770168921741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162053225990513445947827 1743079838985770168921741)
                ·
                  refine ⟨653654939619663813345653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1743079838985770168921741 653654939619663813345653)
                  ·
                    refine ⟨61280150589343482501155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 653654939619663813345653 61280150589343482501155)
                    ·
                      rfl

theorem cell23_358028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_358028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358028 prefixEnd_358028 := by exact prefixLift 358028
  have htrace : WordTrace (prefixWord ++ tailWord_358028) baseStart_358028 baseEnd_358028 := by
    simpa [prefixWord, tailWord_358028, baseEnd_358028] using wordTrace_append hprefix tailTrace_358028
  have hstable : (prefixWord ++ tailWord_358028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358028).length < 2 ^ (prefixWord ++ tailWord_358028).sum := by decide
  have hdescent : baseEnd_358028 < baseStart_358028 := by decide
  rcases family_descends (prefixWord ++ tailWord_358028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358052 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 2, 3, 2]
def baseStart_358052 : Nat := 118140960795 + 358052 * 2 ^ 59
def prefixEnd_358052 : Nat := 4983230072969 + 3 ^ 40 * 358052 * 2
def baseEnd_358052 : Nat := 183852775303738353603355

theorem tailTrace_358052 : CollatzResearch.WordTrace tailWord_358052 prefixEnd_358052 183852775303738353603355 := by
  unfold tailWord_358052
  simp only [CollatzResearch.WordTrace]
  refine ⟨6529614649423114629138205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8706152865897486172184273 6529614649423114629138205)
  ·
    refine ⟨2448605493533667985926827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6529614649423114629138205 2448605493533667985926827)
    ·
      refine ⟨3672908240300501978890241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2448605493533667985926827 3672908240300501978890241)
      ·
        refine ⟨2754681180225376484167681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3672908240300501978890241 2754681180225376484167681)
        ·
          refine ⟨2066010885169032363125761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2754681180225376484167681 2066010885169032363125761)
          ·
            refine ⟨1549508163876774272344321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2066010885169032363125761 1549508163876774272344321)
            ·
              refine ⟨1162131122907580704258241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549508163876774272344321 1162131122907580704258241)
              ·
                refine ⟨871598342180685528193681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162131122907580704258241 871598342180685528193681)
                ·
                  refine ⟨653698756635514146145261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 871598342180685528193681 653698756635514146145261)
                  ·
                    refine ⟨245137033738317804804473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653698756635514146145261 245137033738317804804473)
                    ·
                      refine ⟨183852775303738353603355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 245137033738317804804473 183852775303738353603355)
                      ·
                        rfl

theorem cell23_358052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_358052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358052 prefixEnd_358052 := by exact prefixLift 358052
  have htrace : WordTrace (prefixWord ++ tailWord_358052) baseStart_358052 baseEnd_358052 := by
    simpa [prefixWord, tailWord_358052, baseEnd_358052] using wordTrace_append hprefix tailTrace_358052
  have hstable : (prefixWord ++ tailWord_358052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358052).length < 2 ^ (prefixWord ++ tailWord_358052).sum := by decide
  have hdescent : baseEnd_358052 < baseStart_358052 := by decide
  rcases family_descends (prefixWord ++ tailWord_358052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358086 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_358086 : Nat := 118140960795 + 358086 * 2 ^ 59
def prefixEnd_358086 : Nat := 4983230072969 + 3 ^ 40 * 358086 * 2
def baseEnd_358086 : Nat := 183870233645991220578199

theorem tailTrace_358086 : CollatzResearch.WordTrace tailWord_358086 prefixEnd_358086 183870233645991220578199 := by
  unfold tailWord_358086
  simp only [CollatzResearch.WordTrace]
  refine ⟨408139668147595408281691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8706979587148702043342741 408139668147595408281691)
  ·
    refine ⟨612209502221393112422537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 408139668147595408281691 612209502221393112422537)
    ·
      refine ⟨459157126666044834316903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 612209502221393112422537 459157126666044834316903)
      ·
        refine ⟨688735689999067251475355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459157126666044834316903 688735689999067251475355)
        ·
          refine ⟨1033103534998600877213033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688735689999067251475355 1033103534998600877213033)
          ·
            refine ⟨774827651248950657909775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033103534998600877213033 774827651248950657909775)
            ·
              refine ⟨1162241476873425986864663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774827651248950657909775 1162241476873425986864663)
              ·
                refine ⟨1743362215310138980296995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162241476873425986864663 1743362215310138980296995)
                ·
                  refine ⟨2615043322965208470445493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743362215310138980296995 2615043322965208470445493)
                  ·
                    refine ⟨245160311527988294104265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2615043322965208470445493 245160311527988294104265)
                    ·
                      refine ⟨183870233645991220578199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 245160311527988294104265 183870233645991220578199)
                      ·
                        rfl

theorem cell23_358086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_358086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358086 prefixEnd_358086 := by exact prefixLift 358086
  have htrace : WordTrace (prefixWord ++ tailWord_358086) baseStart_358086 baseEnd_358086 := by
    simpa [prefixWord, tailWord_358086, baseEnd_358086] using wordTrace_append hprefix tailTrace_358086
  have hstable : (prefixWord ++ tailWord_358086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358086).length < 2 ^ (prefixWord ++ tailWord_358086).sum := by decide
  have hdescent : baseEnd_358086 < baseStart_358086 := by decide
  rcases family_descends (prefixWord ++ tailWord_358086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358093 : List Nat := [1, 6, 2, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_358093 : Nat := 118140960795 + 358093 * 2 ^ 59
def prefixEnd_358093 : Nat := 4983230072969 + 3 ^ 40 * 358093 * 2
def baseEnd_358093 : Nat := 183873828010572693190667

theorem tailTrace_358093 : CollatzResearch.WordTrace tailWord_358093 prefixEnd_358093 183873828010572693190667 := by
  unfold tailWord_358093
  simp only [CollatzResearch.WordTrace]
  refine ⟨13060724691697693260518933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8707149794465128840345955 13060724691697693260518933)
  ·
    refine ⟨612221469923329371586825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13060724691697693260518933 612221469923329371586825)
    ·
      refine ⟨459166102442497028690119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 612221469923329371586825 459166102442497028690119)
      ·
        refine ⟨688749153663745543035179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459166102442497028690119 688749153663745543035179)
        ·
          refine ⟨1033123730495618314552769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688749153663745543035179 1033123730495618314552769)
          ·
            refine ⟨774842797871713735914577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033123730495618314552769 774842797871713735914577)
            ·
              refine ⟨581132098403785301935933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 774842797871713735914577 581132098403785301935933)
              ·
                refine ⟨217924536901419488225975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 581132098403785301935933 217924536901419488225975)
                ·
                  refine ⟨326886805352129232338963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217924536901419488225975 326886805352129232338963)
                  ·
                    refine ⟨490330208028193848508445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326886805352129232338963 490330208028193848508445)
                    ·
                      refine ⟨183873828010572693190667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 490330208028193848508445 183873828010572693190667)
                      ·
                        rfl

theorem cell23_358093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_358093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358093 prefixEnd_358093 := by exact prefixLift 358093
  have htrace : WordTrace (prefixWord ++ tailWord_358093) baseStart_358093 baseEnd_358093 := by
    simpa [prefixWord, tailWord_358093, baseEnd_358093] using wordTrace_append hprefix tailTrace_358093
  have hstable : (prefixWord ++ tailWord_358093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358093).length < 2 ^ (prefixWord ++ tailWord_358093).sum := by decide
  have hdescent : baseEnd_358093 < baseStart_358093 := by decide
  rcases family_descends (prefixWord ++ tailWord_358093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358109 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_358109 : Nat := 118140960795 + 358109 * 2 ^ 59
def prefixEnd_358109 : Nat := 4983230072969 + 3 ^ 40 * 358109 * 2
def baseEnd_358109 : Nat := 61294014567014876863531

theorem tailTrace_358109 : CollatzResearch.WordTrace tailWord_358109 prefixEnd_358109 61294014567014876863531 := by
  unfold tailWord_358109
  simp only [CollatzResearch.WordTrace]
  refine ⟨13061308259639727993101381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8707538839759818662067587 13061308259639727993101381)
  ·
    refine ⟨2448995298682448998706509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13061308259639727993101381 2448995298682448998706509)
    ·
      refine ⟨918373237005918374514941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2448995298682448998706509 918373237005918374514941)
      ·
        refine ⟨344389963877219390443103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 918373237005918374514941 344389963877219390443103)
        ·
          refine ⟨516584945815829085664655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344389963877219390443103 516584945815829085664655)
          ·
            refine ⟨774877418723743628496983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516584945815829085664655 774877418723743628496983)
            ·
              refine ⟨1162316128085615442745475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774877418723743628496983 1162316128085615442745475)
              ·
                refine ⟨1743474192128423164118213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162316128085615442745475 1743474192128423164118213)
                ·
                  refine ⟨326901411024079343272165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1743474192128423164118213 326901411024079343272165)
                  ·
                    refine ⟨61294014567014876863531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326901411024079343272165 61294014567014876863531)
                    ·
                      rfl

theorem cell23_358109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_358109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358109 prefixEnd_358109 := by exact prefixLift 358109
  have htrace : WordTrace (prefixWord ++ tailWord_358109) baseStart_358109 baseEnd_358109 := by
    simpa [prefixWord, tailWord_358109, baseEnd_358109] using wordTrace_append hprefix tailTrace_358109
  have hstable : (prefixWord ++ tailWord_358109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358109).length < 2 ^ (prefixWord ++ tailWord_358109).sum := by decide
  have hdescent : baseEnd_358109 < baseStart_358109 := by decide
  rcases family_descends (prefixWord ++ tailWord_358109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358175 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 3]
def baseStart_358175 : Nat := 118140960795 + 358175 * 2 ^ 59
def prefixEnd_358175 : Nat := 4983230072969 + 3 ^ 40 * 358175 * 2
def baseEnd_358175 : Nat := 183915933424241372365289

theorem tailTrace_358175 : CollatzResearch.WordTrace tailWord_358175 prefixEnd_358175 183915933424241372365289 := by
  unfold tailWord_358175
  simp only [CollatzResearch.WordTrace]
  refine ⟨13063715477400621265003979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8709143651600414176669319 13063715477400621265003979)
  ·
    refine ⟨19595573216100931897505969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13063715477400621265003979 19595573216100931897505969)
    ·
      refine ⟨14696679912075698923129477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19595573216100931897505969 14696679912075698923129477)
      ·
        refine ⟨2755627483514193548086777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14696679912075698923129477 2755627483514193548086777)
        ·
          refine ⟨2066720612635645161065083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2755627483514193548086777 2066720612635645161065083)
          ·
            refine ⟨3100080918953467741597625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066720612635645161065083 3100080918953467741597625)
            ·
              refine ⟨2325060689215100806198219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3100080918953467741597625 2325060689215100806198219)
              ·
                refine ⟨3487591033822651209297329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325060689215100806198219 3487591033822651209297329)
                ·
                  refine ⟨2615693275366988406972997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3487591033822651209297329 2615693275366988406972997)
                  ·
                    refine ⟨490442489131310326307437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2615693275366988406972997 490442489131310326307437)
                    ·
                      refine ⟨183915933424241372365289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 490442489131310326307437 183915933424241372365289)
                      ·
                        rfl

theorem cell23_358175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_358175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358175 prefixEnd_358175 := by exact prefixLift 358175
  have htrace : WordTrace (prefixWord ++ tailWord_358175) baseStart_358175 baseEnd_358175 := by
    simpa [prefixWord, tailWord_358175, baseEnd_358175] using wordTrace_append hprefix tailTrace_358175
  have hstable : (prefixWord ++ tailWord_358175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358175).length < 2 ^ (prefixWord ++ tailWord_358175).sum := by decide
  have hdescent : baseEnd_358175 < baseStart_358175 := by decide
  rcases family_descends (prefixWord ++ tailWord_358175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358229 : List Nat := [1, 3, 2, 2, 2, 2, 4, 2, 5]
def baseStart_358229 : Nat := 118140960795 + 358229 * 2 ^ 59
def prefixEnd_358229 : Nat := 4983230072969 + 3 ^ 40 * 358229 * 2
def baseEnd_358229 : Nat := 20438184597731573454449

theorem tailTrace_358229 : CollatzResearch.WordTrace tailWord_358229 prefixEnd_358229 20438184597731573454449 := by
  unfold tailWord_358229
  simp only [CollatzResearch.WordTrace]
  refine ⟨13065685019204988487469741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8710456679469992324979827 13065685019204988487469741)
  ·
    refine ⟨4899631882201870682801153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13065685019204988487469741 4899631882201870682801153)
    ·
      refine ⟨3674723911651403012100865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4899631882201870682801153 3674723911651403012100865)
      ·
        refine ⟨2756042933738552259075649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3674723911651403012100865 2756042933738552259075649)
        ·
          refine ⟨2067032200303914194306737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2756042933738552259075649 2067032200303914194306737)
          ·
            refine ⟨1550274150227935645730053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2067032200303914194306737 1550274150227935645730053)
            ·
              refine ⟨290676403167737933574385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1550274150227935645730053 290676403167737933574385)
              ·
                refine ⟨218007302375803450180789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290676403167737933574385 218007302375803450180789)
                ·
                  refine ⟨20438184597731573454449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218007302375803450180789 20438184597731573454449)
                  ·
                    rfl

theorem cell23_358229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_358229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358229 prefixEnd_358229 := by exact prefixLift 358229
  have htrace : WordTrace (prefixWord ++ tailWord_358229) baseStart_358229 baseEnd_358229 := by
    simpa [prefixWord, tailWord_358229, baseEnd_358229] using wordTrace_append hprefix tailTrace_358229
  have hstable : (prefixWord ++ tailWord_358229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358229).length < 2 ^ (prefixWord ++ tailWord_358229).sum := by decide
  have hdescent : baseEnd_358229 < baseStart_358229 := by decide
  rcases family_descends (prefixWord ++ tailWord_358229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358245 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_358245 : Nat := 118140960795 + 358245 * 2 ^ 59
def prefixEnd_358245 : Nat := 4983230072969 + 3 ^ 40 * 358245 * 2
def baseEnd_358245 : Nat := 183951877070056098489967

theorem tailTrace_358245 : CollatzResearch.WordTrace tailWord_358245 prefixEnd_358245 183951877070056098489967 := by
  unfold tailWord_358245
  simp only [CollatzResearch.WordTrace]
  refine ⟨13066268587147023220052189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8710845724764682146701459 13066268587147023220052189)
  ·
    refine ⟨4899850720180133707519571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13066268587147023220052189 4899850720180133707519571)
    ·
      refine ⟨7349776080270200561279357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4899850720180133707519571 7349776080270200561279357)
      ·
        refine ⟨2756166030101325210479759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7349776080270200561279357 2756166030101325210479759)
        ·
          refine ⟨4134249045151987815719639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2756166030101325210479759 4134249045151987815719639)
          ·
            refine ⟨6201373567727981723579459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4134249045151987815719639 6201373567727981723579459)
            ·
              refine ⟨9302060351591972585369189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6201373567727981723579459 9302060351591972585369189)
              ·
                refine ⟨1744136315923494859756723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9302060351591972585369189 1744136315923494859756723)
                ·
                  refine ⟨2616204473885242289635085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744136315923494859756723 2616204473885242289635085)
                  ·
                    refine ⟨981076677706965858613157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2616204473885242289635085 981076677706965858613157)
                    ·
                      refine ⟨183951877070056098489967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 981076677706965858613157 183951877070056098489967)
                      ·
                        rfl

theorem cell23_358245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_358245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358245 prefixEnd_358245 := by exact prefixLift 358245
  have htrace : WordTrace (prefixWord ++ tailWord_358245) baseStart_358245 baseEnd_358245 := by
    simpa [prefixWord, tailWord_358245, baseEnd_358245] using wordTrace_append hprefix tailTrace_358245
  have hstable : (prefixWord ++ tailWord_358245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358245).length < 2 ^ (prefixWord ++ tailWord_358245).sum := by decide
  have hdescent : baseEnd_358245 < baseStart_358245 := by decide
  rcases family_descends (prefixWord ++ tailWord_358245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358275 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 6]
def baseStart_358275 : Nat := 118140960795 + 358275 * 2 ^ 59
def prefixEnd_358275 : Nat := 4983230072969 + 3 ^ 40 * 358275 * 2
def baseEnd_358275 : Nat := 183967281489690981114829

theorem tailTrace_358275 : CollatzResearch.WordTrace tailWord_358275 prefixEnd_358275 183967281489690981114829 := by
  unfold tailWord_358275
  simp only [CollatzResearch.WordTrace]
  refine ⟨13067362777038338343644279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8711575184692225562429519 13067362777038338343644279)
  ·
    refine ⟨19601044165557507515466419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13067362777038338343644279 19601044165557507515466419)
    ·
      refine ⟨29401566248336261273199629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19601044165557507515466419 29401566248336261273199629)
      ·
        refine ⟨11025587343126097977449861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29401566248336261273199629 11025587343126097977449861)
        ·
          refine ⟨2067297626836143370771849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11025587343126097977449861 2067297626836143370771849)
          ·
            refine ⟨1550473220127107528078887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2067297626836143370771849 1550473220127107528078887)
            ·
              refine ⟨2325709830190661292118331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550473220127107528078887 2325709830190661292118331)
              ·
                refine ⟨3488564745285991938177497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325709830190661292118331 3488564745285991938177497)
                ·
                  refine ⟨2616423558964493953633123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3488564745285991938177497 2616423558964493953633123)
                  ·
                    refine ⟨3924635338446740930449685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2616423558964493953633123 3924635338446740930449685)
                    ·
                      refine ⟨183967281489690981114829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3924635338446740930449685 183967281489690981114829)
                      ·
                        rfl

theorem cell23_358275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_358275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358275 prefixEnd_358275 := by exact prefixLift 358275
  have htrace : WordTrace (prefixWord ++ tailWord_358275) baseStart_358275 baseEnd_358275 := by
    simpa [prefixWord, tailWord_358275, baseEnd_358275] using wordTrace_append hprefix tailTrace_358275
  have hstable : (prefixWord ++ tailWord_358275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358275).length < 2 ^ (prefixWord ++ tailWord_358275).sum := by decide
  have hdescent : baseEnd_358275 < baseStart_358275 := by decide
  rcases family_descends (prefixWord ++ tailWord_358275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358289 : List Nat := [1, 2, 2, 1, 1, 1, 6, 4, 1, 4]
def baseStart_358289 : Nat := 118140960795 + 358289 * 2 ^ 59
def prefixEnd_358289 : Nat := 4983230072969 + 3 ^ 40 * 358289 * 2
def baseEnd_358289 : Nat := 61324823406284642113255

theorem tailTrace_358289 : CollatzResearch.WordTrace tailWord_358289 prefixEnd_358289 61324823406284642113255 := by
  unfold tailWord_358289
  simp only [CollatzResearch.WordTrace]
  refine ⟨13067873398987618734653921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8711915599325079156435947 13067873398987618734653921)
  ·
    refine ⟨9800905049240714050990441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13067873398987618734653921 9800905049240714050990441)
    ·
      refine ⟨7350678786930535538242831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9800905049240714050990441 7350678786930535538242831)
      ·
        refine ⟨11026018180395803307364247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7350678786930535538242831 11026018180395803307364247)
        ·
          refine ⟨16539027270593704961046371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11026018180395803307364247 16539027270593704961046371)
          ·
            refine ⟨24808540905890557441569557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16539027270593704961046371 24808540905890557441569557)
            ·
              refine ⟨1162900354963619880073573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24808540905890557441569557 1162900354963619880073573)
              ·
                refine ⟨218043816555678727513795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1162900354963619880073573 218043816555678727513795)
                ·
                  refine ⟨327065724833518091270693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218043816555678727513795 327065724833518091270693)
                  ·
                    refine ⟨61324823406284642113255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 327065724833518091270693 61324823406284642113255)
                    ·
                      rfl

theorem cell23_358289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_358289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358289 prefixEnd_358289 := by exact prefixLift 358289
  have htrace : WordTrace (prefixWord ++ tailWord_358289) baseStart_358289 baseEnd_358289 := by
    simpa [prefixWord, tailWord_358289, baseEnd_358289] using wordTrace_append hprefix tailTrace_358289
  have hstable : (prefixWord ++ tailWord_358289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358289).length < 2 ^ (prefixWord ++ tailWord_358289).sum := by decide
  have hdescent : baseEnd_358289 < baseStart_358289 := by decide
  rcases family_descends (prefixWord ++ tailWord_358289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358345 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 3, 6]
def baseStart_358345 : Nat := 118140960795 + 358345 * 2 ^ 59
def prefixEnd_358345 : Nat := 4983230072969 + 3 ^ 40 * 358345 * 2
def baseEnd_358345 : Nat := 61334408378501902413169

theorem tailTrace_358345 : CollatzResearch.WordTrace tailWord_358345 prefixEnd_358345 61334408378501902413169 := by
  unfold tailWord_358345
  simp only [CollatzResearch.WordTrace]
  refine ⟨13069915886784740298692489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8713277257856493532461659 13069915886784740298692489)
  ·
    refine ⟨9802436915088555224019367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13069915886784740298692489 9802436915088555224019367)
    ·
      refine ⟨14703655372632832836029051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9802436915088555224019367 14703655372632832836029051)
      ·
        refine ⟨22055483058949249254043577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14703655372632832836029051 22055483058949249254043577)
        ·
          refine ⟨16541612294211936940532683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22055483058949249254043577 16541612294211936940532683)
          ·
            refine ⟨24812418441317905410799025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16541612294211936940532683 24812418441317905410799025)
            ·
              refine ⟨18609313830988429058099269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24812418441317905410799025 18609313830988429058099269)
              ·
                refine ⟨3489246343310330448393613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18609313830988429058099269 3489246343310330448393613)
                ·
                  refine ⟨1308467378741373918147605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3489246343310330448393613 1308467378741373918147605)
                  ·
                    refine ⟨61334408378501902413169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1308467378741373918147605 61334408378501902413169)
                    ·
                      rfl

theorem cell23_358345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_358345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358345 prefixEnd_358345 := by exact prefixLift 358345
  have htrace : WordTrace (prefixWord ++ tailWord_358345) baseStart_358345 baseEnd_358345 := by
    simpa [prefixWord, tailWord_358345, baseEnd_358345] using wordTrace_append hprefix tailTrace_358345
  have hstable : (prefixWord ++ tailWord_358345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358345).length < 2 ^ (prefixWord ++ tailWord_358345).sum := by decide
  have hdescent : baseEnd_358345 < baseStart_358345 := by decide
  rcases family_descends (prefixWord ++ tailWord_358345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358346 : List Nat := [3, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3]
def baseStart_358346 : Nat := 118140960795 + 358346 * 2 ^ 59
def prefixEnd_358346 : Nat := 4983230072969 + 3 ^ 40 * 358346 * 2
def baseEnd_358346 : Nat := 184003738616160203327003

theorem tailTrace_358346 : CollatzResearch.WordTrace tailWord_358346 prefixEnd_358346 184003738616160203327003 := by
  unfold tailWord_358346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3267488089945279367369723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8713301573187411646319261 3267488089945279367369723)
  ·
    refine ⟨4901232134917919051054585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3267488089945279367369723 4901232134917919051054585)
    ·
      refine ⟨3675924101188439288290939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4901232134917919051054585 3675924101188439288290939)
      ·
        refine ⟨5513886151782658932436409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3675924101188439288290939 5513886151782658932436409)
        ·
          refine ⟨4135414613836994199327307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5513886151782658932436409 4135414613836994199327307)
          ·
            refine ⟨6203121920755491298990961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135414613836994199327307 6203121920755491298990961)
            ·
              refine ⟨4652341440566618474243221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6203121920755491298990961 4652341440566618474243221)
              ·
                refine ⟨218078505026560240980151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4652341440566618474243221 218078505026560240980151)
                ·
                  refine ⟨327117757539840361470227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218078505026560240980151 327117757539840361470227)
                  ·
                    refine ⟨490676636309760542205341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 327117757539840361470227 490676636309760542205341)
                    ·
                      refine ⟨184003738616160203327003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 490676636309760542205341 184003738616160203327003)
                      ·
                        rfl

theorem cell23_358346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_358346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358346 prefixEnd_358346 := by exact prefixLift 358346
  have htrace : WordTrace (prefixWord ++ tailWord_358346) baseStart_358346 baseEnd_358346 := by
    simpa [prefixWord, tailWord_358346, baseEnd_358346] using wordTrace_append hprefix tailTrace_358346
  have hstable : (prefixWord ++ tailWord_358346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358346).length < 2 ^ (prefixWord ++ tailWord_358346).sum := by decide
  have hdescent : baseEnd_358346 < baseStart_358346 := by decide
  rcases family_descends (prefixWord ++ tailWord_358346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358369 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_358369 : Nat := 118140960795 + 358369 * 2 ^ 59
def prefixEnd_358369 : Nat := 4983230072969 + 3 ^ 40 * 358369 * 2
def baseEnd_358369 : Nat := 184015548671213613339397

theorem tailTrace_358369 : CollatzResearch.WordTrace tailWord_358369 prefixEnd_358369 184015548671213613339397 := by
  unfold tailWord_358369
  simp only [CollatzResearch.WordTrace]
  refine ⟨13070791238697792397566161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8713860825798528265044107 13070791238697792397566161)
  ·
    refine ⟨9803093429023344298174621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13070791238697792397566161 9803093429023344298174621)
    ·
      refine ⟨3676160035883754111815483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9803093429023344298174621 3676160035883754111815483)
      ·
        refine ⟨5514240053825631167723225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3676160035883754111815483 5514240053825631167723225)
        ·
          refine ⟨4135680040369223375792419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5514240053825631167723225 4135680040369223375792419)
          ·
            refine ⟨6203520060553835063688629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135680040369223375792419 6203520060553835063688629)
            ·
              refine ⟨581580005676922037220809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6203520060553835063688629 581580005676922037220809)
              ·
                refine ⟨436185004257691527915607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581580005676922037220809 436185004257691527915607)
                ·
                  refine ⟨654277506386537291873411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436185004257691527915607 654277506386537291873411)
                  ·
                    refine ⟨981416259579805937810117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 654277506386537291873411 981416259579805937810117)
                    ·
                      refine ⟨184015548671213613339397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 981416259579805937810117 184015548671213613339397)
                      ·
                        rfl

theorem cell23_358369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_358369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358369 prefixEnd_358369 := by exact prefixLift 358369
  have htrace : WordTrace (prefixWord ++ tailWord_358369) baseStart_358369 baseEnd_358369 := by
    simpa [prefixWord, tailWord_358369, baseEnd_358369] using wordTrace_append hprefix tailTrace_358369
  have hstable : (prefixWord ++ tailWord_358369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358369).length < 2 ^ (prefixWord ++ tailWord_358369).sum := by decide
  have hdescent : baseEnd_358369 < baseStart_358369 := by decide
  rcases family_descends (prefixWord ++ tailWord_358369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358472 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_358472 : Nat := 118140960795 + 358472 * 2 ^ 59
def prefixEnd_358472 : Nat := 4983230072969 + 3 ^ 40 * 358472 * 2
def baseEnd_358472 : Nat := 184068437178626710351423

theorem tailTrace_358472 : CollatzResearch.WordTrace tailWord_358472 prefixEnd_358472 184068437178626710351423 := by
  unfold tailWord_358472
  simp only [CollatzResearch.WordTrace]
  refine ⟨6537273978662320494282835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8716365304883093992377113 6537273978662320494282835)
  ·
    refine ⟨9805910967993480741424253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6537273978662320494282835 9805910967993480741424253)
    ·
      refine ⟨3677216612997555278034095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9805910967993480741424253 3677216612997555278034095)
      ·
        refine ⟨5515824919496332917051143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677216612997555278034095 5515824919496332917051143)
        ·
          refine ⟨8273737379244499375576715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5515824919496332917051143 8273737379244499375576715)
          ·
            refine ⟨12410606068866749063365073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8273737379244499375576715 12410606068866749063365073)
            ·
              refine ⟨9307954551650061797523805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12410606068866749063365073 9307954551650061797523805)
              ·
                refine ⟨3490482956868773174071427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9307954551650061797523805 3490482956868773174071427)
                ·
                  refine ⟨5235724435303159761107141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490482956868773174071427 5235724435303159761107141)
                  ·
                    refine ⟨981698331619342455207589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5235724435303159761107141 981698331619342455207589)
                    ·
                      refine ⟨184068437178626710351423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 981698331619342455207589 184068437178626710351423)
                      ·
                        rfl

theorem cell23_358472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_358472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358472 prefixEnd_358472 := by exact prefixLift 358472
  have htrace : WordTrace (prefixWord ++ tailWord_358472) baseStart_358472 baseEnd_358472 := by
    simpa [prefixWord, tailWord_358472, baseEnd_358472] using wordTrace_append hprefix tailTrace_358472
  have hstable : (prefixWord ++ tailWord_358472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358472).length < 2 ^ (prefixWord ++ tailWord_358472).sum := by decide
  have hdescent : baseEnd_358472 < baseStart_358472 := by decide
  rcases family_descends (prefixWord ++ tailWord_358472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358476 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 1, 4, 2]
def baseStart_358476 : Nat := 118140960795 + 358476 * 2 ^ 59
def prefixEnd_358476 : Nat := 4983230072969 + 3 ^ 40 * 358476 * 2
def baseEnd_358476 : Nat := 184070491101244694701405

theorem tailTrace_358476 : CollatzResearch.WordTrace tailWord_358476 prefixEnd_358476 184070491101244694701405 := by
  unfold tailWord_358476
  simp only [CollatzResearch.WordTrace]
  refine ⟨6537346924655074835855641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8716462566206766447807521 6537346924655074835855641)
  ·
    refine ⟨4903010193491306126891731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6537346924655074835855641 4903010193491306126891731)
    ·
      refine ⟨7354515290236959190337597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4903010193491306126891731 7354515290236959190337597)
      ·
        refine ⟨2757943233838859696376599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7354515290236959190337597 2757943233838859696376599)
        ·
          refine ⟨4136914850758289544564899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757943233838859696376599 4136914850758289544564899)
          ·
            refine ⟨6205372276137434316847349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4136914850758289544564899 6205372276137434316847349)
            ·
              refine ⟨581753650887884467204439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6205372276137434316847349 581753650887884467204439)
              ·
                refine ⟨872630476331826700806659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581753650887884467204439 872630476331826700806659)
                ·
                  refine ⟨1308945714497740051209989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872630476331826700806659 1308945714497740051209989)
                  ·
                    refine ⟨245427321468326259601873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1308945714497740051209989 245427321468326259601873)
                    ·
                      refine ⟨184070491101244694701405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 245427321468326259601873 184070491101244694701405)
                      ·
                        rfl

theorem cell23_358476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_358476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358476 prefixEnd_358476 := by exact prefixLift 358476
  have htrace : WordTrace (prefixWord ++ tailWord_358476) baseStart_358476 baseEnd_358476 := by
    simpa [prefixWord, tailWord_358476, baseEnd_358476] using wordTrace_append hprefix tailTrace_358476
  have hstable : (prefixWord ++ tailWord_358476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358476).length < 2 ^ (prefixWord ++ tailWord_358476).sum := by decide
  have hdescent : baseEnd_358476 < baseStart_358476 := by decide
  rcases family_descends (prefixWord ++ tailWord_358476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358546 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_358546 : Nat := 118140960795 + 358546 * 2 ^ 59
def prefixEnd_358546 : Nat := 4983230072969 + 3 ^ 40 * 358546 * 2
def baseEnd_358546 : Nat := 61368811582353140275361

theorem tailTrace_358546 : CollatzResearch.WordTrace tailWord_358546 prefixEnd_358546 61368811582353140275361 := by
  unfold tailWord_358546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269311739764137906689873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8718164639371034417839661 3269311739764137906689873)
  ·
    refine ⟨2451983804823103430017405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3269311739764137906689873 2451983804823103430017405)
    ·
      refine ⟨919493926808663786256527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2451983804823103430017405 919493926808663786256527)
      ·
        refine ⟨1379240890212995679384791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919493926808663786256527 1379240890212995679384791)
        ·
          refine ⟨2068861335319493519077187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379240890212995679384791 2068861335319493519077187)
          ·
            refine ⟨3103292002979240278615781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068861335319493519077187 3103292002979240278615781)
            ·
              refine ⟨581867250558607552240459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3103292002979240278615781 581867250558607552240459)
              ·
                refine ⟨872800875837911328360689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581867250558607552240459 872800875837911328360689)
                ·
                  refine ⟨654600656878433496270517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 872800875837911328360689 654600656878433496270517)
                  ·
                    refine ⟨61368811582353140275361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 654600656878433496270517 61368811582353140275361)
                    ·
                      rfl

theorem cell23_358546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_358546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358546 prefixEnd_358546 := by exact prefixLift 358546
  have htrace : WordTrace (prefixWord ++ tailWord_358546) baseStart_358546 baseEnd_358546 := by
    simpa [prefixWord, tailWord_358546, baseEnd_358546] using wordTrace_append hprefix tailTrace_358546
  have hstable : (prefixWord ++ tailWord_358546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358546).length < 2 ^ (prefixWord ++ tailWord_358546).sum := by decide
  have hdescent : baseEnd_358546 < baseStart_358546 := by decide
  rcases family_descends (prefixWord ++ tailWord_358546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358567 : List Nat := [1, 1, 6, 2, 3, 1, 2, 2, 5]
def baseStart_358567 : Nat := 118140960795 + 358567 * 2 ^ 59
def prefixEnd_358567 : Nat := 4983230072969 + 3 ^ 40 * 358567 * 2
def baseEnd_358567 : Nat := 20457468648978204295943

theorem tailTrace_358567 : CollatzResearch.WordTrace tailWord_358567 prefixEnd_358567 20457468648978204295943 := by
  unfold tailWord_358567
  simp only [CollatzResearch.WordTrace]
  refine ⟨13078012891980472213273955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8718675261320314808849303 13078012891980472213273955)
  ·
    refine ⟨19617019337970708319910933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13078012891980472213273955 19617019337970708319910933)
    ·
      refine ⟨919547781467376952495825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19617019337970708319910933 919547781467376952495825)
      ·
        refine ⟨689660836100532714371869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 919547781467376952495825 689660836100532714371869)
        ·
          refine ⟨258622813537699767889451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 689660836100532714371869 258622813537699767889451)
          ·
            refine ⟨387934220306549651834177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258622813537699767889451 387934220306549651834177)
            ·
              refine ⟨290950665229912238875633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387934220306549651834177 290950665229912238875633)
              ·
                refine ⟨218212998922434179156725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290950665229912238875633 218212998922434179156725)
                ·
                  refine ⟨20457468648978204295943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218212998922434179156725 20457468648978204295943)
                  ·
                    rfl

theorem cell23_358567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 5].length) (baseStart_358567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358567 prefixEnd_358567 := by exact prefixLift 358567
  have htrace : WordTrace (prefixWord ++ tailWord_358567) baseStart_358567 baseEnd_358567 := by
    simpa [prefixWord, tailWord_358567, baseEnd_358567] using wordTrace_append hprefix tailTrace_358567
  have hstable : (prefixWord ++ tailWord_358567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358567).length < 2 ^ (prefixWord ++ tailWord_358567).sum := by decide
  have hdescent : baseEnd_358567 < baseStart_358567 := by decide
  rcases family_descends (prefixWord ++ tailWord_358567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358572 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 12]
def baseStart_358572 : Nat := 118140960795 + 358572 * 2 ^ 59
def prefixEnd_358572 : Nat := 4983230072969 + 3 ^ 40 * 358572 * 2
def baseEnd_358572 : Nat := 20457753916008479900107

theorem tailTrace_358572 : CollatzResearch.WordTrace tailWord_358572 prefixEnd_358572 20457753916008479900107 := by
  unfold tailWord_358572
  simp only [CollatzResearch.WordTrace]
  refine ⟨6539097628481179033602985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8718796837974905378137313 6539097628481179033602985)
  ·
    refine ⟨4904323221360884275202239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6539097628481179033602985 4904323221360884275202239)
    ·
      refine ⟨7356484832041326412803359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4904323221360884275202239 7356484832041326412803359)
      ·
        refine ⟨11034727248061989619205039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7356484832041326412803359 11034727248061989619205039)
        ·
          refine ⟨16552090872092984428807559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11034727248061989619205039 16552090872092984428807559)
          ·
            refine ⟨24828136308139476643211339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16552090872092984428807559 24828136308139476643211339)
            ·
              refine ⟨37242204462209214964817009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24828136308139476643211339 37242204462209214964817009)
              ·
                refine ⟨27931653346656911223612757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37242204462209214964817009 27931653346656911223612757)
                ·
                  refine ⟨20457753916008479900107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 27931653346656911223612757 20457753916008479900107)
                  ·
                    rfl

theorem cell23_358572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_358572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358572 prefixEnd_358572 := by exact prefixLift 358572
  have htrace : WordTrace (prefixWord ++ tailWord_358572) baseStart_358572 baseEnd_358572 := by
    simpa [prefixWord, tailWord_358572, baseEnd_358572] using wordTrace_append hprefix tailTrace_358572
  have hstable : (prefixWord ++ tailWord_358572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358572).length < 2 ^ (prefixWord ++ tailWord_358572).sum := by decide
  have hdescent : baseEnd_358572 < baseStart_358572 := by decide
  rcases family_descends (prefixWord ++ tailWord_358572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358610 : List Nat := [3, 2, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_358610 : Nat := 118140960795 + 358610 * 2 ^ 59
def prefixEnd_358610 : Nat := 4983230072969 + 3 ^ 40 * 358610 * 2
def baseEnd_358610 : Nat := 61379765836315723475263

theorem tailTrace_358610 : CollatzResearch.WordTrace tailWord_358610 prefixEnd_358610 61379765836315723475263 := by
  unfold tailWord_358610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269895307706172639272321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8719720820549793704726189 3269895307706172639272321)
  ·
    refine ⟨2452421480779629479454241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3269895307706172639272321 2452421480779629479454241)
    ·
      refine ⟨1839316110584722109590681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2452421480779629479454241 1839316110584722109590681)
      ·
        refine ⟨1379487082938541582193011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1839316110584722109590681 1379487082938541582193011)
        ·
          refine ⟨2069230624407812373289517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379487082938541582193011 2069230624407812373289517)
          ·
            refine ⟨775961484152929639983569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2069230624407812373289517 775961484152929639983569)
            ·
              refine ⟨581971113114697229987677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775961484152929639983569 581971113114697229987677)
              ·
                refine ⟨218239167418011461245379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 581971113114697229987677 218239167418011461245379)
                ·
                  refine ⟨327358751127017191868069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218239167418011461245379 327358751127017191868069)
                  ·
                    refine ⟨61379765836315723475263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 327358751127017191868069 61379765836315723475263)
                    ·
                      rfl

theorem cell23_358610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_358610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358610 prefixEnd_358610 := by exact prefixLift 358610
  have htrace : WordTrace (prefixWord ++ tailWord_358610) baseStart_358610 baseEnd_358610 := by
    simpa [prefixWord, tailWord_358610, baseEnd_358610] using wordTrace_append hprefix tailTrace_358610
  have hstable : (prefixWord ++ tailWord_358610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358610).length < 2 ^ (prefixWord ++ tailWord_358610).sum := by decide
  have hdescent : baseEnd_358610 < baseStart_358610 := by decide
  rcases family_descends (prefixWord ++ tailWord_358610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358649 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 1, 6]
def baseStart_358649 : Nat := 118140960795 + 358649 * 2 ^ 59
def prefixEnd_358649 : Nat := 4983230072969 + 3 ^ 40 * 358649 * 2
def baseEnd_358649 : Nat := 61386441084824172612703

theorem tailTrace_358649 : CollatzResearch.WordTrace tailWord_358649 prefixEnd_358649 61386441084824172612703 := by
  unfold tailWord_358649
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081003677683400217759001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8720669118455600145172667 13081003677683400217759001)
  ·
    refine ⟨9810752758262550163319251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13081003677683400217759001 9810752758262550163319251)
    ·
      refine ⟨14716129137393825244978877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9810752758262550163319251 14716129137393825244978877)
      ·
        refine ⟨5518548426522684466867079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14716129137393825244978877 5518548426522684466867079)
        ·
          refine ⟨8277822639784026700300619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5518548426522684466867079 8277822639784026700300619)
          ·
            refine ⟨12416733959676040050450929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8277822639784026700300619 12416733959676040050450929)
            ·
              refine ⟨9312550469757030037838197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12416733959676040050450929 9312550469757030037838197)
              ·
                refine ⟨873051606539721566047331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9312550469757030037838197 873051606539721566047331)
                ·
                  refine ⟨1309577409809582349070997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873051606539721566047331 1309577409809582349070997)
                  ·
                    refine ⟨61386441084824172612703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1309577409809582349070997 61386441084824172612703)
                    ·
                      rfl

theorem cell23_358649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_358649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358649 prefixEnd_358649 := by exact prefixLift 358649
  have htrace : WordTrace (prefixWord ++ tailWord_358649) baseStart_358649 baseEnd_358649 := by
    simpa [prefixWord, tailWord_358649, baseEnd_358649] using wordTrace_append hprefix tailTrace_358649
  have hstable : (prefixWord ++ tailWord_358649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358649).length < 2 ^ (prefixWord ++ tailWord_358649).sum := by decide
  have hdescent : baseEnd_358649 < baseStart_358649 := by decide
  rcases family_descends (prefixWord ++ tailWord_358649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358656 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 4]
def baseStart_358656 : Nat := 118140960795 + 358656 * 2 ^ 59
def prefixEnd_358656 : Nat := 4983230072969 + 3 ^ 40 * 358656 * 2
def baseEnd_358656 : Nat := 184162917619053990450577

theorem tailTrace_358656 : CollatzResearch.WordTrace tailWord_358656 prefixEnd_358656 184162917619053990450577 := by
  unfold tailWord_358656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6540629494329020206631911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8720839325772026942175881 6540629494329020206631911)
  ·
    refine ⟨9810944241493530309947867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6540629494329020206631911 9810944241493530309947867)
    ·
      refine ⟨14716416362240295464921801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9810944241493530309947867 14716416362240295464921801)
      ·
        refine ⟨11037312271680221598691351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14716416362240295464921801 11037312271680221598691351)
        ·
          refine ⟨16555968407520332398037027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11037312271680221598691351 16555968407520332398037027)
          ·
            refine ⟨24833952611280498597055541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16555968407520332398037027 24833952611280498597055541)
            ·
              refine ⟨2328183057307546743473957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24833952611280498597055541 2328183057307546743473957)
              ·
                refine ⟨436534323245165014401367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2328183057307546743473957 436534323245165014401367)
                ·
                  refine ⟨654801484867747521602051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436534323245165014401367 654801484867747521602051)
                  ·
                    refine ⟨982202227301621282403077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 654801484867747521602051 982202227301621282403077)
                    ·
                      refine ⟨184162917619053990450577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 982202227301621282403077 184162917619053990450577)
                      ·
                        rfl

theorem cell23_358656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_358656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358656 prefixEnd_358656 := by exact prefixLift 358656
  have htrace : WordTrace (prefixWord ++ tailWord_358656) baseStart_358656 baseEnd_358656 := by
    simpa [prefixWord, tailWord_358656, baseEnd_358656] using wordTrace_append hprefix tailTrace_358656
  have hstable : (prefixWord ++ tailWord_358656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358656).length < 2 ^ (prefixWord ++ tailWord_358656).sum := by decide
  have hdescent : baseEnd_358656 < baseStart_358656 := by decide
  rcases family_descends (prefixWord ++ tailWord_358656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358659 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 5]
def baseStart_358659 : Nat := 118140960795 + 358659 * 2 ^ 59
def prefixEnd_358659 : Nat := 4983230072969 + 3 ^ 40 * 358659 * 2
def baseEnd_358659 : Nat := 184164458061017478713063

theorem tailTrace_358659 : CollatzResearch.WordTrace tailWord_358659 prefixEnd_358659 184164458061017478713063 := by
  unfold tailWord_358659
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081368407647171925623031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8720912271764781283748687 13081368407647171925623031)
  ·
    refine ⟨19622052611470757888434547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13081368407647171925623031 19622052611470757888434547)
    ·
      refine ⟨29433078917206136832651821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19622052611470757888434547 29433078917206136832651821)
      ·
        refine ⟨11037404593952301312244433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29433078917206136832651821 11037404593952301312244433)
        ·
          refine ⟨8278053445464225984183325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11037404593952301312244433 8278053445464225984183325)
          ·
            refine ⟨3104270042049084744068747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8278053445464225984183325 3104270042049084744068747)
            ·
              refine ⟨4656405063073627116103121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104270042049084744068747 4656405063073627116103121)
              ·
                refine ⟨3492303797305220337077341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4656405063073627116103121 3492303797305220337077341)
                ·
                  refine ⟨1309613923989457626404003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3492303797305220337077341 1309613923989457626404003)
                  ·
                    refine ⟨1964420885984186439606005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309613923989457626404003 1964420885984186439606005)
                    ·
                      refine ⟨184164458061017478713063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1964420885984186439606005 184164458061017478713063)
                      ·
                        rfl

theorem cell23_358659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_358659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358659 prefixEnd_358659 := by exact prefixLift 358659
  have htrace : WordTrace (prefixWord ++ tailWord_358659) baseStart_358659 baseEnd_358659 := by
    simpa [prefixWord, tailWord_358659, baseEnd_358659] using wordTrace_append hprefix tailTrace_358659
  have hstable : (prefixWord ++ tailWord_358659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358659).length < 2 ^ (prefixWord ++ tailWord_358659).sum := by decide
  have hdescent : baseEnd_358659 < baseStart_358659 := by decide
  rcases family_descends (prefixWord ++ tailWord_358659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358666 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_358666 : Nat := 118140960795 + 358666 * 2 ^ 59
def prefixEnd_358666 : Nat := 4983230072969 + 3 ^ 40 * 358666 * 2
def baseEnd_358666 : Nat := 61389350808532983775177

theorem tailTrace_358666 : CollatzResearch.WordTrace tailWord_358666 prefixEnd_358666 61389350808532983775177 := by
  unfold tailWord_358666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3270405929655453030281963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8721082479081208080751901 3270405929655453030281963)
  ·
    refine ⟨4905608894483179545422945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3270405929655453030281963 4905608894483179545422945)
    ·
      refine ⟨3679206670862384659067209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4905608894483179545422945 3679206670862384659067209)
      ·
        refine ⟨2759405003146788494300407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3679206670862384659067209 2759405003146788494300407)
        ·
          refine ⟨4139107504720182741450611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759405003146788494300407 4139107504720182741450611)
          ·
            refine ⟨6208661257080274112175917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139107504720182741450611 6208661257080274112175917)
            ·
              refine ⟨2328247971405102792065969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6208661257080274112175917 2328247971405102792065969)
              ·
                refine ⟨1746185978553827094049477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2328247971405102792065969 1746185978553827094049477)
                ·
                  refine ⟨327409870978842580134277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1746185978553827094049477 327409870978842580134277)
                  ·
                    refine ⟨61389350808532983775177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 327409870978842580134277 61389350808532983775177)
                    ·
                      rfl

theorem cell23_358666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_358666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358666 prefixEnd_358666 := by exact prefixLift 358666
  have htrace : WordTrace (prefixWord ++ tailWord_358666) baseStart_358666 baseEnd_358666 := by
    simpa [prefixWord, tailWord_358666, baseEnd_358666] using wordTrace_append hprefix tailTrace_358666
  have hstable : (prefixWord ++ tailWord_358666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358666).length < 2 ^ (prefixWord ++ tailWord_358666).sum := by decide
  have hdescent : baseEnd_358666 < baseStart_358666 := by decide
  rcases family_descends (prefixWord ++ tailWord_358666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358679 : List Nat := [1, 1, 3, 4, 1, 2, 11]
def baseStart_358679 : Nat := 118140960795 + 358679 * 2 ^ 59
def prefixEnd_358679 : Nat := 4983230072969 + 3 ^ 40 * 358679 * 2
def baseEnd_358679 : Nat := 2273762070050708647691

theorem tailTrace_358679 : CollatzResearch.WordTrace tailWord_358679 prefixEnd_358679 2273762070050708647691 := by
  unfold tailWord_358679
  simp only [CollatzResearch.WordTrace]
  refine ⟨13082097867574715341351091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8721398578383143560900727 13082097867574715341351091)
  ·
    refine ⟨19623146801362073012026637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13082097867574715341351091 19623146801362073012026637)
    ·
      refine ⟨7358680050510777379509989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19623146801362073012026637 7358680050510777379509989)
      ·
        refine ⟨1379752509470770758658123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7358680050510777379509989 1379752509470770758658123)
        ·
          refine ⟨2069628764206156137987185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379752509470770758658123 2069628764206156137987185)
          ·
            refine ⟨1552221573154617103490389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2069628764206156137987185 1552221573154617103490389)
            ·
              refine ⟨2273762070050708647691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1552221573154617103490389 2273762070050708647691)
              ·
                rfl

theorem cell23_358679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 11].length) (baseStart_358679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358679 prefixEnd_358679 := by exact prefixLift 358679
  have htrace : WordTrace (prefixWord ++ tailWord_358679) baseStart_358679 baseEnd_358679 := by
    simpa [prefixWord, tailWord_358679, baseEnd_358679] using wordTrace_append hprefix tailTrace_358679
  have hstable : (prefixWord ++ tailWord_358679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358679).length < 2 ^ (prefixWord ++ tailWord_358679).sum := by decide
  have hdescent : baseEnd_358679 < baseStart_358679 := by decide
  rcases family_descends (prefixWord ++ tailWord_358679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358740 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_358740 : Nat := 118140960795 + 358740 * 2 ^ 59
def prefixEnd_358740 : Nat := 4983230072969 + 3 ^ 40 * 358740 * 2
def baseEnd_358740 : Nat := 184206049994031661800191

theorem tailTrace_358740 : CollatzResearch.WordTrace tailWord_358740 prefixEnd_358740 184206049994031661800191 := by
  unfold tailWord_358740
  simp only [CollatzResearch.WordTrace]
  refine ⟨6542161360176861379660837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8722881813569148506214449 6542161360176861379660837)
  ·
    refine ⟨1226655255033161508686407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6542161360176861379660837 1226655255033161508686407)
    ·
      refine ⟨1839982882549742263029611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226655255033161508686407 1839982882549742263029611)
      ·
        refine ⟨2759974323824613394544417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839982882549742263029611 2759974323824613394544417)
        ·
          refine ⟨2069980742868460045908313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2759974323824613394544417 2069980742868460045908313)
          ·
            refine ⟨1552485557151345034431235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2069980742868460045908313 1552485557151345034431235)
            ·
              refine ⟨2328728335727017551646853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552485557151345034431235 2328728335727017551646853)
              ·
                refine ⟨436636562948815790933785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2328728335727017551646853 436636562948815790933785)
                ·
                  refine ⟨327477422211611843200339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436636562948815790933785 327477422211611843200339)
                  ·
                    refine ⟨491216133317417764800509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 327477422211611843200339 491216133317417764800509)
                    ·
                      refine ⟨184206049994031661800191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 491216133317417764800509 184206049994031661800191)
                      ·
                        rfl

theorem cell23_358740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_358740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358740 prefixEnd_358740 := by exact prefixLift 358740
  have htrace : WordTrace (prefixWord ++ tailWord_358740) baseStart_358740 baseEnd_358740 := by
    simpa [prefixWord, tailWord_358740, baseEnd_358740] using wordTrace_append hprefix tailTrace_358740
  have hstable : (prefixWord ++ tailWord_358740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358740).length < 2 ^ (prefixWord ++ tailWord_358740).sum := by decide
  have hdescent : baseEnd_358740 < baseStart_358740 := by decide
  rcases family_descends (prefixWord ++ tailWord_358740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358741 : List Nat := [1, 3, 2, 2, 4, 2, 2, 2, 1, 2, 2]
def baseStart_358741 : Nat := 118140960795 + 358741 * 2 ^ 59
def prefixEnd_358741 : Nat := 4983230072969 + 3 ^ 40 * 358741 * 2
def baseEnd_358741 : Nat := 184206563474686157887687

theorem tailTrace_358741 : CollatzResearch.WordTrace tailWord_358741 prefixEnd_358741 184206563474686157887687 := by
  unfold tailWord_358741
  simp only [CollatzResearch.WordTrace]
  refine ⟨13084359193350099930108077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8722906128900066620072051 13084359193350099930108077)
  ·
    refine ⟨4906634697506287473790529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13084359193350099930108077 4906634697506287473790529)
    ·
      refine ⟨3679976023129715605342897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4906634697506287473790529 3679976023129715605342897)
      ·
        refine ⟨2759982017347286704007173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3679976023129715605342897 2759982017347286704007173)
        ·
          refine ⟨517496628252616257001345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2759982017347286704007173 517496628252616257001345)
          ·
            refine ⟨388122471189462192751009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517496628252616257001345 388122471189462192751009)
            ·
              refine ⟨291091853392096644563257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388122471189462192751009 291091853392096644563257)
              ·
                refine ⟨218318890044072483422443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291091853392096644563257 218318890044072483422443)
                ·
                  refine ⟨327478335066108725133665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218318890044072483422443 327478335066108725133665)
                  ·
                    refine ⟨245608751299581543850249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 327478335066108725133665 245608751299581543850249)
                    ·
                      refine ⟨184206563474686157887687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 245608751299581543850249 184206563474686157887687)
                      ·
                        rfl

theorem cell23_358741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_358741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358741 prefixEnd_358741 := by exact prefixLift 358741
  have htrace : WordTrace (prefixWord ++ tailWord_358741) baseStart_358741 baseEnd_358741 := by
    simpa [prefixWord, tailWord_358741, baseEnd_358741] using wordTrace_append hprefix tailTrace_358741
  have hstable : (prefixWord ++ tailWord_358741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358741).length < 2 ^ (prefixWord ++ tailWord_358741).sum := by decide
  have hdescent : baseEnd_358741 < baseStart_358741 := by decide
  rcases family_descends (prefixWord ++ tailWord_358741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358756 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_358756 : Nat := 118140960795 + 358756 * 2 ^ 59
def prefixEnd_358756 : Nat := 4983230072969 + 3 ^ 40 * 358756 * 2
def baseEnd_358756 : Nat := 61404755228167866400039

theorem tailTrace_358756 : CollatzResearch.WordTrace tailWord_358756 prefixEnd_358756 61404755228167866400039 := by
  unfold tailWord_358756
  simp only [CollatzResearch.WordTrace]
  refine ⟨6542453144147878745952061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8723270858863838327936081 6542453144147878745952061)
  ·
    refine ⟨2453419929055454529732023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6542453144147878745952061 2453419929055454529732023)
    ·
      refine ⟨3680129893583181794598035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2453419929055454529732023 3680129893583181794598035)
      ·
        refine ⟨5520194840374772691897053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3680129893583181794598035 5520194840374772691897053)
        ·
          refine ⟨2070073065140539759461395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5520194840374772691897053 2070073065140539759461395)
          ·
            refine ⟨3105109597710809639192093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070073065140539759461395 3105109597710809639192093)
            ·
              refine ⟨1164416099141553614697035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3105109597710809639192093 1164416099141553614697035)
              ·
                refine ⟨1746624148712330422045553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164416099141553614697035 1746624148712330422045553)
                ·
                  refine ⟨1309968111534247816534165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1746624148712330422045553 1309968111534247816534165)
                  ·
                    refine ⟨61404755228167866400039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1309968111534247816534165 61404755228167866400039)
                    ·
                      rfl

theorem cell23_358756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_358756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358756 prefixEnd_358756 := by exact prefixLift 358756
  have htrace : WordTrace (prefixWord ++ tailWord_358756) baseStart_358756 baseEnd_358756 := by
    simpa [prefixWord, tailWord_358756, baseEnd_358756] using wordTrace_append hprefix tailTrace_358756
  have hstable : (prefixWord ++ tailWord_358756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358756).length < 2 ^ (prefixWord ++ tailWord_358756).sum := by decide
  have hdescent : baseEnd_358756 < baseStart_358756 := by decide
  rcases family_descends (prefixWord ++ tailWord_358756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358814 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_358814 : Nat := 118140960795 + 358814 * 2 ^ 59
def prefixEnd_358814 : Nat := 4983230072969 + 3 ^ 40 * 358814 * 2
def baseEnd_358814 : Nat := 184244047562464372274851

theorem tailTrace_358814 : CollatzResearch.WordTrace tailWord_358814 prefixEnd_358814 184244047562464372274851 := by
  unfold tailWord_358814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635877715260704174689437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8724681148057088931676997 1635877715260704174689437)
  ·
    refine ⟨613454143222764065508539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1635877715260704174689437 613454143222764065508539)
    ·
      refine ⟨920181214834146098262809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613454143222764065508539 920181214834146098262809)
      ·
        refine ⟨690135911125609573697107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 920181214834146098262809 690135911125609573697107)
        ·
          refine ⟨1035203866688414360545661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690135911125609573697107 1035203866688414360545661)
          ·
            refine ⟨388201450008155385204623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1035203866688414360545661 388201450008155385204623)
            ·
              refine ⟨582302175012233077806935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388201450008155385204623 582302175012233077806935)
              ·
                refine ⟨873453262518349616710403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582302175012233077806935 873453262518349616710403)
                ·
                  refine ⟨1310179893777524425065605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873453262518349616710403 1310179893777524425065605)
                  ·
                    refine ⟨245658730083285829699801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1310179893777524425065605 245658730083285829699801)
                    ·
                      refine ⟨184244047562464372274851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 245658730083285829699801 184244047562464372274851)
                      ·
                        rfl

theorem cell23_358814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_358814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358814 prefixEnd_358814 := by exact prefixLift 358814
  have htrace : WordTrace (prefixWord ++ tailWord_358814) baseStart_358814 baseEnd_358814 := by
    simpa [prefixWord, tailWord_358814, baseEnd_358814] using wordTrace_append hprefix tailTrace_358814
  have hstable : (prefixWord ++ tailWord_358814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358814).length < 2 ^ (prefixWord ++ tailWord_358814).sum := by decide
  have hdescent : baseEnd_358814 < baseStart_358814 := by decide
  rcases family_descends (prefixWord ++ tailWord_358814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358816 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 1, 7]
def baseStart_358816 : Nat := 118140960795 + 358816 * 2 ^ 59
def prefixEnd_358816 : Nat := 4983230072969 + 3 ^ 40 * 358816 * 2
def baseEnd_358816 : Nat := 61415024841257788149947

theorem tailTrace_358816 : CollatzResearch.WordTrace tailWord_358816 prefixEnd_358816 61415024841257788149947 := by
  unfold tailWord_358816
  simp only [CollatzResearch.WordTrace]
  refine ⟨6543547334039193869544151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8724729778718925159392201 6543547334039193869544151)
  ·
    refine ⟨9815321001058790804316227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6543547334039193869544151 9815321001058790804316227)
    ·
      refine ⟨14722981501588186206474341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9815321001058790804316227 14722981501588186206474341)
      ·
        refine ⟨2760559031547784913713939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14722981501588186206474341 2760559031547784913713939)
        ·
          refine ⟨4140838547321677370570909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2760559031547784913713939 4140838547321677370570909)
          ·
            refine ⟨1552814455245629013964091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4140838547321677370570909 1552814455245629013964091)
            ·
              refine ⟨2329221682868443520946137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552814455245629013964091 2329221682868443520946137)
              ·
                refine ⟨1746916262151332640709603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329221682868443520946137 1746916262151332640709603)
                ·
                  refine ⟨2620374393226998961064405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746916262151332640709603 2620374393226998961064405)
                  ·
                    refine ⟨61415024841257788149947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2620374393226998961064405 61415024841257788149947)
                    ·
                      rfl

theorem cell23_358816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_358816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358816 prefixEnd_358816 := by exact prefixLift 358816
  have htrace : WordTrace (prefixWord ++ tailWord_358816) baseStart_358816 baseEnd_358816 := by
    simpa [prefixWord, tailWord_358816, baseEnd_358816] using wordTrace_append hprefix tailTrace_358816
  have hstable : (prefixWord ++ tailWord_358816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358816).length < 2 ^ (prefixWord ++ tailWord_358816).sum := by decide
  have hdescent : baseEnd_358816 < baseStart_358816 := by decide
  rcases family_descends (prefixWord ++ tailWord_358816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358837 : List Nat := [1, 3, 3, 2, 3, 2, 1, 3, 5]
def baseStart_358837 : Nat := 118140960795 + 358837 * 2 ^ 59
def prefixEnd_358837 : Nat := 4983230072969 + 3 ^ 40 * 358837 * 2
def baseEnd_358837 : Nat := 20472873068613086920805

theorem tailTrace_358837 : CollatzResearch.WordTrace tailWord_358837 prefixEnd_358837 20472873068613086920805 := by
  unfold tailWord_358837
  simp only [CollatzResearch.WordTrace]
  refine ⟨13087860601002308325602765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8725240400668205550401843 13087860601002308325602765)
  ·
    refine ⟨4907947725375865622101037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13087860601002308325602765 4907947725375865622101037)
    ·
      refine ⟨1840480397015949608287889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4907947725375865622101037 1840480397015949608287889)
      ·
        refine ⟨1380360297761962206215917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1840480397015949608287889 1380360297761962206215917)
        ·
          refine ⟨517635111660735827330969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1380360297761962206215917 517635111660735827330969)
          ·
            refine ⟨388226333745551870498227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517635111660735827330969 388226333745551870498227)
            ·
              refine ⟨582339500618327805747341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388226333745551870498227 582339500618327805747341)
              ·
                refine ⟨218377312731872927155253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 582339500618327805747341 218377312731872927155253)
                ·
                  refine ⟨20472873068613086920805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218377312731872927155253 20472873068613086920805)
                  ·
                    rfl

theorem cell23_358837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_358837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358837 prefixEnd_358837 := by exact prefixLift 358837
  have htrace : WordTrace (prefixWord ++ tailWord_358837) baseStart_358837 baseEnd_358837 := by
    simpa [prefixWord, tailWord_358837, baseEnd_358837] using wordTrace_append hprefix tailTrace_358837
  have hstable : (prefixWord ++ tailWord_358837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358837).length < 2 ^ (prefixWord ++ tailWord_358837).sum := by decide
  have hdescent : baseEnd_358837 < baseStart_358837 := by decide
  rcases family_descends (prefixWord ++ tailWord_358837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358870 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_358870 : Nat := 118140960795 + 358870 * 2 ^ 59
def prefixEnd_358870 : Nat := 4983230072969 + 3 ^ 40 * 358870 * 2
def baseEnd_358870 : Nat := 184272802479116153174593

theorem tailTrace_358870 : CollatzResearch.WordTrace tailWord_358870 prefixEnd_358870 184272802479116153174593 := by
  unfold tailWord_358870
  simp only [CollatzResearch.WordTrace]
  refine ⟨818066513117672185097129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8726042806588503307702709 818066513117672185097129)
  ·
    refine ⟨613549884838254138822847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 818066513117672185097129 613549884838254138822847)
    ·
      refine ⟨920324827257381208234271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613549884838254138822847 920324827257381208234271)
      ·
        refine ⟨1380487240886071812351407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920324827257381208234271 1380487240886071812351407)
        ·
          refine ⟨2070730861329107718527111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380487240886071812351407 2070730861329107718527111)
          ·
            refine ⟨3106096291993661577790667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070730861329107718527111 3106096291993661577790667)
            ·
              refine ⟨4659144437990492366686001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106096291993661577790667 4659144437990492366686001)
              ·
                refine ⟨3494358328492869275014501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4659144437990492366686001 3494358328492869275014501)
                ·
                  refine ⟨655192186592412989065219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3494358328492869275014501 655192186592412989065219)
                  ·
                    refine ⟨982788279888619483597829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 655192186592412989065219 982788279888619483597829)
                    ·
                      refine ⟨184272802479116153174593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 982788279888619483597829 184272802479116153174593)
                      ·
                        rfl

theorem cell23_358870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_358870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358870 prefixEnd_358870 := by exact prefixLift 358870
  have htrace : WordTrace (prefixWord ++ tailWord_358870) baseStart_358870 baseEnd_358870 := by
    simpa [prefixWord, tailWord_358870, baseEnd_358870] using wordTrace_append hprefix tailTrace_358870
  have hstable : (prefixWord ++ tailWord_358870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358870).length < 2 ^ (prefixWord ++ tailWord_358870).sum := by decide
  have hdescent : baseEnd_358870 < baseStart_358870 := by decide
  rcases family_descends (prefixWord ++ tailWord_358870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358873 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 4, 2, 3]
def baseStart_358873 : Nat := 118140960795 + 358873 * 2 ^ 59
def prefixEnd_358873 : Nat := 4983230072969 + 3 ^ 40 * 358873 * 2
def baseEnd_358873 : Nat := 184274342921079641437079

theorem tailTrace_358873 : CollatzResearch.WordTrace tailWord_358873 prefixEnd_358873 184274342921079641437079 := by
  unfold tailWord_358873
  simp only [CollatzResearch.WordTrace]
  refine ⟨13089173628871886473913273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8726115752581257649275515 13089173628871886473913273)
  ·
    refine ⟨9816880221653914855434955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13089173628871886473913273 9816880221653914855434955)
    ·
      refine ⟨14725320332480872283152433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9816880221653914855434955 14725320332480872283152433)
      ·
        refine ⟨11043990249360654212364325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14725320332480872283152433 11043990249360654212364325)
        ·
          refine ⟨2070748171755122664818311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11043990249360654212364325 2070748171755122664818311)
          ·
            refine ⟨3106122257632683997227467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070748171755122664818311 3106122257632683997227467)
            ·
              refine ⟨4659183386449025995841201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106122257632683997227467 4659183386449025995841201)
              ·
                refine ⟨3494387539836769496880901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4659183386449025995841201 3494387539836769496880901)
                ·
                  refine ⟨655197663719394280665169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3494387539836769496880901 655197663719394280665169)
                  ·
                    refine ⟨491398247789545710498877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 655197663719394280665169 491398247789545710498877)
                    ·
                      refine ⟨184274342921079641437079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 491398247789545710498877 184274342921079641437079)
                      ·
                        rfl

theorem cell23_358873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_358873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358873 prefixEnd_358873 := by exact prefixLift 358873
  have htrace : WordTrace (prefixWord ++ tailWord_358873) baseStart_358873 baseEnd_358873 := by
    simpa [prefixWord, tailWord_358873, baseEnd_358873] using wordTrace_append hprefix tailTrace_358873
  have hstable : (prefixWord ++ tailWord_358873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358873).length < 2 ^ (prefixWord ++ tailWord_358873).sum := by decide
  have hdescent : baseEnd_358873 < baseStart_358873 := by decide
  rcases family_descends (prefixWord ++ tailWord_358873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358890 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_358890 : Nat := 118140960795 + 358890 * 2 ^ 59
def prefixEnd_358890 : Nat := 4983230072969 + 3 ^ 40 * 358890 * 2
def baseEnd_358890 : Nat := 184283072092206074924501

theorem tailTrace_358890 : CollatzResearch.WordTrace tailWord_358890 prefixEnd_358890 184283072092206074924501 := by
  unfold tailWord_358890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272448417452574594320531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8726529113206865584854749 3272448417452574594320531)
  ·
    refine ⟨4908672626178861891480797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3272448417452574594320531 4908672626178861891480797)
    ·
      refine ⟨1840752234817073209305299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4908672626178861891480797 1840752234817073209305299)
      ·
        refine ⟨2761128352225609813957949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840752234817073209305299 2761128352225609813957949)
        ·
          refine ⟨1035423132084603680234231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2761128352225609813957949 1035423132084603680234231)
          ·
            refine ⟨1553134698126905520351347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035423132084603680234231 1553134698126905520351347)
            ·
              refine ⟨2329702047190358280527021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553134698126905520351347 2329702047190358280527021)
              ·
                refine ⟨873638267696384355197633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2329702047190358280527021 873638267696384355197633)
                ·
                  refine ⟨655228700772288266398225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 873638267696384355197633 655228700772288266398225)
                  ·
                    refine ⟨491421525579216199798669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 655228700772288266398225 491421525579216199798669)
                    ·
                      refine ⟨184283072092206074924501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 491421525579216199798669 184283072092206074924501)
                      ·
                        rfl

theorem cell23_358890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_358890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358890 prefixEnd_358890 := by exact prefixLift 358890
  have htrace : WordTrace (prefixWord ++ tailWord_358890) baseStart_358890 baseEnd_358890 := by
    simpa [prefixWord, tailWord_358890, baseEnd_358890] using wordTrace_append hprefix tailTrace_358890
  have hstable : (prefixWord ++ tailWord_358890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358890).length < 2 ^ (prefixWord ++ tailWord_358890).sum := by decide
  have hdescent : baseEnd_358890 < baseStart_358890 := by decide
  rcases family_descends (prefixWord ++ tailWord_358890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358920 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_358920 : Nat := 118140960795 + 358920 * 2 ^ 59
def prefixEnd_358920 : Nat := 4983230072969 + 3 ^ 40 * 358920 * 2
def baseEnd_358920 : Nat := 184298476511840957549363

theorem tailTrace_358920 : CollatzResearch.WordTrace tailWord_358920 prefixEnd_358920 184298476511840957549363 := by
  unfold tailWord_358920
  simp only [CollatzResearch.WordTrace]
  refine ⟨6545443929850806750437107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8727258573134409000582809 6545443929850806750437107)
  ·
    refine ⟨9818165894776210125655661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6545443929850806750437107 9818165894776210125655661)
    ·
      refine ⟨3681812210541078797120873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9818165894776210125655661 3681812210541078797120873)
      ·
        refine ⟨2761359157905809097840655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3681812210541078797120873 2761359157905809097840655)
        ·
          refine ⟨4142038736858713646760983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2761359157905809097840655 4142038736858713646760983)
          ·
            refine ⟨6213058105288070470141475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142038736858713646760983 6213058105288070470141475)
            ·
              refine ⟨9319587157932105705212213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6213058105288070470141475 9319587157932105705212213)
              ·
                refine ⟨873711296056134909863645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9319587157932105705212213 873711296056134909863645)
                ·
                  refine ⟨327641736021050591198867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873711296056134909863645 327641736021050591198867)
                  ·
                    refine ⟨491462604031575886798301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 327641736021050591198867 491462604031575886798301)
                    ·
                      refine ⟨184298476511840957549363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 491462604031575886798301 184298476511840957549363)
                      ·
                        rfl

theorem cell23_358920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_358920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358920 prefixEnd_358920 := by exact prefixLift 358920
  have htrace : WordTrace (prefixWord ++ tailWord_358920) baseStart_358920 baseEnd_358920 := by
    simpa [prefixWord, tailWord_358920, baseEnd_358920] using wordTrace_append hprefix tailTrace_358920
  have hstable : (prefixWord ++ tailWord_358920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358920).length < 2 ^ (prefixWord ++ tailWord_358920).sum := by decide
  have hdescent : baseEnd_358920 < baseStart_358920 := by decide
  rcases family_descends (prefixWord ++ tailWord_358920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358923 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 3, 5]
def baseStart_358923 : Nat := 118140960795 + 358923 * 2 ^ 59
def prefixEnd_358923 : Nat := 4983230072969 + 3 ^ 40 * 358923 * 2
def baseEnd_358923 : Nat := 61433338984601481937283

theorem tailTrace_358923 : CollatzResearch.WordTrace tailWord_358923 prefixEnd_358923 61433338984601481937283 := by
  unfold tailWord_358923
  simp only [CollatzResearch.WordTrace]
  refine ⟨13090997278690745013233423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8727331519127163342155615 13090997278690745013233423)
  ·
    refine ⟨19636495918036117519850135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13090997278690745013233423 19636495918036117519850135)
    ·
      refine ⟨29454743877054176279775203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19636495918036117519850135 29454743877054176279775203)
      ·
        refine ⟨44182115815581264419662805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29454743877054176279775203 44182115815581264419662805)
        ·
          refine ⟨1035518339427685884835847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 44182115815581264419662805 1035518339427685884835847)
          ·
            refine ⟨1553277509141528827253771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035518339427685884835847 1553277509141528827253771)
            ·
              refine ⟨2329916263712293240880657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553277509141528827253771 2329916263712293240880657)
              ·
                refine ⟨1747437197784219930660493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329916263712293240880657 1747437197784219930660493)
                ·
                  refine ⟨655288949169082473997685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1747437197784219930660493 655288949169082473997685)
                  ·
                    refine ⟨61433338984601481937283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 655288949169082473997685 61433338984601481937283)
                    ·
                      rfl

theorem cell23_358923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 5].length) (baseStart_358923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358923 prefixEnd_358923 := by exact prefixLift 358923
  have htrace : WordTrace (prefixWord ++ tailWord_358923) baseStart_358923 baseEnd_358923 := by
    simpa [prefixWord, tailWord_358923, baseEnd_358923] using wordTrace_append hprefix tailTrace_358923
  have hstable : (prefixWord ++ tailWord_358923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358923).length < 2 ^ (prefixWord ++ tailWord_358923).sum := by decide
  have hdescent : baseEnd_358923 < baseStart_358923 := by decide
  rcases family_descends (prefixWord ++ tailWord_358923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358947 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 2, 3, 2]
def baseStart_358947 : Nat := 118140960795 + 358947 * 2 ^ 59
def prefixEnd_358947 : Nat := 4983230072969 + 3 ^ 40 * 358947 * 2
def baseEnd_358947 : Nat := 184312340489512351911739

theorem tailTrace_358947 : CollatzResearch.WordTrace tailWord_358947 prefixEnd_358947 184312340489512351911739 := by
  unfold tailWord_358947
  simp only [CollatzResearch.WordTrace]
  refine ⟨13091872630603797112107095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8727915087069198074738063 13091872630603797112107095)
  ·
    refine ⟨19637808945905695668160643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13091872630603797112107095 19637808945905695668160643)
    ·
      refine ⟨29456713418858543502240965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19637808945905695668160643 29456713418858543502240965)
      ·
        refine ⟨5523133766035976906670181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29456713418858543502240965 5523133766035976906670181)
        ·
          refine ⟨1035587581131745670000659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5523133766035976906670181 1035587581131745670000659)
          ·
            refine ⟨1553381371697618505000989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035587581131745670000659 1553381371697618505000989)
            ·
              refine ⟨582518014386606939375371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1553381371697618505000989 582518014386606939375371)
              ·
                refine ⟨873777021579910409063057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582518014386606939375371 873777021579910409063057)
                ·
                  refine ⟨655332766184932806797293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 873777021579910409063057 655332766184932806797293)
                  ·
                    refine ⟨245749787319349802548985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 655332766184932806797293 245749787319349802548985)
                    ·
                      refine ⟨184312340489512351911739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 245749787319349802548985 184312340489512351911739)
                      ·
                        rfl

theorem cell23_358947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_358947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358947 prefixEnd_358947 := by exact prefixLift 358947
  have htrace : WordTrace (prefixWord ++ tailWord_358947) baseStart_358947 baseEnd_358947 := by
    simpa [prefixWord, tailWord_358947, baseEnd_358947] using wordTrace_append hprefix tailTrace_358947
  have hstable : (prefixWord ++ tailWord_358947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358947).length < 2 ^ (prefixWord ++ tailWord_358947).sum := by decide
  have hdescent : baseEnd_358947 < baseStart_358947 := by decide
  rcases family_descends (prefixWord ++ tailWord_358947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358954 : List Nat := [3, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_358954 : Nat := 118140960795 + 358954 * 2 ^ 59
def prefixEnd_358954 : Nat := 4983230072969 + 3 ^ 40 * 358954 * 2
def baseEnd_358954 : Nat := 184315934854093824524207

theorem tailTrace_358954 : CollatzResearch.WordTrace tailWord_358954 prefixEnd_358954 184315934854093824524207 := by
  unfold tailWord_358954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273031985394609326902979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8728085294385624871741277 3273031985394609326902979)
  ·
    refine ⟨4909547978091913990354469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3273031985394609326902979 4909547978091913990354469)
    ·
      refine ⟨920540245892233873191463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4909547978091913990354469 920540245892233873191463)
      ·
        refine ⟨1380810368838350809787195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920540245892233873191463 1380810368838350809787195)
        ·
          refine ⟨2071215553257526214680793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380810368838350809787195 2071215553257526214680793)
          ·
            refine ⟨1553411664943144661010595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2071215553257526214680793 1553411664943144661010595)
            ·
              refine ⟨2330117497414716991515893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553411664943144661010595 2330117497414716991515893)
              ·
                refine ⟨218448515382629717954615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2330117497414716991515893 218448515382629717954615)
                ·
                  refine ⟨327672773073944576931923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218448515382629717954615 327672773073944576931923)
                  ·
                    refine ⟨491509159610916865397885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 327672773073944576931923 491509159610916865397885)
                    ·
                      refine ⟨184315934854093824524207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 491509159610916865397885 184315934854093824524207)
                      ·
                        rfl

theorem cell23_358954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_358954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358954 prefixEnd_358954 := by exact prefixLift 358954
  have htrace : WordTrace (prefixWord ++ tailWord_358954) baseStart_358954 baseEnd_358954 := by
    simpa [prefixWord, tailWord_358954, baseEnd_358954] using wordTrace_append hprefix tailTrace_358954
  have hstable : (prefixWord ++ tailWord_358954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358954).length < 2 ^ (prefixWord ++ tailWord_358954).sum := by decide
  have hdescent : baseEnd_358954 < baseStart_358954 := by decide
  rcases family_descends (prefixWord ++ tailWord_358954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358963 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 5]
def baseStart_358963 : Nat := 118140960795 + 358963 * 2 ^ 59
def prefixEnd_358963 : Nat := 4983230072969 + 3 ^ 40 * 358963 * 2
def baseEnd_358963 : Nat := 184320556179984289311665

theorem tailTrace_358963 : CollatzResearch.WordTrace tailWord_358963 prefixEnd_358963 184320556179984289311665 := by
  unfold tailWord_358963
  simp only [CollatzResearch.WordTrace]
  refine ⟨13092456198545831844689543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8728304132363887896459695 13092456198545831844689543)
  ·
    refine ⟨19638684297818747767034315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13092456198545831844689543 19638684297818747767034315)
    ·
      refine ⟨29458026446728121650551473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19638684297818747767034315 29458026446728121650551473)
      ·
        refine ⟨22093519835046091237913605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29458026446728121650551473 22093519835046091237913605)
        ·
          refine ⟨4142534969071142107108801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22093519835046091237913605 4142534969071142107108801)
          ·
            refine ⟨3106901226803356580331601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4142534969071142107108801 3106901226803356580331601)
            ·
              refine ⟨2330175920102517435248701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3106901226803356580331601 2330175920102517435248701)
              ·
                refine ⟨873815970038444038218263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2330175920102517435248701 873815970038444038218263)
                ·
                  refine ⟨1310723955057666057327395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873815970038444038218263 1310723955057666057327395)
                  ·
                    refine ⟨1966085932586499085991093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1310723955057666057327395 1966085932586499085991093)
                    ·
                      refine ⟨184320556179984289311665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1966085932586499085991093 184320556179984289311665)
                      ·
                        rfl

theorem cell23_358963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_358963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358963 prefixEnd_358963 := by exact prefixLift 358963
  have htrace : WordTrace (prefixWord ++ tailWord_358963) baseStart_358963 baseEnd_358963 := by
    simpa [prefixWord, tailWord_358963, baseEnd_358963] using wordTrace_append hprefix tailTrace_358963
  have hstable : (prefixWord ++ tailWord_358963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358963).length < 2 ^ (prefixWord ++ tailWord_358963).sum := by decide
  have hdescent : baseEnd_358963 < baseStart_358963 := by decide
  rcases family_descends (prefixWord ++ tailWord_358963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358970 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_358970 : Nat := 118140960795 + 358970 * 2 ^ 59
def prefixEnd_358970 : Nat := 4983230072969 + 3 ^ 40 * 358970 * 2
def baseEnd_358970 : Nat := 61441383514855253974711

theorem tailTrace_358970 : CollatzResearch.WordTrace tailWord_358970 prefixEnd_358970 61441383514855253974711 := by
  unfold tailWord_358970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273177877380118010048591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8728474339680314693462909 3273177877380118010048591)
  ·
    refine ⟨4909766816070177015072887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3273177877380118010048591 4909766816070177015072887)
    ·
      refine ⟨7364650224105265522609331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4909766816070177015072887 7364650224105265522609331)
      ·
        refine ⟨11046975336157898283913997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7364650224105265522609331 11046975336157898283913997)
        ·
          refine ⟨4142615751059211856467749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11046975336157898283913997 4142615751059211856467749)
          ·
            refine ⟨776740453323602223087703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4142615751059211856467749 776740453323602223087703)
            ·
              refine ⟨1165110679985403334631555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776740453323602223087703 1165110679985403334631555)
              ·
                refine ⟨1747666019978105001947333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165110679985403334631555 1747666019978105001947333)
                ·
                  refine ⟨327687378745894687865125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747666019978105001947333 327687378745894687865125)
                  ·
                    refine ⟨61441383514855253974711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 327687378745894687865125 61441383514855253974711)
                    ·
                      rfl

theorem cell23_358970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_358970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358970 prefixEnd_358970 := by exact prefixLift 358970
  have htrace : WordTrace (prefixWord ++ tailWord_358970) baseStart_358970 baseEnd_358970 := by
    simpa [prefixWord, tailWord_358970, baseEnd_358970] using wordTrace_append hprefix tailTrace_358970
  have hstable : (prefixWord ++ tailWord_358970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358970).length < 2 ^ (prefixWord ++ tailWord_358970).sum := by decide
  have hdescent : baseEnd_358970 < baseStart_358970 := by decide
  rcases family_descends (prefixWord ++ tailWord_358970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358990 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_358990 : Nat := 118140960795 + 358990 * 2 ^ 59
def prefixEnd_358990 : Nat := 4983230072969 + 3 ^ 40 * 358990 * 2
def baseEnd_358990 : Nat := 184334420157655683674041

theorem tailTrace_358990 : CollatzResearch.WordTrace tailWord_358990 prefixEnd_358990 184334420157655683674041 := by
  unfold tailWord_358990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636680121181001931990303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8728960646298676970614949 1636680121181001931990303)
  ·
    refine ⟨2455020181771502897985455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1636680121181001931990303 2455020181771502897985455)
    ·
      refine ⟨3682530272657254346978183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2455020181771502897985455 3682530272657254346978183)
      ·
        refine ⟨5523795408985881520467275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682530272657254346978183 5523795408985881520467275)
        ·
          refine ⟨8285693113478822280700913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5523795408985881520467275 8285693113478822280700913)
          ·
            refine ⟨6214269835109116710525685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8285693113478822280700913 6214269835109116710525685)
            ·
              refine ⟨582587797041479691611783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6214269835109116710525685 582587797041479691611783)
              ·
                refine ⟨873881695562219537417675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582587797041479691611783 873881695562219537417675)
                ·
                  refine ⟨1310822543343329306126513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873881695562219537417675 1310822543343329306126513)
                  ·
                    refine ⟨983116907507496979594885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1310822543343329306126513 983116907507496979594885)
                    ·
                      refine ⟨184334420157655683674041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 983116907507496979594885 184334420157655683674041)
                      ·
                        rfl

theorem cell23_358990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_358990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_358990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_358990 prefixEnd_358990 := by exact prefixLift 358990
  have htrace : WordTrace (prefixWord ++ tailWord_358990) baseStart_358990 baseEnd_358990 := by
    simpa [prefixWord, tailWord_358990, baseEnd_358990] using wordTrace_append hprefix tailTrace_358990
  have hstable : (prefixWord ++ tailWord_358990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358990).length < 2 ^ (prefixWord ++ tailWord_358990).sum := by decide
  have hdescent : baseEnd_358990 < baseStart_358990 := by decide
  rcases family_descends (prefixWord ++ tailWord_358990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359043 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 2, 6]
def baseStart_359043 : Nat := 118140960795 + 359043 * 2 ^ 59
def prefixEnd_359043 : Nat := 4983230072969 + 3 ^ 40 * 359043 * 2
def baseEnd_359043 : Nat := 61453878210781325437099

theorem tailTrace_359043 : CollatzResearch.WordTrace tailWord_359043 prefixEnd_359043 61453878210781325437099 := by
  unfold tailWord_359043
  simp only [CollatzResearch.WordTrace]
  refine ⟨13095374038256005507601783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8730249358837337005067855 13095374038256005507601783)
  ·
    refine ⟨19643061057384008261402675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13095374038256005507601783 19643061057384008261402675)
    ·
      refine ⟨29464591586076012392104013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19643061057384008261402675 29464591586076012392104013)
      ·
        refine ⟨11049221844778504647039005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29464591586076012392104013 11049221844778504647039005)
        ·
          refine ⟨4143458191791939242639627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11049221844778504647039005 4143458191791939242639627)
          ·
            refine ⟨6215187287687908863959441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143458191791939242639627 6215187287687908863959441)
            ·
              refine ⟨4661390465765931647969581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6215187287687908863959441 4661390465765931647969581)
              ·
                refine ⟨1748021424662224367988593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4661390465765931647969581 1748021424662224367988593)
                ·
                  refine ⟨1311016068496668275991445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748021424662224367988593 1311016068496668275991445)
                  ·
                    refine ⟨61453878210781325437099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1311016068496668275991445 61453878210781325437099)
                    ·
                      rfl

theorem cell23_359043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 6].length) (baseStart_359043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359043 prefixEnd_359043 := by exact prefixLift 359043
  have htrace : WordTrace (prefixWord ++ tailWord_359043) baseStart_359043 baseEnd_359043 := by
    simpa [prefixWord, tailWord_359043, baseEnd_359043] using wordTrace_append hprefix tailTrace_359043
  have hstable : (prefixWord ++ tailWord_359043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359043).length < 2 ^ (prefixWord ++ tailWord_359043).sum := by decide
  have hdescent : baseEnd_359043 < baseStart_359043 := by decide
  rcases family_descends (prefixWord ++ tailWord_359043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359044 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_359044 : Nat := 118140960795 + 359044 * 2 ^ 59
def prefixEnd_359044 : Nat := 4983230072969 + 3 ^ 40 * 359044 * 2
def baseEnd_359044 : Nat := 184362148112998472398793

theorem tailTrace_359044 : CollatzResearch.WordTrace tailWord_359044 prefixEnd_359044 184362148112998472398793 := by
  unfold tailWord_359044
  simp only [CollatzResearch.WordTrace]
  refine ⟨6547705255626191339194093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8730273674168255118925457 6547705255626191339194093)
  ·
    refine ⟨2455389470859821752197785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6547705255626191339194093 2455389470859821752197785)
    ·
      refine ⟨1841542103144866314148339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2455389470859821752197785 1841542103144866314148339)
      ·
        refine ⟨2762313154717299471222509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841542103144866314148339 2762313154717299471222509)
        ·
          refine ⟨1035867433018987301708441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2762313154717299471222509 1035867433018987301708441)
          ·
            refine ⟨776900574764240476281331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035867433018987301708441 776900574764240476281331)
            ·
              refine ⟨1165350862146360714421997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776900574764240476281331 1165350862146360714421997)
              ·
                refine ⟨437006573304885267908249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1165350862146360714421997 437006573304885267908249)
                ·
                  refine ⟨327754929978663950931187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437006573304885267908249 327754929978663950931187)
                  ·
                    refine ⟨491632394967995926396781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 327754929978663950931187 491632394967995926396781)
                    ·
                      refine ⟨184362148112998472398793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 491632394967995926396781 184362148112998472398793)
                      ·
                        rfl

theorem cell23_359044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_359044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359044 prefixEnd_359044 := by exact prefixLift 359044
  have htrace : WordTrace (prefixWord ++ tailWord_359044) baseStart_359044 baseEnd_359044 := by
    simpa [prefixWord, tailWord_359044, baseEnd_359044] using wordTrace_append hprefix tailTrace_359044
  have hstable : (prefixWord ++ tailWord_359044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359044).length < 2 ^ (prefixWord ++ tailWord_359044).sum := by decide
  have hdescent : baseEnd_359044 < baseStart_359044 := by decide
  rcases family_descends (prefixWord ++ tailWord_359044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359094 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_359094 : Nat := 118140960795 + 359094 * 2 ^ 59
def prefixEnd_359094 : Nat := 4983230072969 + 3 ^ 40 * 359094 * 2
def baseEnd_359094 : Nat := 61462607381907758924521

theorem tailTrace_359094 : CollatzResearch.WordTrace tailWord_359094 prefixEnd_359094 61462607381907758924521 := by
  unfold tailWord_359094
  simp only [CollatzResearch.WordTrace]
  refine ⟨818577135066952576106771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8731489440714160811805557 818577135066952576106771)
  ·
    refine ⟨1227865702600428864160157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 818577135066952576106771 1227865702600428864160157)
    ·
      refine ⟨460449638475160824060059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1227865702600428864160157 460449638475160824060059)
      ·
        refine ⟨690674457712741236090089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460449638475160824060059 690674457712741236090089)
        ·
          refine ⟨518005843284555927067567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690674457712741236090089 518005843284555927067567)
          ·
            refine ⟨777008764926833890601351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518005843284555927067567 777008764926833890601351)
            ·
              refine ⟨1165513147390250835902027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777008764926833890601351 1165513147390250835902027)
              ·
                refine ⟨1748269721085376253853041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165513147390250835902027 1748269721085376253853041)
                ·
                  refine ⟨1311202290814032190389781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748269721085376253853041 1311202290814032190389781)
                  ·
                    refine ⟨61462607381907758924521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1311202290814032190389781 61462607381907758924521)
                    ·
                      rfl

theorem cell23_359094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_359094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359094 prefixEnd_359094 := by exact prefixLift 359094
  have htrace : WordTrace (prefixWord ++ tailWord_359094) baseStart_359094 baseEnd_359094 := by
    simpa [prefixWord, tailWord_359094, baseEnd_359094] using wordTrace_append hprefix tailTrace_359094
  have hstable : (prefixWord ++ tailWord_359094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359094).length < 2 ^ (prefixWord ++ tailWord_359094).sum := by decide
  have hdescent : baseEnd_359094 < baseStart_359094 := by decide
  rcases family_descends (prefixWord ++ tailWord_359094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359113 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_359113 : Nat := 118140960795 + 359113 * 2 ^ 59
def prefixEnd_359113 : Nat := 4983230072969 + 3 ^ 40 * 359113 * 2
def baseEnd_359113 : Nat := 184397578278158702435975

theorem tailTrace_359113 : CollatzResearch.WordTrace tailWord_359113 prefixEnd_359113 184397578278158702435975 := by
  unfold tailWord_359113
  simp only [CollatzResearch.WordTrace]
  refine ⟨13097927148002407462649993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8731951432001604975099995 13097927148002407462649993)
  ·
    refine ⟨9823445361001805596987495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13097927148002407462649993 9823445361001805596987495)
    ·
      refine ⟨14735168041502708395481243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9823445361001805596987495 14735168041502708395481243)
      ·
        refine ⟨22102752062254062593221865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14735168041502708395481243 22102752062254062593221865)
        ·
          refine ⟨16577064046690546944916399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22102752062254062593221865 16577064046690546944916399)
          ·
            refine ⟨24865596070035820417374599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16577064046690546944916399 24865596070035820417374599)
            ·
              refine ⟨37298394105053730626061899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24865596070035820417374599 37298394105053730626061899)
              ·
                refine ⟨55947591157580595939092849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37298394105053730626061899 55947591157580595939092849)
                ·
                  refine ⟨41960693368185446954319637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55947591157580595939092849 41960693368185446954319637)
                  ·
                    refine ⟨1966907501633692825983733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41960693368185446954319637 1966907501633692825983733)
                    ·
                      refine ⟨184397578278158702435975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1966907501633692825983733 184397578278158702435975)
                      ·
                        rfl

theorem cell23_359113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_359113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359113 prefixEnd_359113 := by exact prefixLift 359113
  have htrace : WordTrace (prefixWord ++ tailWord_359113) baseStart_359113 baseEnd_359113 := by
    simpa [prefixWord, tailWord_359113, baseEnd_359113] using wordTrace_append hprefix tailTrace_359113
  have hstable : (prefixWord ++ tailWord_359113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359113).length < 2 ^ (prefixWord ++ tailWord_359113).sum := by decide
  have hdescent : baseEnd_359113 < baseStart_359113 := by decide
  rcases family_descends (prefixWord ++ tailWord_359113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359160 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 3, 4, 3]
def baseStart_359160 : Nat := 118140960795 + 359160 * 2 ^ 59
def prefixEnd_359160 : Nat := 4983230072969 + 3 ^ 40 * 359160 * 2
def baseEnd_359160 : Nat := 184421711868920018548259

theorem tailTrace_359160 : CollatzResearch.WordTrace tailWord_359160 prefixEnd_359160 184421711868920018548259 := by
  unfold tailWord_359160
  simp only [CollatzResearch.WordTrace]
  refine ⟨6549820689416067244805467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8733094252554756326407289 6549820689416067244805467)
  ·
    refine ⟨9824731034124100867208201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6549820689416067244805467 9824731034124100867208201)
    ·
      refine ⟨7368548275593075650406151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9824731034124100867208201 7368548275593075650406151)
      ·
        refine ⟨11052822413389613475609227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7368548275593075650406151 11052822413389613475609227)
        ·
          refine ⟨16579233620084420213413841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11052822413389613475609227 16579233620084420213413841)
          ·
            refine ⟨12434425215063315160060381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16579233620084420213413841 12434425215063315160060381)
            ·
              refine ⟨4662909455648743185022643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12434425215063315160060381 4662909455648743185022643)
              ·
                refine ⟨6994364183473114777533965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662909455648743185022643 6994364183473114777533965)
                ·
                  refine ⟨2622886568802418041575237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6994364183473114777533965 2622886568802418041575237)
                  ·
                    refine ⟨491791231650453382795357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2622886568802418041575237 491791231650453382795357)
                    ·
                      refine ⟨184421711868920018548259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 491791231650453382795357 184421711868920018548259)
                      ·
                        rfl

theorem cell23_359160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_359160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359160 prefixEnd_359160 := by exact prefixLift 359160
  have htrace : WordTrace (prefixWord ++ tailWord_359160) baseStart_359160 baseEnd_359160 := by
    simpa [prefixWord, tailWord_359160, baseEnd_359160] using wordTrace_append hprefix tailTrace_359160
  have hstable : (prefixWord ++ tailWord_359160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359160).length < 2 ^ (prefixWord ++ tailWord_359160).sum := by decide
  have hdescent : baseEnd_359160 < baseStart_359160 := by decide
  rcases family_descends (prefixWord ++ tailWord_359160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359201 : List Nat := [1, 2, 3, 2, 1, 2, 5, 2, 1, 4]
def baseStart_359201 : Nat := 118140960795 + 359201 * 2 ^ 59
def prefixEnd_359201 : Nat := 4983230072969 + 3 ^ 40 * 359201 * 2
def baseEnd_359201 : Nat := 61480921525251452711857

theorem tailTrace_359201 : CollatzResearch.WordTrace tailWord_359201 prefixEnd_359201 61480921525251452711857 := by
  unfold tailWord_359201
  simp only [CollatzResearch.WordTrace]
  refine ⟨13101136771683598491853457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8734091181122398994568971 13101136771683598491853457)
  ·
    refine ⟨9825852578762698868890093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13101136771683598491853457 9825852578762698868890093)
    ·
      refine ⟨3684694717036012075833785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9825852578762698868890093 3684694717036012075833785)
      ·
        refine ⟨2763521037777009056875339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3684694717036012075833785 2763521037777009056875339)
        ·
          refine ⟨4145281556665513585313009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763521037777009056875339 4145281556665513585313009)
          ·
            refine ⟨3108961167499135188984757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4145281556665513585313009 3108961167499135188984757)
            ·
              refine ⟨291465109453043923967321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3108961167499135188984757 291465109453043923967321)
              ·
                refine ⟨218598832089782942975491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291465109453043923967321 218598832089782942975491)
                ·
                  refine ⟨327898248134674414463237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218598832089782942975491 327898248134674414463237)
                  ·
                    refine ⟨61480921525251452711857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 327898248134674414463237 61480921525251452711857)
                    ·
                      rfl

theorem cell23_359201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_359201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359201 prefixEnd_359201 := by exact prefixLift 359201
  have htrace : WordTrace (prefixWord ++ tailWord_359201) baseStart_359201 baseEnd_359201 := by
    simpa [prefixWord, tailWord_359201, baseEnd_359201] using wordTrace_append hprefix tailTrace_359201
  have hstable : (prefixWord ++ tailWord_359201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359201).length < 2 ^ (prefixWord ++ tailWord_359201).sum := by decide
  have hdescent : baseEnd_359201 < baseStart_359201 := by decide
  rcases family_descends (prefixWord ++ tailWord_359201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359214 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_359214 : Nat := 118140960795 + 359214 * 2 ^ 59
def prefixEnd_359214 : Nat := 4983230072969 + 3 ^ 40 * 359214 * 2
def baseEnd_359214 : Nat := 20494382202695867474779

theorem tailTrace_359214 : CollatzResearch.WordTrace tailWord_359214 prefixEnd_359214 20494382202695867474779 := by
  unfold tailWord_359214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1637701365079562714009587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8734407280424334474717797 1637701365079562714009587)
  ·
    refine ⟨2456552047619344071014381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1637701365079562714009587 2456552047619344071014381)
    ·
      refine ⟨921207017857254026630393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2456552047619344071014381 921207017857254026630393)
      ·
        refine ⟨690905263392940519972795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 921207017857254026630393 690905263392940519972795)
        ·
          refine ⟨1036357895089410779959193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690905263392940519972795 1036357895089410779959193)
          ·
            refine ⟨777268421317058084969395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1036357895089410779959193 777268421317058084969395)
            ·
              refine ⟨1165902631975587127454093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777268421317058084969395 1165902631975587127454093)
              ·
                refine ⟨437213486990845172795285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1165902631975587127454093 437213486990845172795285)
                ·
                  refine ⟨20494382202695867474779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 437213486990845172795285 20494382202695867474779)
                  ·
                    rfl

theorem cell23_359214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_359214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359214 prefixEnd_359214 := by exact prefixLift 359214
  have htrace : WordTrace (prefixWord ++ tailWord_359214) baseStart_359214 baseEnd_359214 := by
    simpa [prefixWord, tailWord_359214, baseEnd_359214] using wordTrace_append hprefix tailTrace_359214
  have hstable : (prefixWord ++ tailWord_359214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359214).length < 2 ^ (prefixWord ++ tailWord_359214).sum := by decide
  have hdescent : baseEnd_359214 < baseStart_359214 := by decide
  rcases family_descends (prefixWord ++ tailWord_359214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359258 : List Nat := [3, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3]
def baseStart_359258 : Nat := 118140960795 + 359258 * 2 ^ 59
def prefixEnd_359258 : Nat := 4983230072969 + 3 ^ 40 * 359258 * 2
def baseEnd_359258 : Nat := 184472032973060635122809

theorem tailTrace_359258 : CollatzResearch.WordTrace tailWord_359258 prefixEnd_359258 184472032973060635122809 := by
  unfold tailWord_359258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3275803933119274306669607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8735477154984731484452285 3275803933119274306669607)
  ·
    refine ⟨4913705899678911460004411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3275803933119274306669607 4913705899678911460004411)
    ·
      refine ⟨7370558849518367190006617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4913705899678911460004411 7370558849518367190006617)
      ·
        refine ⟨5527919137138775392504963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7370558849518367190006617 5527919137138775392504963)
        ·
          refine ⟨8291878705708163088757445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5527919137138775392504963 8291878705708163088757445)
          ·
            refine ⟨1554727257320280579142021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8291878705708163088757445 1554727257320280579142021)
            ·
              refine ⟨291511360747552608589129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1554727257320280579142021 291511360747552608589129)
              ·
                refine ⟨218633520560664456441847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291511360747552608589129 218633520560664456441847)
                ·
                  refine ⟨327950280840996684662771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218633520560664456441847 327950280840996684662771)
                  ·
                    refine ⟨491925421261495026994157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 327950280840996684662771 491925421261495026994157)
                    ·
                      refine ⟨184472032973060635122809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 491925421261495026994157 184472032973060635122809)
                      ·
                        rfl

theorem cell23_359258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_359258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359258 prefixEnd_359258 := by exact prefixLift 359258
  have htrace : WordTrace (prefixWord ++ tailWord_359258) baseStart_359258 baseEnd_359258 := by
    simpa [prefixWord, tailWord_359258, baseEnd_359258] using wordTrace_append hprefix tailTrace_359258
  have hstable : (prefixWord ++ tailWord_359258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359258).length < 2 ^ (prefixWord ++ tailWord_359258).sum := by decide
  have hdescent : baseEnd_359258 < baseStart_359258 := by decide
  rcases family_descends (prefixWord ++ tailWord_359258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359281 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 3, 2, 2]
def baseStart_359281 : Nat := 118140960795 + 359281 * 2 ^ 59
def prefixEnd_359281 : Nat := 4983230072969 + 3 ^ 40 * 359281 * 2
def baseEnd_359281 : Nat := 184483843028114045135203

theorem tailTrace_359281 : CollatzResearch.WordTrace tailWord_359281 prefixEnd_359281 184483843028114045135203 := by
  unfold tailWord_359281
  simp only [CollatzResearch.WordTrace]
  refine ⟨13104054611393772154765697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8736036407595848103177131 13104054611393772154765697)
  ·
    refine ⟨9828040958545329116074273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13104054611393772154765697 9828040958545329116074273)
    ·
      refine ⟨7371030718908996837055705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9828040958545329116074273 7371030718908996837055705)
      ·
        refine ⟨5528273039181747627791779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7371030718908996837055705 5528273039181747627791779)
        ·
          refine ⟨8292409558772621441687669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5528273039181747627791779 8292409558772621441687669)
          ·
            refine ⟨777413396134933260158219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8292409558772621441687669 777413396134933260158219)
            ·
              refine ⟨1166120094202399890237329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777413396134933260158219 1166120094202399890237329)
              ·
                refine ⟨874590070651799917677997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166120094202399890237329 874590070651799917677997)
                ·
                  refine ⟨327971276494424969129249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874590070651799917677997 327971276494424969129249)
                  ·
                    refine ⟨245978457370818726846937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 327971276494424969129249 245978457370818726846937)
                    ·
                      refine ⟨184483843028114045135203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 245978457370818726846937 184483843028114045135203)
                      ·
                        rfl

theorem cell23_359281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_359281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359281 prefixEnd_359281 := by exact prefixLift 359281
  have htrace : WordTrace (prefixWord ++ tailWord_359281) baseStart_359281 baseEnd_359281 := by
    simpa [prefixWord, tailWord_359281, baseEnd_359281] using wordTrace_append hprefix tailTrace_359281
  have hstable : (prefixWord ++ tailWord_359281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359281).length < 2 ^ (prefixWord ++ tailWord_359281).sum := by decide
  have hdescent : baseEnd_359281 < baseStart_359281 := by decide
  rcases family_descends (prefixWord ++ tailWord_359281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359301 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 1, 2, 3]
def baseStart_359301 : Nat := 118140960795 + 359301 * 2 ^ 59
def prefixEnd_359301 : Nat := 4983230072969 + 3 ^ 40 * 359301 * 2
def baseEnd_359301 : Nat := 184494112641203966885111

theorem tailTrace_359301 : CollatzResearch.WordTrace tailWord_359301 prefixEnd_359301 184494112641203966885111 := by
  unfold tailWord_359301
  simp only [CollatzResearch.WordTrace]
  refine ⟨13104784071321315570493757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8736522714214210380329171 13104784071321315570493757)
  ·
    refine ⟨4914294026745493338935159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13104784071321315570493757 4914294026745493338935159)
    ·
      refine ⟨7371441040118240008402739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4914294026745493338935159 7371441040118240008402739)
      ·
        refine ⟨11057161560177360012604109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7371441040118240008402739 11057161560177360012604109)
        ·
          refine ⟨4146435585066510004726541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11057161560177360012604109 4146435585066510004726541)
          ·
            refine ⟨1554913344399941251772453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4146435585066510004726541 1554913344399941251772453)
            ·
              refine ⟨291546252074988984707335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1554913344399941251772453 291546252074988984707335)
              ·
                refine ⟨437319378112483477061003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291546252074988984707335 437319378112483477061003)
                ·
                  refine ⟨655979067168725215591505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437319378112483477061003 655979067168725215591505)
                  ·
                    refine ⟨491984300376543911693629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 655979067168725215591505 491984300376543911693629)
                    ·
                      refine ⟨184494112641203966885111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 491984300376543911693629 184494112641203966885111)
                      ·
                        rfl

theorem cell23_359301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_359301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359301 prefixEnd_359301 := by exact prefixLift 359301
  have htrace : WordTrace (prefixWord ++ tailWord_359301) baseStart_359301 baseEnd_359301 := by
    simpa [prefixWord, tailWord_359301, baseEnd_359301] using wordTrace_append hprefix tailTrace_359301
  have hstable : (prefixWord ++ tailWord_359301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359301).length < 2 ^ (prefixWord ++ tailWord_359301).sum := by decide
  have hdescent : baseEnd_359301 < baseStart_359301 := by decide
  rcases family_descends (prefixWord ++ tailWord_359301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359318 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_359318 : Nat := 118140960795 + 359318 * 2 ^ 59
def prefixEnd_359318 : Nat := 4983230072969 + 3 ^ 40 * 359318 * 2
def baseEnd_359318 : Nat := 184502841812330400372533

theorem tailTrace_359318 : CollatzResearch.WordTrace tailWord_359318 prefixEnd_359318 184502841812330400372533 := by
  unfold tailWord_359318
  simp only [CollatzResearch.WordTrace]
  refine ⟨819087757016232967116413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8736936074839818315908405 819087757016232967116413)
  ·
    refine ⟨307157908881087362668655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 819087757016232967116413 307157908881087362668655)
    ·
      refine ⟨460736863321631044002983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307157908881087362668655 460736863321631044002983)
      ·
        refine ⟨691105294982446566004475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460736863321631044002983 691105294982446566004475)
        ·
          refine ⟨1036657942473669849006713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691105294982446566004475 1036657942473669849006713)
          ·
            refine ⟨777493456855252386755035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1036657942473669849006713 777493456855252386755035)
            ·
              refine ⟨1166240185282878580132553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777493456855252386755035 1166240185282878580132553)
              ·
                refine ⟨874680138962158935099415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166240185282878580132553 874680138962158935099415)
                ·
                  refine ⟨1312020208443238402649123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874680138962158935099415 1312020208443238402649123)
                  ·
                    refine ⟨1968030312664857603973685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1312020208443238402649123 1968030312664857603973685)
                    ·
                      refine ⟨184502841812330400372533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1968030312664857603973685 184502841812330400372533)
                      ·
                        rfl

theorem cell23_359318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_359318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359318 prefixEnd_359318 := by exact prefixLift 359318
  have htrace : WordTrace (prefixWord ++ tailWord_359318) baseStart_359318 baseEnd_359318 := by
    simpa [prefixWord, tailWord_359318, baseEnd_359318] using wordTrace_append hprefix tailTrace_359318
  have hstable : (prefixWord ++ tailWord_359318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359318).length < 2 ^ (prefixWord ++ tailWord_359318).sum := by decide
  have hdescent : baseEnd_359318 < baseStart_359318 := by decide
  rcases family_descends (prefixWord ++ tailWord_359318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359348 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_359348 : Nat := 118140960795 + 359348 * 2 ^ 59
def prefixEnd_359348 : Nat := 4983230072969 + 3 ^ 40 * 359348 * 2
def baseEnd_359348 : Nat := 184518246231965282997395

theorem tailTrace_359348 : CollatzResearch.WordTrace tailWord_359348 prefixEnd_359348 184518246231965282997395 := by
  unfold tailWord_359348
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553249151075521298727349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8737665534767361731636465 6553249151075521298727349)
  ·
    refine ⟨614367107913330121755689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6553249151075521298727349 614367107913330121755689)
    ·
      refine ⟨460775330934997591316767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 614367107913330121755689 460775330934997591316767)
      ·
        refine ⟨691162996402496386975151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460775330934997591316767 691162996402496386975151)
        ·
          refine ⟨1036744494603744580462727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691162996402496386975151 1036744494603744580462727)
          ·
            refine ⟨1555116741905616870694091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036744494603744580462727 1555116741905616870694091)
            ·
              refine ⟨2332675112858425306041137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555116741905616870694091 2332675112858425306041137)
              ·
                refine ⟨1749506334643818979530853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2332675112858425306041137 1749506334643818979530853)
                ·
                  refine ⟨328032437745716058662035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749506334643818979530853 328032437745716058662035)
                  ·
                    refine ⟨492048656618574087993053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 328032437745716058662035 492048656618574087993053)
                    ·
                      refine ⟨184518246231965282997395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 492048656618574087993053 184518246231965282997395)
                      ·
                        rfl

theorem cell23_359348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_359348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359348 prefixEnd_359348 := by exact prefixLift 359348
  have htrace : WordTrace (prefixWord ++ tailWord_359348) baseStart_359348 baseEnd_359348 := by
    simpa [prefixWord, tailWord_359348, baseEnd_359348] using wordTrace_append hprefix tailTrace_359348
  have hstable : (prefixWord ++ tailWord_359348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359348).length < 2 ^ (prefixWord ++ tailWord_359348).sum := by decide
  have hdescent : baseEnd_359348 < baseStart_359348 := by decide
  rcases family_descends (prefixWord ++ tailWord_359348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359354 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2]
def baseStart_359354 : Nat := 118140960795 + 359354 * 2 ^ 59
def prefixEnd_359354 : Nat := 4983230072969 + 3 ^ 40 * 359354 * 2
def baseEnd_359354 : Nat := 184521327115892259522367

theorem tailTrace_359354 : CollatzResearch.WordTrace tailWord_359354 prefixEnd_359354 184521327115892259522367 := by
  unfold tailWord_359354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276679285032326405543279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8737811426752870414782077 3276679285032326405543279)
  ·
    refine ⟨4915018927548489608314919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3276679285032326405543279 4915018927548489608314919)
    ·
      refine ⟨7372528391322734412472379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4915018927548489608314919 7372528391322734412472379)
      ·
        refine ⟨11058792586984101618708569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7372528391322734412472379 11058792586984101618708569)
        ·
          refine ⟨8294094440238076214031427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11058792586984101618708569 8294094440238076214031427)
          ·
            refine ⟨12441141660357114321047141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8294094440238076214031427 12441141660357114321047141)
            ·
              refine ⟨2332714061316958935196339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12441141660357114321047141 2332714061316958935196339)
              ·
                refine ⟨3499071091975438402794509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332714061316958935196339 3499071091975438402794509)
                ·
                  refine ⟨1312151659490789401047941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3499071091975438402794509 1312151659490789401047941)
                  ·
                    refine ⟨246028436154523012696489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1312151659490789401047941 246028436154523012696489)
                    ·
                      refine ⟨184521327115892259522367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246028436154523012696489 184521327115892259522367)
                      ·
                        rfl

theorem cell23_359354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_359354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359354 prefixEnd_359354 := by exact prefixLift 359354
  have htrace : WordTrace (prefixWord ++ tailWord_359354) baseStart_359354 baseEnd_359354 := by
    simpa [prefixWord, tailWord_359354, baseEnd_359354] using wordTrace_append hprefix tailTrace_359354
  have hstable : (prefixWord ++ tailWord_359354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359354).length < 2 ^ (prefixWord ++ tailWord_359354).sum := by decide
  have hdescent : baseEnd_359354 < baseStart_359354 := by decide
  rcases family_descends (prefixWord ++ tailWord_359354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359366 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_359366 : Nat := 118140960795 + 359366 * 2 ^ 59
def prefixEnd_359366 : Nat := 4983230072969 + 3 ^ 40 * 359366 * 2
def baseEnd_359366 : Nat := 184527488883746212572313

theorem tailTrace_359366 : CollatzResearch.WordTrace tailWord_359366 prefixEnd_359366 184527488883746212572313 := by
  unfold tailWord_359366
  simp only [CollatzResearch.WordTrace]
  refine ⟨409598588002682239737811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8738103210723887781073301 409598588002682239737811)
  ·
    refine ⟨614397882004023359606717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409598588002682239737811 614397882004023359606717)
    ·
      refine ⟨230399205751508759852519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 614397882004023359606717 230399205751508759852519)
      ·
        refine ⟨345598808627263139778779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230399205751508759852519 345598808627263139778779)
        ·
          refine ⟨518398212940894709668169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345598808627263139778779 518398212940894709668169)
          ·
            refine ⟨388798659705671032251127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518398212940894709668169 388798659705671032251127)
            ·
              refine ⟨583197989558506548376691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388798659705671032251127 583197989558506548376691)
              ·
                refine ⟨874796984337759822565037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583197989558506548376691 874796984337759822565037)
                ·
                  refine ⟨328048869126659933461889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874796984337759822565037 328048869126659933461889)
                  ·
                    refine ⟨246036651844994950096417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328048869126659933461889 246036651844994950096417)
                    ·
                      refine ⟨184527488883746212572313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246036651844994950096417 184527488883746212572313)
                      ·
                        rfl

theorem cell23_359366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_359366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359366 prefixEnd_359366 := by exact prefixLift 359366
  have htrace : WordTrace (prefixWord ++ tailWord_359366) baseStart_359366 baseEnd_359366 := by
    simpa [prefixWord, tailWord_359366, baseEnd_359366] using wordTrace_append hprefix tailTrace_359366
  have hstable : (prefixWord ++ tailWord_359366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359366).length < 2 ^ (prefixWord ++ tailWord_359366).sum := by decide
  have hdescent : baseEnd_359366 < baseStart_359366 := by decide
  rcases family_descends (prefixWord ++ tailWord_359366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359367 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_359367 : Nat := 118140960795 + 359367 * 2 ^ 59
def prefixEnd_359367 : Nat := 4983230072969 + 3 ^ 40 * 359367 * 2
def baseEnd_359367 : Nat := 184528002364400708659807

theorem tailTrace_359367 : CollatzResearch.WordTrace tailWord_359367 prefixEnd_359367 184528002364400708659807 := by
  unfold tailWord_359367
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107191289082208842396355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8738127526054805894930903 13107191289082208842396355)
  ·
    refine ⟨19660786933623313263594533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13107191289082208842396355 19660786933623313263594533)
    ·
      refine ⟨3686397550054371236923975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19660786933623313263594533 3686397550054371236923975)
      ·
        refine ⟨5529596325081556855385963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686397550054371236923975 5529596325081556855385963)
        ·
          refine ⟨8294394487622335283078945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529596325081556855385963 8294394487622335283078945)
          ·
            refine ⟨6220795865716751462309209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8294394487622335283078945 6220795865716751462309209)
            ·
              refine ⟨4665596899287563596731907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6220795865716751462309209 4665596899287563596731907)
              ·
                refine ⟨6998395348931345395097861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665596899287563596731907 6998395348931345395097861)
                ·
                  refine ⟨1312199127924627261580849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6998395348931345395097861 1312199127924627261580849)
                  ·
                    refine ⟨984149345943470446185637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1312199127924627261580849 984149345943470446185637)
                    ·
                      refine ⟨184528002364400708659807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 984149345943470446185637 184528002364400708659807)
                      ·
                        rfl

theorem cell23_359367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_359367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359367 prefixEnd_359367 := by exact prefixLift 359367
  have htrace : WordTrace (prefixWord ++ tailWord_359367) baseStart_359367 baseEnd_359367 := by
    simpa [prefixWord, tailWord_359367, baseEnd_359367] using wordTrace_append hprefix tailTrace_359367
  have hstable : (prefixWord ++ tailWord_359367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359367).length < 2 ^ (prefixWord ++ tailWord_359367).sum := by decide
  have hdescent : baseEnd_359367 < baseStart_359367 := by decide
  rcases family_descends (prefixWord ++ tailWord_359367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359371 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 4, 2, 2]
def baseStart_359371 : Nat := 118140960795 + 359371 * 2 ^ 59
def prefixEnd_359371 : Nat := 4983230072969 + 3 ^ 40 * 359371 * 2
def baseEnd_359371 : Nat := 184530056287018693009789

theorem tailTrace_359371 : CollatzResearch.WordTrace tailWord_359371 prefixEnd_359371 184530056287018693009789 := by
  unfold tailWord_359371
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107337181067717525541967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8738224787378478350361311 13107337181067717525541967)
  ·
    refine ⟨19661005771601576288312951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13107337181067717525541967 19661005771601576288312951)
    ·
      refine ⟨29491508657402364432469427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19661005771601576288312951 29491508657402364432469427)
      ·
        refine ⟨44237262986103546648704141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29491508657402364432469427 44237262986103546648704141)
        ·
          refine ⟨16588973619788829993264053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44237262986103546648704141 16588973619788829993264053)
          ·
            refine ⟨1555216276855202811868505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16588973619788829993264053 1555216276855202811868505)
            ·
              refine ⟨1166412207641402108901379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1555216276855202811868505 1166412207641402108901379)
              ·
                refine ⟨1749618311462103163352069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166412207641402108901379 1749618311462103163352069)
                ·
                  refine ⟨328053433399144343128513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749618311462103163352069 328053433399144343128513)
                  ·
                    refine ⟨246040075049358257346385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328053433399144343128513 246040075049358257346385)
                    ·
                      refine ⟨184530056287018693009789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246040075049358257346385 184530056287018693009789)
                      ·
                        rfl

theorem cell23_359371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 2, 2].length) (baseStart_359371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359371 prefixEnd_359371 := by exact prefixLift 359371
  have htrace : WordTrace (prefixWord ++ tailWord_359371) baseStart_359371 baseEnd_359371 := by
    simpa [prefixWord, tailWord_359371, baseEnd_359371] using wordTrace_append hprefix tailTrace_359371
  have hstable : (prefixWord ++ tailWord_359371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359371).length < 2 ^ (prefixWord ++ tailWord_359371).sum := by decide
  have hdescent : baseEnd_359371 < baseStart_359371 := by decide
  rcases family_descends (prefixWord ++ tailWord_359371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359382 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_359382 : Nat := 118140960795 + 359382 * 2 ^ 59
def prefixEnd_359382 : Nat := 4983230072969 + 3 ^ 40 * 359382 * 2
def baseEnd_359382 : Nat := 184535704574218149972239

theorem tailTrace_359382 : CollatzResearch.WordTrace tailWord_359382 prefixEnd_359382 184535704574218149972239 := by
  unfold tailWord_359382
  simp only [CollatzResearch.WordTrace]
  refine ⟨819233649001741650262025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8738492256018577602794933 819233649001741650262025)
  ·
    refine ⟨614425236751306237696519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 819233649001741650262025 614425236751306237696519)
    ·
      refine ⟨921637855126959356544779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614425236751306237696519 921637855126959356544779)
      ·
        refine ⟨1382456782690439034817169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921637855126959356544779 1382456782690439034817169)
        ·
          refine ⟨1036842587017829276112877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1382456782690439034817169 1036842587017829276112877)
          ·
            refine ⟨388815970131685978542329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1036842587017829276112877 388815970131685978542329)
            ·
              refine ⟨291611977598764483906747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388815970131685978542329 291611977598764483906747)
              ·
                refine ⟨437417966398146725860121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291611977598764483906747 437417966398146725860121)
                ·
                  refine ⟨328063474798610044395091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437417966398146725860121 328063474798610044395091)
                  ·
                    refine ⟨492095212197915066592637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 328063474798610044395091 492095212197915066592637)
                    ·
                      refine ⟨184535704574218149972239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 492095212197915066592637 184535704574218149972239)
                      ·
                        rfl

theorem cell23_359382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_359382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359382 prefixEnd_359382 := by exact prefixLift 359382
  have htrace : WordTrace (prefixWord ++ tailWord_359382) baseStart_359382 baseEnd_359382 := by
    simpa [prefixWord, tailWord_359382, baseEnd_359382] using wordTrace_append hprefix tailTrace_359382
  have hstable : (prefixWord ++ tailWord_359382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359382).length < 2 ^ (prefixWord ++ tailWord_359382).sum := by decide
  have hdescent : baseEnd_359382 < baseStart_359382 := by decide
  rcases family_descends (prefixWord ++ tailWord_359382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359417 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_359417 : Nat := 118140960795 + 359417 * 2 ^ 59
def prefixEnd_359417 : Nat := 4983230072969 + 3 ^ 40 * 359417 * 2
def baseEnd_359417 : Nat := 184553676397125513034577

theorem tailTrace_359417 : CollatzResearch.WordTrace tailWord_359417 prefixEnd_359417 184553676397125513034577 := by
  unfold tailWord_359417
  simp only [CollatzResearch.WordTrace]
  refine ⟨13109014938901067381716505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8739343292600711587811003 13109014938901067381716505)
  ·
    refine ⟨9831761204175800536287379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13109014938901067381716505 9831761204175800536287379)
    ·
      refine ⟨14747641806263700804431069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9831761204175800536287379 14747641806263700804431069)
      ·
        refine ⟨5530365677348887801661651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14747641806263700804431069 5530365677348887801661651)
        ·
          refine ⟨8295548516023331702492477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5530365677348887801661651 8295548516023331702492477)
          ·
            refine ⟨3110830693508749388434679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8295548516023331702492477 3110830693508749388434679)
            ·
              refine ⟨4666246040263124082652019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110830693508749388434679 4666246040263124082652019)
              ·
                refine ⟨6999369060394686123978029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4666246040263124082652019 6999369060394686123978029)
                ·
                  refine ⟨2624763397648007296491761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6999369060394686123978029 2624763397648007296491761)
                  ·
                    refine ⟨1968572548236005472368821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2624763397648007296491761 1968572548236005472368821)
                    ·
                      refine ⟨184553676397125513034577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1968572548236005472368821 184553676397125513034577)
                      ·
                        rfl

theorem cell23_359417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_359417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359417 prefixEnd_359417 := by exact prefixLift 359417
  have htrace : WordTrace (prefixWord ++ tailWord_359417) baseStart_359417 baseEnd_359417 := by
    simpa [prefixWord, tailWord_359417, baseEnd_359417] using wordTrace_append hprefix tailTrace_359417
  have hstable : (prefixWord ++ tailWord_359417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359417).length < 2 ^ (prefixWord ++ tailWord_359417).sum := by decide
  have hdescent : baseEnd_359417 < baseStart_359417 := by decide
  rcases family_descends (prefixWord ++ tailWord_359417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359422 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_359422 : Nat := 118140960795 + 359422 * 2 ^ 59
def prefixEnd_359422 : Nat := 4983230072969 + 3 ^ 40 * 359422 * 2
def baseEnd_359422 : Nat := 184556243800397993472055

theorem tailTrace_359422 : CollatzResearch.WordTrace tailWord_359422 prefixEnd_359422 184556243800397993472055 := by
  unfold tailWord_359422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1638649662985369154456065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8739464869255302157099013 1638649662985369154456065)
  ·
    refine ⟨1228987247239026865842049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1638649662985369154456065 1228987247239026865842049)
    ·
      refine ⟨921740435429270149381537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1228987247239026865842049 921740435429270149381537)
      ·
        refine ⟨691305326571952612036153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 921740435429270149381537 691305326571952612036153)
        ·
          refine ⟨518478994928964459027115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691305326571952612036153 518478994928964459027115)
          ·
            refine ⟨777718492393446688540673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518478994928964459027115 777718492393446688540673)
            ·
              refine ⟨583288869295085016405505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777718492393446688540673 583288869295085016405505)
              ·
                refine ⟨437466651971313762304129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583288869295085016405505 437466651971313762304129)
                ·
                  refine ⟨328099988978485321728097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437466651971313762304129 328099988978485321728097)
                  ·
                    refine ⟨246074991733863991296073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328099988978485321728097 246074991733863991296073)
                    ·
                      refine ⟨184556243800397993472055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246074991733863991296073 184556243800397993472055)
                      ·
                        rfl

theorem cell23_359422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_359422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359422 prefixEnd_359422 := by exact prefixLift 359422
  have htrace : WordTrace (prefixWord ++ tailWord_359422) baseStart_359422 baseEnd_359422 := by
    simpa [prefixWord, tailWord_359422, baseEnd_359422] using wordTrace_append hprefix tailTrace_359422
  have hstable : (prefixWord ++ tailWord_359422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359422).length < 2 ^ (prefixWord ++ tailWord_359422).sum := by decide
  have hdescent : baseEnd_359422 < baseStart_359422 := by decide
  rcases family_descends (prefixWord ++ tailWord_359422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359427 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 4]
def baseStart_359427 : Nat := 118140960795 + 359427 * 2 ^ 59
def prefixEnd_359427 : Nat := 4983230072969 + 3 ^ 40 * 359427 * 2
def baseEnd_359427 : Nat := 184558811203670473909531

theorem tailTrace_359427 : CollatzResearch.WordTrace tailWord_359427 prefixEnd_359427 184558811203670473909531 := by
  unfold tailWord_359427
  simp only [CollatzResearch.WordTrace]
  refine ⟨13109379668864839089580535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8739586445909892726387023 13109379668864839089580535)
  ·
    refine ⟨19664069503297258634370803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13109379668864839089580535 19664069503297258634370803)
    ·
      refine ⟨29496104254945887951556205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19664069503297258634370803 29496104254945887951556205)
      ·
        refine ⟨11061039095604707981833577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29496104254945887951556205 11061039095604707981833577)
        ·
          refine ⟨8295779321703530986375183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11061039095604707981833577 8295779321703530986375183)
          ·
            refine ⟨12443668982555296479562775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8295779321703530986375183 12443668982555296479562775)
            ·
              refine ⟨18665503473832944719344163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12443668982555296479562775 18665503473832944719344163)
              ·
                refine ⟨27998255210749417079016245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18665503473832944719344163 27998255210749417079016245)
                ·
                  refine ⟨2624836426007757851157773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27998255210749417079016245 2624836426007757851157773)
                  ·
                    refine ⟨984313659752909194184165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624836426007757851157773 984313659752909194184165)
                    ·
                      refine ⟨184558811203670473909531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 984313659752909194184165 184558811203670473909531)
                      ·
                        rfl

theorem cell23_359427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_359427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359427 prefixEnd_359427 := by exact prefixLift 359427
  have htrace : WordTrace (prefixWord ++ tailWord_359427) baseStart_359427 baseEnd_359427 := by
    simpa [prefixWord, tailWord_359427, baseEnd_359427] using wordTrace_append hprefix tailTrace_359427
  have hstable : (prefixWord ++ tailWord_359427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359427).length < 2 ^ (prefixWord ++ tailWord_359427).sum := by decide
  have hdescent : baseEnd_359427 < baseStart_359427 := by decide
  rcases family_descends (prefixWord ++ tailWord_359427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359434 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_359434 : Nat := 118140960795 + 359434 * 2 ^ 59
def prefixEnd_359434 : Nat := 4983230072969 + 3 ^ 40 * 359434 * 2
def baseEnd_359434 : Nat := 184562405568251946521999

theorem tailTrace_359434 : CollatzResearch.WordTrace tailWord_359434 prefixEnd_359434 184562405568251946521999 := by
  unfold tailWord_359434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277408744959869821271339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8739756653226319523390237 3277408744959869821271339)
  ·
    refine ⟨4916113117439804731907009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3277408744959869821271339 4916113117439804731907009)
    ·
      refine ⟨3687084838079853548930257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4916113117439804731907009 3687084838079853548930257)
      ·
        refine ⟨2765313628559890161697693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3687084838079853548930257 2765313628559890161697693)
        ·
          refine ⟨1036992610709958810636635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2765313628559890161697693 1036992610709958810636635)
          ·
            refine ⟨1555488916064938215954953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036992610709958810636635 1555488916064938215954953)
            ·
              refine ⟨1166616687048703661966215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1555488916064938215954953 1166616687048703661966215)
              ·
                refine ⟨1749925030573055492949323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166616687048703661966215 1749925030573055492949323)
                ·
                  refine ⟨2624887545859583239423985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749925030573055492949323 2624887545859583239423985)
                  ·
                    refine ⟨1968665659394687429567989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2624887545859583239423985 1968665659394687429567989)
                    ·
                      refine ⟨184562405568251946521999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1968665659394687429567989 184562405568251946521999)
                      ·
                        rfl

theorem cell23_359434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_359434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359434 prefixEnd_359434 := by exact prefixLift 359434
  have htrace : WordTrace (prefixWord ++ tailWord_359434) baseStart_359434 baseEnd_359434 := by
    simpa [prefixWord, tailWord_359434, baseEnd_359434] using wordTrace_append hprefix tailTrace_359434
  have hstable : (prefixWord ++ tailWord_359434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359434).length < 2 ^ (prefixWord ++ tailWord_359434).sum := by decide
  have hdescent : baseEnd_359434 < baseStart_359434 := by decide
  rcases family_descends (prefixWord ++ tailWord_359434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359467 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 8]
def baseStart_359467 : Nat := 118140960795 + 359467 * 2 ^ 59
def prefixEnd_359467 : Nat := 4983230072969 + 3 ^ 40 * 359467 * 2
def baseEnd_359467 : Nat := 20508816714427813045483

theorem tailTrace_359467 : CollatzResearch.WordTrace tailWord_359467 prefixEnd_359467 20508816714427813045483 := by
  unfold tailWord_359467
  simp only [CollatzResearch.WordTrace]
  refine ⟨13110838588719925921036655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8740559059146617280691103 13110838588719925921036655)
  ·
    refine ⟨19666257883079888881554983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13110838588719925921036655 19666257883079888881554983)
    ·
      refine ⟨29499386824619833322332475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19666257883079888881554983 29499386824619833322332475)
      ·
        refine ⟨44249080236929749983498713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29499386824619833322332475 44249080236929749983498713)
        ·
          refine ⟨33186810177697312487624035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44249080236929749983498713 33186810177697312487624035)
          ·
            refine ⟨49780215266545968731436053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33186810177697312487624035 49780215266545968731436053)
            ·
              refine ⟨2333447590619342284286065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49780215266545968731436053 2333447590619342284286065)
              ·
                refine ⟨1750085692964506713214549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2333447590619342284286065 1750085692964506713214549)
                ·
                  refine ⟨20508816714427813045483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1750085692964506713214549 20508816714427813045483)
                  ·
                    rfl

theorem cell23_359467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 8].length) (baseStart_359467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359467 prefixEnd_359467 := by exact prefixLift 359467
  have htrace : WordTrace (prefixWord ++ tailWord_359467) baseStart_359467 baseEnd_359467 := by
    simpa [prefixWord, tailWord_359467, baseEnd_359467] using wordTrace_append hprefix tailTrace_359467
  have hstable : (prefixWord ++ tailWord_359467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359467).length < 2 ^ (prefixWord ++ tailWord_359467).sum := by decide
  have hdescent : baseEnd_359467 < baseStart_359467 := by decide
  rcases family_descends (prefixWord ++ tailWord_359467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359478 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_359478 : Nat := 118140960795 + 359478 * 2 ^ 59
def prefixEnd_359478 : Nat := 4983230072969 + 3 ^ 40 * 359478 * 2
def baseEnd_359478 : Nat := 184584998717049774371797

theorem tailTrace_359478 : CollatzResearch.WordTrace tailWord_359478 prefixEnd_359478 184584998717049774371797 := by
  unfold tailWord_359478
  simp only [CollatzResearch.WordTrace]
  refine ⟨819452486980004674980443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8740826527786716533124725 819452486980004674980443)
  ·
    refine ⟨1229178730470007012470665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 819452486980004674980443 1229178730470007012470665)
    ·
      refine ⟨921884047852505259352999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1229178730470007012470665 921884047852505259352999)
      ·
        refine ⟨1382826071778757889029499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921884047852505259352999 1382826071778757889029499)
        ·
          refine ⟨2074239107668136833544249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1382826071778757889029499 2074239107668136833544249)
          ·
            refine ⟨1555679330751102625158187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2074239107668136833544249 1555679330751102625158187)
            ·
              refine ⟨2333518996126653937737281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555679330751102625158187 2333518996126653937737281)
              ·
                refine ⟨1750139247094990453302961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2333518996126653937737281 1750139247094990453302961)
                ·
                  refine ⟨1312604435321242839977221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1750139247094990453302961 1312604435321242839977221)
                  ·
                    refine ⟨246113331622733032495729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1312604435321242839977221 246113331622733032495729)
                    ·
                      refine ⟨184584998717049774371797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246113331622733032495729 184584998717049774371797)
                      ·
                        rfl

theorem cell23_359478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_359478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359478 prefixEnd_359478 := by exact prefixLift 359478
  have htrace : WordTrace (prefixWord ++ tailWord_359478) baseStart_359478 baseEnd_359478 := by
    simpa [prefixWord, tailWord_359478, baseEnd_359478] using wordTrace_append hprefix tailTrace_359478
  have hstable : (prefixWord ++ tailWord_359478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359478).length < 2 ^ (prefixWord ++ tailWord_359478).sum := by decide
  have hdescent : baseEnd_359478 < baseStart_359478 := by decide
  rcases family_descends (prefixWord ++ tailWord_359478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359484 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 8]
def baseStart_359484 : Nat := 118140960795 + 359484 * 2 ^ 59
def prefixEnd_359484 : Nat := 4983230072969 + 3 ^ 40 * 359484 * 2
def baseEnd_359484 : Nat := 20509786622330750099641

theorem tailTrace_359484 : CollatzResearch.WordTrace tailWord_359484 prefixEnd_359484 20509786622330750099641 := by
  unfold tailWord_359484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6555729314829168912202753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8740972419772225216270337 6555729314829168912202753)
  ·
    refine ⟨4916796986121876684152065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6555729314829168912202753 4916796986121876684152065)
    ·
      refine ⟨3687597739591407513114049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4916796986121876684152065 3687597739591407513114049)
      ·
        refine ⟨2765698304693555634835537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3687597739591407513114049 2765698304693555634835537)
        ·
          refine ⟨2074273728520166726126653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765698304693555634835537 2074273728520166726126653)
          ·
            refine ⟨777852648195062522297495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2074273728520166726126653 777852648195062522297495)
            ·
              refine ⟨1166778972292593783446243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777852648195062522297495 1166778972292593783446243)
              ·
                refine ⟨1750168458438890675169365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166778972292593783446243 1750168458438890675169365)
                ·
                  refine ⟨20509786622330750099641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1750168458438890675169365 20509786622330750099641)
                  ·
                    rfl

theorem cell23_359484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_359484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359484 prefixEnd_359484 := by exact prefixLift 359484
  have htrace : WordTrace (prefixWord ++ tailWord_359484) baseStart_359484 baseEnd_359484 := by
    simpa [prefixWord, tailWord_359484, baseEnd_359484] using wordTrace_append hprefix tailTrace_359484
  have hstable : (prefixWord ++ tailWord_359484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359484).length < 2 ^ (prefixWord ++ tailWord_359484).sum := by decide
  have hdescent : baseEnd_359484 < baseStart_359484 := by decide
  rcases family_descends (prefixWord ++ tailWord_359484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359497 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 2, 9]
def baseStart_359497 : Nat := 118140960795 + 359497 * 2 ^ 59
def prefixEnd_359497 : Nat := 4983230072969 + 3 ^ 40 * 359497 * 2
def baseEnd_359497 : Nat := 61531584949828400011403

theorem tailTrace_359497 : CollatzResearch.WordTrace tailWord_359497 prefixEnd_359497 61531584949828400011403 := by
  unfold tailWord_359497
  simp only [CollatzResearch.WordTrace]
  refine ⟨13111932778611241044628745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8741288519074160696419163 13111932778611241044628745)
  ·
    refine ⟨9833949583958430783471559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13111932778611241044628745 9833949583958430783471559)
    ·
      refine ⟨14750924375937646175207339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9833949583958430783471559 14750924375937646175207339)
      ·
        refine ⟨22126386563906469262811009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14750924375937646175207339 22126386563906469262811009)
        ·
          refine ⟨16594789922929851947108257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22126386563906469262811009 16594789922929851947108257)
          ·
            refine ⟨12446092442197388960331193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16594789922929851947108257 12446092442197388960331193)
            ·
              refine ⟨9334569331648041720248395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12446092442197388960331193 9334569331648041720248395)
              ·
                refine ⟨14001853997472062580372593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9334569331648041720248395 14001853997472062580372593)
                ·
                  refine ⟨10501390498104046935279445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14001853997472062580372593 10501390498104046935279445)
                  ·
                    refine ⟨61531584949828400011403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 10501390498104046935279445 61531584949828400011403)
                    ·
                      rfl

theorem cell23_359497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_359497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359497 prefixEnd_359497 := by exact prefixLift 359497
  have htrace : WordTrace (prefixWord ++ tailWord_359497) baseStart_359497 baseEnd_359497 := by
    simpa [prefixWord, tailWord_359497, baseEnd_359497] using wordTrace_append hprefix tailTrace_359497
  have hstable : (prefixWord ++ tailWord_359497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359497).length < 2 ^ (prefixWord ++ tailWord_359497).sum := by decide
  have hdescent : baseEnd_359497 < baseStart_359497 := by decide
  rcases family_descends (prefixWord ++ tailWord_359497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359507 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 7]
def baseStart_359507 : Nat := 118140960795 + 359507 * 2 ^ 59
def prefixEnd_359507 : Nat := 4983230072969 + 3 ^ 40 * 359507 * 2
def baseEnd_359507 : Nat := 184599889656030160909163

theorem tailTrace_359507 : CollatzResearch.WordTrace tailWord_359507 prefixEnd_359507 184599889656030160909163 := by
  unfold tailWord_359507
  simp only [CollatzResearch.WordTrace]
  refine ⟨13112297508575012752492775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8741531672383341834995183 13112297508575012752492775)
  ·
    refine ⟨19668446262862519128739163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13112297508575012752492775 19668446262862519128739163)
    ·
      refine ⟨29502669394293778693108745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19668446262862519128739163 29502669394293778693108745)
      ·
        refine ⟨22127002045720334019831559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29502669394293778693108745 22127002045720334019831559)
        ·
          refine ⟨33190503068580501029747339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22127002045720334019831559 33190503068580501029747339)
          ·
            refine ⟨49785754602870751544621009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33190503068580501029747339 49785754602870751544621009)
            ·
              refine ⟨37339315952153063658465757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49785754602870751544621009 37339315952153063658465757)
              ·
                refine ⟨14002243482057398871924659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37339315952153063658465757 14002243482057398871924659)
                ·
                  refine ⟨21003365223086098307886989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14002243482057398871924659 21003365223086098307886989)
                  ·
                    refine ⟨7876261958657286865457621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21003365223086098307886989 7876261958657286865457621)
                    ·
                      refine ⟨184599889656030160909163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7876261958657286865457621 184599889656030160909163)
                      ·
                        rfl

theorem cell23_359507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_359507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359507 prefixEnd_359507 := by exact prefixLift 359507
  have htrace : WordTrace (prefixWord ++ tailWord_359507) baseStart_359507 baseEnd_359507 := by
    simpa [prefixWord, tailWord_359507, baseEnd_359507] using wordTrace_append hprefix tailTrace_359507
  have hstable : (prefixWord ++ tailWord_359507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359507).length < 2 ^ (prefixWord ++ tailWord_359507).sum := by decide
  have hdescent : baseEnd_359507 < baseStart_359507 := by decide
  rcases family_descends (prefixWord ++ tailWord_359507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359518 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_359518 : Nat := 118140960795 + 359518 * 2 ^ 59
def prefixEnd_359518 : Nat := 4983230072969 + 3 ^ 40 * 359518 * 2
def baseEnd_359518 : Nat := 20511726438136624207957

theorem tailTrace_359518 : CollatzResearch.WordTrace tailWord_359518 prefixEnd_359518 20511726438136624207957 := by
  unfold tailWord_359518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639087338941895203892901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8741799141023441087428805 1639087338941895203892901)
  ·
    refine ⟨307328876051605350729919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1639087338941895203892901 307328876051605350729919)
    ·
      refine ⟨460993314077408026094879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307328876051605350729919 460993314077408026094879)
      ·
        refine ⟨691489971116112039142319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460993314077408026094879 691489971116112039142319)
        ·
          refine ⟨1037234956674168058713479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691489971116112039142319 1037234956674168058713479)
          ·
            refine ⟨1555852435011252088070219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037234956674168058713479 1555852435011252088070219)
            ·
              refine ⟨2333778652516878132105329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555852435011252088070219 2333778652516878132105329)
              ·
                refine ⟨1750333989387658599078997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2333778652516878132105329 1750333989387658599078997)
                ·
                  refine ⟨20511726438136624207957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1750333989387658599078997 20511726438136624207957)
                  ·
                    rfl

theorem cell23_359518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_359518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359518 prefixEnd_359518 := by exact prefixLift 359518
  have htrace : WordTrace (prefixWord ++ tailWord_359518) baseStart_359518 baseEnd_359518 := by
    simpa [prefixWord, tailWord_359518, baseEnd_359518] using wordTrace_append hprefix tailTrace_359518
  have hstable : (prefixWord ++ tailWord_359518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359518).length < 2 ^ (prefixWord ++ tailWord_359518).sum := by decide
  have hdescent : baseEnd_359518 < baseStart_359518 := by decide
  rcases family_descends (prefixWord ++ tailWord_359518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359521 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 1, 5, 2]
def baseStart_359521 : Nat := 118140960795 + 359521 * 2 ^ 59
def prefixEnd_359521 : Nat := 4983230072969 + 3 ^ 40 * 359521 * 2
def baseEnd_359521 : Nat := 184607078385193106134099

theorem tailTrace_359521 : CollatzResearch.WordTrace tailWord_359521 prefixEnd_359521 184607078385193106134099 := by
  unfold tailWord_359521
  simp only [CollatzResearch.WordTrace]
  refine ⟨13112808130524293143502417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8741872087016195429001611 13112808130524293143502417)
  ·
    refine ⟨9834606097893219857626813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13112808130524293143502417 9834606097893219857626813)
    ·
      refine ⟨3687977286709957446610055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9834606097893219857626813 3687977286709957446610055)
      ·
        refine ⟨5531965930064936169915083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3687977286709957446610055 5531965930064936169915083)
        ·
          refine ⟨8297948895097404254872625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5531965930064936169915083 8297948895097404254872625)
          ·
            refine ⟨6223461671323053191154469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8297948895097404254872625 6223461671323053191154469)
            ·
              refine ⟨1166899063373072473341463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6223461671323053191154469 1166899063373072473341463)
              ·
                refine ⟨1750348595059608710012195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166899063373072473341463 1750348595059608710012195)
                ·
                  refine ⟨2625522892589413065018293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750348595059608710012195 2625522892589413065018293)
                  ·
                    refine ⟨246142771180257474845465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2625522892589413065018293 246142771180257474845465)
                    ·
                      refine ⟨184607078385193106134099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246142771180257474845465 184607078385193106134099)
                      ·
                        rfl

theorem cell23_359521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_359521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359521 prefixEnd_359521 := by exact prefixLift 359521
  have htrace : WordTrace (prefixWord ++ tailWord_359521) baseStart_359521 baseEnd_359521 := by
    simpa [prefixWord, tailWord_359521, baseEnd_359521] using wordTrace_append hprefix tailTrace_359521
  have hstable : (prefixWord ++ tailWord_359521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359521).length < 2 ^ (prefixWord ++ tailWord_359521).sum := by decide
  have hdescent : baseEnd_359521 < baseStart_359521 := by decide
  rcases family_descends (prefixWord ++ tailWord_359521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359522 : List Nat := [3, 3, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_359522 : Nat := 118140960795 + 359522 * 2 ^ 59
def prefixEnd_359522 : Nat := 4983230072969 + 3 ^ 40 * 359522 * 2
def baseEnd_359522 : Nat := 61535863955282534073865

theorem tailTrace_359522 : CollatzResearch.WordTrace tailWord_359522 prefixEnd_359522 61535863955282534073865 := by
  unfold tailWord_359522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278211150880167578572205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8741896402347113542859213 3278211150880167578572205)
  ·
    refine ⟨1229329181580062841964577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3278211150880167578572205 1229329181580062841964577)
    ·
      refine ⟨921996886185047131473433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1229329181580062841964577 921996886185047131473433)
      ·
        refine ⟨691497664638785348605075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 921996886185047131473433 691497664638785348605075)
        ·
          refine ⟨1037246496958178022907613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691497664638785348605075 1037246496958178022907613)
          ·
            refine ⟨388967436359316758590355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1037246496958178022907613 388967436359316758590355)
            ·
              refine ⟨583451154538975137885533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388967436359316758590355 583451154538975137885533)
              ·
                refine ⟨218794182952115676707075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 583451154538975137885533 218794182952115676707075)
                ·
                  refine ⟨328191274428173515060613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218794182952115676707075 328191274428173515060613)
                  ·
                    refine ⟨61535863955282534073865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 328191274428173515060613 61535863955282534073865)
                    ·
                      rfl

theorem cell23_359522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_359522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359522 prefixEnd_359522 := by exact prefixLift 359522
  have htrace : WordTrace (prefixWord ++ tailWord_359522) baseStart_359522 baseEnd_359522 := by
    simpa [prefixWord, tailWord_359522, baseEnd_359522] using wordTrace_append hprefix tailTrace_359522
  have hstable : (prefixWord ++ tailWord_359522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359522).length < 2 ^ (prefixWord ++ tailWord_359522).sum := by decide
  have hdescent : baseEnd_359522 < baseStart_359522 := by decide
  rcases family_descends (prefixWord ++ tailWord_359522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359538 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 2, 3, 2]
def baseStart_359538 : Nat := 118140960795 + 359538 * 2 ^ 59
def prefixEnd_359538 : Nat := 4983230072969 + 3 ^ 40 * 359538 * 2
def baseEnd_359538 : Nat := 184615807556319539621521

theorem tailTrace_359538 : CollatzResearch.WordTrace tailWord_359538 prefixEnd_359538 184615807556319539621521 := by
  unfold tailWord_359538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278357042865676261717817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8742285447641803364580845 3278357042865676261717817)
  ·
    refine ⟨2458767782149257196288363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3278357042865676261717817 2458767782149257196288363)
    ·
      refine ⟨3688151673223885794432545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2458767782149257196288363 3688151673223885794432545)
      ·
        refine ⟨2766113754917914345824409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3688151673223885794432545 2766113754917914345824409)
        ·
          refine ⟨2074585316188435759368307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2766113754917914345824409 2074585316188435759368307)
          ·
            refine ⟨3111877974282653639052461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074585316188435759368307 3111877974282653639052461)
            ·
              refine ⟨1166954240355995114644673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3111877974282653639052461 1166954240355995114644673)
              ·
                refine ⟨875215680266996335983505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166954240355995114644673 875215680266996335983505)
                ·
                  refine ⟨656411760200247251987629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 875215680266996335983505 656411760200247251987629)
                  ·
                    refine ⟨246154410075092719495361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 656411760200247251987629 246154410075092719495361)
                    ·
                      refine ⟨184615807556319539621521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246154410075092719495361 184615807556319539621521)
                      ·
                        rfl

theorem cell23_359538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_359538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359538 prefixEnd_359538 := by exact prefixLift 359538
  have htrace : WordTrace (prefixWord ++ tailWord_359538) baseStart_359538 baseEnd_359538 := by
    simpa [prefixWord, tailWord_359538, baseEnd_359538] using wordTrace_append hprefix tailTrace_359538
  have hstable : (prefixWord ++ tailWord_359538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359538).length < 2 ^ (prefixWord ++ tailWord_359538).sum := by decide
  have hdescent : baseEnd_359538 < baseStart_359538 := by decide
  rcases family_descends (prefixWord ++ tailWord_359538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359545 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 3, 1, 3]
def baseStart_359545 : Nat := 118140960795 + 359545 * 2 ^ 59
def prefixEnd_359545 : Nat := 4983230072969 + 3 ^ 40 * 359545 * 2
def baseEnd_359545 : Nat := 184619401920901012233989

theorem tailTrace_359545 : CollatzResearch.WordTrace tailWord_359545 prefixEnd_359545 184619401920901012233989 := by
  unfold tailWord_359545
  simp only [CollatzResearch.WordTrace]
  refine ⟨13113683482437345242376089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8742455654958230161584059 13113683482437345242376089)
  ·
    refine ⟨9835262611828008931782067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13113683482437345242376089 9835262611828008931782067)
    ·
      refine ⟨14752893917742013397673101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9835262611828008931782067 14752893917742013397673101)
      ·
        refine ⟨5532335219153255024127413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14752893917742013397673101 5532335219153255024127413)
        ·
          refine ⟨518656426795617658511945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5532335219153255024127413 518656426795617658511945)
          ·
            refine ⟨388992320096713243883959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518656426795617658511945 388992320096713243883959)
            ·
              refine ⟨583488480145069865825939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388992320096713243883959 583488480145069865825939)
              ·
                refine ⟨875232720217604798738909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583488480145069865825939 875232720217604798738909)
                ·
                  refine ⟨328212270081601799527091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875232720217604798738909 328212270081601799527091)
                  ·
                    refine ⟨492318405122402699290637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 328212270081601799527091 492318405122402699290637)
                    ·
                      refine ⟨184619401920901012233989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 492318405122402699290637 184619401920901012233989)
                      ·
                        rfl

theorem cell23_359545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_359545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359545 prefixEnd_359545 := by exact prefixLift 359545
  have htrace : WordTrace (prefixWord ++ tailWord_359545) baseStart_359545 baseEnd_359545 := by
    simpa [prefixWord, tailWord_359545, baseEnd_359545] using wordTrace_append hprefix tailTrace_359545
  have hstable : (prefixWord ++ tailWord_359545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359545).length < 2 ^ (prefixWord ++ tailWord_359545).sum := by decide
  have hdescent : baseEnd_359545 < baseStart_359545 := by decide
  rcases family_descends (prefixWord ++ tailWord_359545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359564 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_359564 : Nat := 118140960795 + 359564 * 2 ^ 59
def prefixEnd_359564 : Nat := 4983230072969 + 3 ^ 40 * 359564 * 2
def baseEnd_359564 : Nat := 184629158053336437896401

theorem tailTrace_359564 : CollatzResearch.WordTrace tailWord_359564 prefixEnd_359564 184629158053336437896401 := by
  unfold tailWord_359564
  simp only [CollatzResearch.WordTrace]
  refine ⟨6557188234684255743658873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8742917646245674324878497 6557188234684255743658873)
  ·
    refine ⟨4917891176013191807744155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6557188234684255743658873 4917891176013191807744155)
    ·
      refine ⟨7376836764019787711616233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4917891176013191807744155 7376836764019787711616233)
      ·
        refine ⟨5532627573014840783712175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7376836764019787711616233 5532627573014840783712175)
        ·
          refine ⟨8298941359522261175568263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5532627573014840783712175 8298941359522261175568263)
          ·
            refine ⟨12448412039283391763352395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8298941359522261175568263 12448412039283391763352395)
            ·
              refine ⟨18672618058925087645028593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12448412039283391763352395 18672618058925087645028593)
              ·
                refine ⟨14004463544193815733771445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18672618058925087645028593 14004463544193815733771445)
                ·
                  refine ⟨1312918457268170225041073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14004463544193815733771445 1312918457268170225041073)
                  ·
                    refine ⟨984688842951127668780805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1312918457268170225041073 984688842951127668780805)
                    ·
                      refine ⟨184629158053336437896401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 984688842951127668780805 184629158053336437896401)
                      ·
                        rfl

theorem cell23_359564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_359564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359564 prefixEnd_359564 := by exact prefixLift 359564
  have htrace : WordTrace (prefixWord ++ tailWord_359564) baseStart_359564 baseEnd_359564 := by
    simpa [prefixWord, tailWord_359564, baseEnd_359564] using wordTrace_append hprefix tailTrace_359564
  have hstable : (prefixWord ++ tailWord_359564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359564).length < 2 ^ (prefixWord ++ tailWord_359564).sum := by decide
  have hdescent : baseEnd_359564 < baseStart_359564 := by decide
  rcases family_descends (prefixWord ++ tailWord_359564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359581 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_359581 : Nat := 118140960795 + 359581 * 2 ^ 59
def prefixEnd_359581 : Nat := 4983230072969 + 3 ^ 40 * 359581 * 2
def baseEnd_359581 : Nat := 184637887224462871383823

theorem tailTrace_359581 : CollatzResearch.WordTrace tailWord_359581 prefixEnd_359581 184637887224462871383823 := by
  unfold tailWord_359581
  simp only [CollatzResearch.WordTrace]
  refine ⟨13114996510306923390686597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8743331006871282260457731 13114996510306923390686597)
  ·
    refine ⟨2459061845682548135753737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13114996510306923390686597 2459061845682548135753737)
    ·
      refine ⟨1844296384261911101815303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2459061845682548135753737 1844296384261911101815303)
      ·
        refine ⟨2766444576392866652722955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844296384261911101815303 2766444576392866652722955)
        ·
          refine ⟨4149666864589299979084433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766444576392866652722955 4149666864589299979084433)
          ·
            refine ⟨3112250148441974984313325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4149666864589299979084433 3112250148441974984313325)
            ·
              refine ⟨1167093805665740619117497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3112250148441974984313325 1167093805665740619117497)
              ·
                refine ⟨875320354249305464338123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167093805665740619117497 875320354249305464338123)
                ·
                  refine ⟨1312980531373958196507185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875320354249305464338123 1312980531373958196507185)
                  ·
                    refine ⟨984735398530468647380389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1312980531373958196507185 984735398530468647380389)
                    ·
                      refine ⟨184637887224462871383823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 984735398530468647380389 184637887224462871383823)
                      ·
                        rfl

theorem cell23_359581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_359581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359581 prefixEnd_359581 := by exact prefixLift 359581
  have htrace : WordTrace (prefixWord ++ tailWord_359581) baseStart_359581 baseEnd_359581 := by
    simpa [prefixWord, tailWord_359581, baseEnd_359581] using wordTrace_append hprefix tailTrace_359581
  have hstable : (prefixWord ++ tailWord_359581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359581).length < 2 ^ (prefixWord ++ tailWord_359581).sum := by decide
  have hdescent : baseEnd_359581 < baseStart_359581 := by decide
  rcases family_descends (prefixWord ++ tailWord_359581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359588 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_359588 : Nat := 118140960795 + 359588 * 2 ^ 59
def prefixEnd_359588 : Nat := 4983230072969 + 3 ^ 40 * 359588 * 2
def baseEnd_359588 : Nat := 184641481589044343996291

theorem tailTrace_359588 : CollatzResearch.WordTrace tailWord_359588 prefixEnd_359588 184641481589044343996291 := by
  unfold tailWord_359588
  simp only [CollatzResearch.WordTrace]
  refine ⟨6557625910640781793095709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8743501214187709057460945 6557625910640781793095709)
  ·
    refine ⟨2459109716490293172410891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6557625910640781793095709 2459109716490293172410891)
    ·
      refine ⟨3688664574735439758616337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2459109716490293172410891 3688664574735439758616337)
      ·
        refine ⟨2766498431051579818962253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3688664574735439758616337 2766498431051579818962253)
        ·
          refine ⟨1037436911644342432110845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2766498431051579818962253 1037436911644342432110845)
          ·
            refine ⟨389038841866628412041567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1037436911644342432110845 389038841866628412041567)
            ·
              refine ⟨583558262799942618062351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389038841866628412041567 583558262799942618062351)
              ·
                refine ⟨875337394199913927093527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583558262799942618062351 875337394199913927093527)
                ·
                  refine ⟨1313006091299870890640291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875337394199913927093527 1313006091299870890640291)
                  ·
                    refine ⟨1969509136949806335960437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1313006091299870890640291 1969509136949806335960437)
                    ·
                      refine ⟨184641481589044343996291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1969509136949806335960437 184641481589044343996291)
                      ·
                        rfl

theorem cell23_359588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_359588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359588 prefixEnd_359588 := by exact prefixLift 359588
  have htrace : WordTrace (prefixWord ++ tailWord_359588) baseStart_359588 baseEnd_359588 := by
    simpa [prefixWord, tailWord_359588, baseEnd_359588] using wordTrace_append hprefix tailTrace_359588
  have hstable : (prefixWord ++ tailWord_359588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359588).length < 2 ^ (prefixWord ++ tailWord_359588).sum := by decide
  have hdescent : baseEnd_359588 < baseStart_359588 := by decide
  rcases family_descends (prefixWord ++ tailWord_359588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359602 : List Nat := [3, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2]
def baseStart_359602 : Nat := 118140960795 + 359602 * 2 ^ 59
def prefixEnd_359602 : Nat := 4983230072969 + 3 ^ 40 * 359602 * 2
def baseEnd_359602 : Nat := 184648670318207289221227

theorem tailTrace_359602 : CollatzResearch.WordTrace tailWord_359602 prefixEnd_359602 184648670318207289221227 := by
  unfold tailWord_359602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278940610807710994300265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8743841628820562651467373 3278940610807710994300265)
  ·
    refine ⟨2459205458105783245725199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3278940610807710994300265 2459205458105783245725199)
    ·
      refine ⟨3688808187158674868587799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2459205458105783245725199 3688808187158674868587799)
      ·
        refine ⟨5533212280738012302881699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3688808187158674868587799 5533212280738012302881699)
        ·
          refine ⟨8299818421107018454322549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5533212280738012302881699 8299818421107018454322549)
          ·
            refine ⟨778107976978782980092739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8299818421107018454322549 778107976978782980092739)
            ·
              refine ⟨1167161965468174470139109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778107976978782980092739 1167161965468174470139109)
              ·
                refine ⟨218842868525282713151083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1167161965468174470139109 218842868525282713151083)
                ·
                  refine ⟨328264302787924069726625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218842868525282713151083 328264302787924069726625)
                  ·
                    refine ⟨246198227090943052294969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328264302787924069726625 246198227090943052294969)
                    ·
                      refine ⟨184648670318207289221227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246198227090943052294969 184648670318207289221227)
                      ·
                        rfl

theorem cell23_359602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_359602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359602 prefixEnd_359602 := by exact prefixLift 359602
  have htrace : WordTrace (prefixWord ++ tailWord_359602) baseStart_359602 baseEnd_359602 := by
    simpa [prefixWord, tailWord_359602, baseEnd_359602] using wordTrace_append hprefix tailTrace_359602
  have hstable : (prefixWord ++ tailWord_359602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359602).length < 2 ^ (prefixWord ++ tailWord_359602).sum := by decide
  have hdescent : baseEnd_359602 < baseStart_359602 := by decide
  rcases family_descends (prefixWord ++ tailWord_359602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359636 : List Nat := [2, 4, 1, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_359636 : Nat := 118140960795 + 359636 * 2 ^ 59
def prefixEnd_359636 : Nat := 4983230072969 + 3 ^ 40 * 359636 * 2
def baseEnd_359636 : Nat := 184666128660460156196071

theorem tailTrace_359636 : CollatzResearch.WordTrace tailWord_359636 prefixEnd_359636 184666128660460156196071 := by
  unfold tailWord_359636
  simp only [CollatzResearch.WordTrace]
  refine ⟨6558501262553833891969381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8744668350071778522625841 6558501262553833891969381)
  ·
    refine ⟨1229718986728843854744259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6558501262553833891969381 1229718986728843854744259)
    ·
      refine ⟨1844578480093265782116389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1229718986728843854744259 1844578480093265782116389)
      ·
        refine ⟨345858465017487334146823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1844578480093265782116389 345858465017487334146823)
        ·
          refine ⟨518787697526231001220235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345858465017487334146823 518787697526231001220235)
          ·
            refine ⟨778181546289346501830353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518787697526231001220235 778181546289346501830353)
            ·
              refine ⟨583636159717009876372765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778181546289346501830353 583636159717009876372765)
              ·
                refine ⟨218863559893878703639787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 583636159717009876372765 218863559893878703639787)
                ·
                  refine ⟨328295339840818055459681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218863559893878703639787 328295339840818055459681)
                  ·
                    refine ⟨246221504880613541594761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328295339840818055459681 246221504880613541594761)
                    ·
                      refine ⟨184666128660460156196071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246221504880613541594761 184666128660460156196071)
                      ·
                        rfl

theorem cell23_359636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_359636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359636 prefixEnd_359636 := by exact prefixLift 359636
  have htrace : WordTrace (prefixWord ++ tailWord_359636) baseStart_359636 baseEnd_359636 := by
    simpa [prefixWord, tailWord_359636, baseEnd_359636] using wordTrace_append hprefix tailTrace_359636
  have hstable : (prefixWord ++ tailWord_359636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359636).length < 2 ^ (prefixWord ++ tailWord_359636).sum := by decide
  have hdescent : baseEnd_359636 < baseStart_359636 := by decide
  rcases family_descends (prefixWord ++ tailWord_359636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359681 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 7]
def baseStart_359681 : Nat := 118140960795 + 359681 * 2 ^ 59
def prefixEnd_359681 : Nat := 4983230072969 + 3 ^ 40 * 359681 * 2
def baseEnd_359681 : Nat := 20521026143323608903707

theorem tailTrace_359681 : CollatzResearch.WordTrace tailWord_359681 prefixEnd_359681 20521026143323608903707 := by
  unfold tailWord_359681
  simp only [CollatzResearch.WordTrace]
  refine ⟨13118643809944640469326897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8745762539963093646217931 13118643809944640469326897)
  ·
    refine ⟨9838982857458480351995173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13118643809944640469326897 9838982857458480351995173)
    ·
      refine ⟨1844809285773465065999095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9838982857458480351995173 1844809285773465065999095)
      ·
        refine ⟨2767213928660197598998643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844809285773465065999095 2767213928660197598998643)
        ·
          refine ⟨4150820892990296398497965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767213928660197598998643 4150820892990296398497965)
          ·
            refine ⟨1556557834871361149436737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4150820892990296398497965 1556557834871361149436737)
            ·
              refine ⟨1167418376153520862077553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556557834871361149436737 1167418376153520862077553)
              ·
                refine ⟨875563782115140646558165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167418376153520862077553 875563782115140646558165)
                ·
                  refine ⟨20521026143323608903707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 875563782115140646558165 20521026143323608903707)
                  ·
                    rfl

theorem cell23_359681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 7].length) (baseStart_359681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359681 prefixEnd_359681 := by exact prefixLift 359681
  have htrace : WordTrace (prefixWord ++ tailWord_359681) baseStart_359681 baseEnd_359681 := by
    simpa [prefixWord, tailWord_359681, baseEnd_359681] using wordTrace_append hprefix tailTrace_359681
  have hstable : (prefixWord ++ tailWord_359681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359681).length < 2 ^ (prefixWord ++ tailWord_359681).sum := by decide
  have hdescent : baseEnd_359681 < baseStart_359681 := by decide
  rcases family_descends (prefixWord ++ tailWord_359681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359715 : List Nat := [1, 1, 1, 4, 2, 4, 3, 2, 5]
def baseStart_359715 : Nat := 118140960795 + 359715 * 2 ^ 59
def prefixEnd_359715 : Nat := 4983230072969 + 3 ^ 40 * 359715 * 2
def baseEnd_359715 : Nat := 20522965959129483012023

theorem tailTrace_359715 : CollatzResearch.WordTrace tailWord_359715 prefixEnd_359715 20522965959129483012023 := by
  unfold tailWord_359715
  simp only [CollatzResearch.WordTrace]
  refine ⟨13119883891821464276064599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8746589261214309517376399 13119883891821464276064599)
  ·
    refine ⟨19679825837732196414096899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13119883891821464276064599 19679825837732196414096899)
    ·
      refine ⟨29519738756598294621145349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19679825837732196414096899 29519738756598294621145349)
      ·
        refine ⟨5534951016862180241464753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29519738756598294621145349 5534951016862180241464753)
        ·
          refine ⟨4151213262646635181098565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5534951016862180241464753 4151213262646635181098565)
          ·
            refine ⟨778352486746244096455981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4151213262646635181098565 778352486746244096455981)
            ·
              refine ⟨291882182529841536170993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 778352486746244096455981 291882182529841536170993)
              ·
                refine ⟨218911636897381152128245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291882182529841536170993 218911636897381152128245)
                ·
                  refine ⟨20522965959129483012023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218911636897381152128245 20522965959129483012023)
                  ·
                    rfl

theorem cell23_359715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 5].length) (baseStart_359715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359715 prefixEnd_359715 := by exact prefixLift 359715
  have htrace : WordTrace (prefixWord ++ tailWord_359715) baseStart_359715 baseEnd_359715 := by
    simpa [prefixWord, tailWord_359715, baseEnd_359715] using wordTrace_append hprefix tailTrace_359715
  have hstable : (prefixWord ++ tailWord_359715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359715).length < 2 ^ (prefixWord ++ tailWord_359715).sum := by decide
  have hdescent : baseEnd_359715 < baseStart_359715 := by decide
  rcases family_descends (prefixWord ++ tailWord_359715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359745 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 2, 5]
def baseStart_359745 : Nat := 118140960795 + 359745 * 2 ^ 59
def prefixEnd_359745 : Nat := 4983230072969 + 3 ^ 40 * 359745 * 2
def baseEnd_359745 : Nat := 61574032683933409911023

theorem tailTrace_359745 : CollatzResearch.WordTrace tailWord_359745 prefixEnd_359745 61574032683933409911023 := by
  unfold tailWord_359745
  simp only [CollatzResearch.WordTrace]
  refine ⟨13120978081712779399656689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8747318721141852933104459 13120978081712779399656689)
  ·
    refine ⟨9840733561284584549742517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13120978081712779399656689 9840733561284584549742517)
    ·
      refine ⟨922568771370429801538361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9840733561284584549742517 922568771370429801538361)
      ·
        refine ⟨691926578527822351153771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 922568771370429801538361 691926578527822351153771)
        ·
          refine ⟨1037889867791733526730657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691926578527822351153771 1037889867791733526730657)
          ·
            refine ⟨778417400843800145047993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037889867791733526730657 778417400843800145047993)
            ·
              refine ⟨583813050632850108785995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778417400843800145047993 583813050632850108785995)
              ·
                refine ⟨875719575949275163178993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583813050632850108785995 875719575949275163178993)
                ·
                  refine ⟨656789681961956372384245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 875719575949275163178993 656789681961956372384245)
                  ·
                    refine ⟨61574032683933409911023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 656789681961956372384245 61574032683933409911023)
                    ·
                      rfl

theorem cell23_359745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_359745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359745 prefixEnd_359745 := by exact prefixLift 359745
  have htrace : WordTrace (prefixWord ++ tailWord_359745) baseStart_359745 baseEnd_359745 := by
    simpa [prefixWord, tailWord_359745, baseEnd_359745] using wordTrace_append hprefix tailTrace_359745
  have hstable : (prefixWord ++ tailWord_359745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359745).length < 2 ^ (prefixWord ++ tailWord_359745).sum := by decide
  have hdescent : baseEnd_359745 < baseStart_359745 := by decide
  rcases family_descends (prefixWord ++ tailWord_359745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359761 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_359761 : Nat := 118140960795 + 359761 * 2 ^ 59
def prefixEnd_359761 : Nat := 4983230072969 + 3 ^ 40 * 359761 * 2
def baseEnd_359761 : Nat := 184730313742272167132995

theorem tailTrace_359761 : CollatzResearch.WordTrace tailWord_359761 prefixEnd_359761 184730313742272167132995 := by
  unfold tailWord_359761
  simp only [CollatzResearch.WordTrace]
  refine ⟨13121561649654814132239137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8747707766436542754826091 13121561649654814132239137)
  ·
    refine ⟨9841171237241110599179353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13121561649654814132239137 9841171237241110599179353)
    ·
      refine ⟨7380878427930832949384515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9841171237241110599179353 7380878427930832949384515)
      ·
        refine ⟨11071317641896249424076773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7380878427930832949384515 11071317641896249424076773)
        ·
          refine ⟨2075872057855546767014395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11071317641896249424076773 2075872057855546767014395)
          ·
            refine ⟨3113808086783320150521593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075872057855546767014395 3113808086783320150521593)
            ·
              refine ⟨2335356065087490112891195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3113808086783320150521593 2335356065087490112891195)
              ·
                refine ⟨3503034097631235169336793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335356065087490112891195 3503034097631235169336793)
                ·
                  refine ⟨2627275573223426377002595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503034097631235169336793 2627275573223426377002595)
                  ·
                    refine ⟨3940913359835139565503893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2627275573223426377002595 3940913359835139565503893)
                    ·
                      refine ⟨184730313742272167132995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3940913359835139565503893 184730313742272167132995)
                      ·
                        rfl

theorem cell23_359761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_359761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359761 prefixEnd_359761 := by exact prefixLift 359761
  have htrace : WordTrace (prefixWord ++ tailWord_359761) baseStart_359761 baseEnd_359761 := by
    simpa [prefixWord, tailWord_359761, baseEnd_359761] using wordTrace_append hprefix tailTrace_359761
  have hstable : (prefixWord ++ tailWord_359761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359761).length < 2 ^ (prefixWord ++ tailWord_359761).sum := by decide
  have hdescent : baseEnd_359761 < baseStart_359761 := by decide
  rcases family_descends (prefixWord ++ tailWord_359761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359766 : List Nat := [5, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_359766 : Nat := 118140960795 + 359766 * 2 ^ 59
def prefixEnd_359766 : Nat := 4983230072969 + 3 ^ 40 * 359766 * 2
def baseEnd_359766 : Nat := 20525875682838294174497

theorem tailTrace_359766 : CollatzResearch.WordTrace tailWord_359766 prefixEnd_359766 20525875682838294174497 := by
  unfold tailWord_359766
  simp only [CollatzResearch.WordTrace]
  refine ⟨820109000914793749135697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8747829343091133324114101 820109000914793749135697)
  ·
    refine ⟨615081750686095311851773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 820109000914793749135697 615081750686095311851773)
    ·
      refine ⟨230655656507285741944415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 615081750686095311851773 230655656507285741944415)
      ·
        refine ⟨345983484760928612916623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230655656507285741944415 345983484760928612916623)
        ·
          refine ⟨518975227141392919374935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345983484760928612916623 518975227141392919374935)
          ·
            refine ⟨778462840712089379062403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518975227141392919374935 778462840712089379062403)
            ·
              refine ⟨1167694261068134068593605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778462840712089379062403 1167694261068134068593605)
              ·
                refine ⟨218942673950275137861301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1167694261068134068593605 218942673950275137861301)
                ·
                  refine ⟨20525875682838294174497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218942673950275137861301 20525875682838294174497)
                  ·
                    rfl

theorem cell23_359766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_359766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359766 prefixEnd_359766 := by exact prefixLift 359766
  have htrace : WordTrace (prefixWord ++ tailWord_359766) baseStart_359766 baseEnd_359766 := by
    simpa [prefixWord, tailWord_359766, baseEnd_359766] using wordTrace_append hprefix tailTrace_359766
  have hstable : (prefixWord ++ tailWord_359766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359766).length < 2 ^ (prefixWord ++ tailWord_359766).sum := by decide
  have hdescent : baseEnd_359766 < baseStart_359766 := by decide
  rcases family_descends (prefixWord ++ tailWord_359766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359768 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 2, 2, 3]
def baseStart_359768 : Nat := 118140960795 + 359768 * 2 ^ 59
def prefixEnd_359768 : Nat := 4983230072969 + 3 ^ 40 * 359768 * 2
def baseEnd_359768 : Nat := 184733908106853639745463

theorem tailTrace_359768 : CollatzResearch.WordTrace tailWord_359768 prefixEnd_359768 184733908106853639745463 := by
  unfold tailWord_359768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6560908480314727163871979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8747877973752969551829305 6560908480314727163871979)
  ·
    refine ⟨9841362720472090745807969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6560908480314727163871979 9841362720472090745807969)
    ·
      refine ⟨7381022040354068059355977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9841362720472090745807969 7381022040354068059355977)
      ·
        refine ⟨5535766530265551044516983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7381022040354068059355977 5535766530265551044516983)
        ·
          refine ⟨8303649795398326566775475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535766530265551044516983 8303649795398326566775475)
          ·
            refine ⟨12455474693097489850163213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8303649795398326566775475 12455474693097489850163213)
            ·
              refine ⟨4670803009911558693811205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12455474693097489850163213 4670803009911558693811205)
              ·
                refine ⟨875775564358417255089601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4670803009911558693811205 875775564358417255089601)
                ·
                  refine ⟨656831673268812941317201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 875775564358417255089601 656831673268812941317201)
                  ·
                    refine ⟨492623754951609705987901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 656831673268812941317201 492623754951609705987901)
                    ·
                      refine ⟨184733908106853639745463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 492623754951609705987901 184733908106853639745463)
                      ·
                        rfl

theorem cell23_359768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_359768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359768 prefixEnd_359768 := by exact prefixLift 359768
  have htrace : WordTrace (prefixWord ++ tailWord_359768) baseStart_359768 baseEnd_359768 := by
    simpa [prefixWord, tailWord_359768, baseEnd_359768] using wordTrace_append hprefix tailTrace_359768
  have hstable : (prefixWord ++ tailWord_359768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359768).length < 2 ^ (prefixWord ++ tailWord_359768).sum := by decide
  have hdescent : baseEnd_359768 < baseStart_359768 := by decide
  rcases family_descends (prefixWord ++ tailWord_359768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359788 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 6]
def baseStart_359788 : Nat := 118140960795 + 359788 * 2 ^ 59
def prefixEnd_359788 : Nat := 4983230072969 + 3 ^ 40 * 359788 * 2
def baseEnd_359788 : Nat := 20527130857771506832819

theorem tailTrace_359788 : CollatzResearch.WordTrace tailWord_359788 prefixEnd_359788 20527130857771506832819 := by
  unfold tailWord_359788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6561273210278498871736009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8748364280371331828981345 6561273210278498871736009)
  ·
    refine ⟨4920954907708874153802007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6561273210278498871736009 4920954907708874153802007)
    ·
      refine ⟨7381432361563311230703011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4920954907708874153802007 7381432361563311230703011)
      ·
        refine ⟨11072148542344966846054517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7381432361563311230703011 11072148542344966846054517)
        ·
          refine ⟨1038013925844840641817611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11072148542344966846054517 1038013925844840641817611)
          ·
            refine ⟨1557020888767260962726417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038013925844840641817611 1557020888767260962726417)
            ·
              refine ⟨1167765666575445722044813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1557020888767260962726417 1167765666575445722044813)
              ·
                refine ⟨437912124965792145766805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1167765666575445722044813 437912124965792145766805)
                ·
                  refine ⟨20527130857771506832819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 437912124965792145766805 20527130857771506832819)
                  ·
                    rfl

theorem cell23_359788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_359788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359788 prefixEnd_359788 := by exact prefixLift 359788
  have htrace : WordTrace (prefixWord ++ tailWord_359788) baseStart_359788 baseEnd_359788 := by
    simpa [prefixWord, tailWord_359788, baseEnd_359788] using wordTrace_append hprefix tailTrace_359788
  have hstable : (prefixWord ++ tailWord_359788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359788).length < 2 ^ (prefixWord ++ tailWord_359788).sum := by decide
  have hdescent : baseEnd_359788 < baseStart_359788 := by decide
  rcases family_descends (prefixWord ++ tailWord_359788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359809 : List Nat := [1, 2, 4, 3, 2, 1, 2, 3, 1, 4]
def baseStart_359809 : Nat := 118140960795 + 359809 * 2 ^ 59
def prefixEnd_359809 : Nat := 4983230072969 + 3 ^ 40 * 359809 * 2
def baseEnd_359809 : Nat := 61584986937895993110925

theorem tailTrace_359809 : CollatzResearch.WordTrace tailWord_359809 prefixEnd_359809 61584986937895993110925 := by
  unfold tailWord_359809
  simp only [CollatzResearch.WordTrace]
  refine ⟨13123312353480918329986481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8748874902320612219990987 13123312353480918329986481)
  ·
    refine ⟨9842484265110688747489861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13123312353480918329986481 9842484265110688747489861)
    ·
      refine ⟨1845465799708254140154349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9842484265110688747489861 1845465799708254140154349)
      ·
        refine ⟨692049674890595302557881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1845465799708254140154349 692049674890595302557881)
        ·
          refine ⟨519037256167946476918411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692049674890595302557881 519037256167946476918411)
          ·
            refine ⟨778555884251919715377617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519037256167946476918411 778555884251919715377617)
            ·
              refine ⟨583916913188939786533213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778555884251919715377617 583916913188939786533213)
              ·
                refine ⟨218968842445852419949955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 583916913188939786533213 218968842445852419949955)
                ·
                  refine ⟨328453263668778629924933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218968842445852419949955 328453263668778629924933)
                  ·
                    refine ⟨61584986937895993110925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 328453263668778629924933 61584986937895993110925)
                    ·
                      rfl

theorem cell23_359809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_359809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359809 prefixEnd_359809 := by exact prefixLift 359809
  have htrace : WordTrace (prefixWord ++ tailWord_359809) baseStart_359809 baseEnd_359809 := by
    simpa [prefixWord, tailWord_359809, baseEnd_359809] using wordTrace_append hprefix tailTrace_359809
  have hstable : (prefixWord ++ tailWord_359809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359809).length < 2 ^ (prefixWord ++ tailWord_359809).sum := by decide
  have hdescent : baseEnd_359809 < baseStart_359809 := by decide
  rcases family_descends (prefixWord ++ tailWord_359809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359822 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_359822 : Nat := 118140960795 + 359822 * 2 ^ 59
def prefixEnd_359822 : Nat := 4983230072969 + 3 ^ 40 * 359822 * 2
def baseEnd_359822 : Nat := 20529070673577380941135

theorem tailTrace_359822 : CollatzResearch.WordTrace tailWord_359822 prefixEnd_359822 20529070673577380941135 := by
  unfold tailWord_359822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640473312804227693776215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8749191001622547700139813 1640473312804227693776215)
  ·
    refine ⟨2460709969206341540664323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1640473312804227693776215 2460709969206341540664323)
    ·
      refine ⟨3691064953809512310996485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2460709969206341540664323 3691064953809512310996485)
      ·
        refine ⟨692074678839283558311841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3691064953809512310996485 692074678839283558311841)
        ·
          refine ⟨519056009129462668733881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692074678839283558311841 519056009129462668733881)
          ·
            refine ⟨389292006847097001550411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519056009129462668733881 389292006847097001550411)
            ·
              refine ⟨583938010270645502325617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389292006847097001550411 583938010270645502325617)
              ·
                refine ⟨437953507702984126744213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583938010270645502325617 437953507702984126744213)
                ·
                  refine ⟨20529070673577380941135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 437953507702984126744213 20529070673577380941135)
                  ·
                    rfl

theorem cell23_359822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_359822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359822 prefixEnd_359822 := by exact prefixLift 359822
  have htrace : WordTrace (prefixWord ++ tailWord_359822) baseStart_359822 baseEnd_359822 := by
    simpa [prefixWord, tailWord_359822, baseEnd_359822] using wordTrace_append hprefix tailTrace_359822
  have hstable : (prefixWord ++ tailWord_359822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359822).length < 2 ^ (prefixWord ++ tailWord_359822).sum := by decide
  have hdescent : baseEnd_359822 < baseStart_359822 := by decide
  rcases family_descends (prefixWord ++ tailWord_359822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359875 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 1, 2, 3]
def baseStart_359875 : Nat := 118140960795 + 359875 * 2 ^ 59
def prefixEnd_359875 : Nat := 4983230072969 + 3 ^ 40 * 359875 * 2
def baseEnd_359875 : Nat := 184788850536884721107471

theorem tailTrace_359875 : CollatzResearch.WordTrace tailWord_359875 prefixEnd_359875 184788850536884721107471 := by
  unfold tailWord_359875
  simp only [CollatzResearch.WordTrace]
  refine ⟨13125719571241811601889079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8750479714161207734592719 13125719571241811601889079)
  ·
    refine ⟨19688579356862717402833619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13125719571241811601889079 19688579356862717402833619)
    ·
      refine ⟨29532869035294076104250429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19688579356862717402833619 29532869035294076104250429)
      ·
        refine ⟨11074825888235278539093911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29532869035294076104250429 11074825888235278539093911)
        ·
          refine ⟨16612238832352917808640867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11074825888235278539093911 16612238832352917808640867)
          ·
            refine ⟨24918358248529376712961301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16612238832352917808640867 24918358248529376712961301)
            ·
              refine ⟨1168048042899814533420061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24918358248529376712961301 1168048042899814533420061)
              ·
                refine ⟨438018016087430450032523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1168048042899814533420061 438018016087430450032523)
                ·
                  refine ⟨657027024131145675048785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438018016087430450032523 657027024131145675048785)
                  ·
                    refine ⟨492770268098359256286589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 657027024131145675048785 492770268098359256286589)
                    ·
                      refine ⟨184788850536884721107471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 492770268098359256286589 184788850536884721107471)
                      ·
                        rfl

theorem cell23_359875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_359875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359875 prefixEnd_359875 := by exact prefixLift 359875
  have htrace : WordTrace (prefixWord ++ tailWord_359875) baseStart_359875 baseEnd_359875 := by
    simpa [prefixWord, tailWord_359875, baseEnd_359875] using wordTrace_append hprefix tailTrace_359875
  have hstable : (prefixWord ++ tailWord_359875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359875).length < 2 ^ (prefixWord ++ tailWord_359875).sum := by decide
  have hdescent : baseEnd_359875 < baseStart_359875 := by decide
  rcases family_descends (prefixWord ++ tailWord_359875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359888 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 3]
def baseStart_359888 : Nat := 118140960795 + 359888 * 2 ^ 59
def prefixEnd_359888 : Nat := 4983230072969 + 3 ^ 40 * 359888 * 2
def baseEnd_359888 : Nat := 184795525785393170244911

theorem tailTrace_359888 : CollatzResearch.WordTrace tailWord_359888 prefixEnd_359888 184795525785393170244911 := by
  unfold tailWord_359888
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563096860097357411056159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8750795813463143214741545 6563096860097357411056159)
  ·
    refine ⟨9844645290146036116584239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6563096860097357411056159 9844645290146036116584239)
    ·
      refine ⟨14766967935219054174876359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9844645290146036116584239 14766967935219054174876359)
      ·
        refine ⟨22150451902828581262314539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14766967935219054174876359 22150451902828581262314539)
        ·
          refine ⟨33225677854242871893471809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22150451902828581262314539 33225677854242871893471809)
          ·
            refine ⟨24919258390682153920103857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33225677854242871893471809 24919258390682153920103857)
            ·
              refine ⟨18689443793011615440077893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24919258390682153920103857 18689443793011615440077893)
              ·
                refine ⟨3504270711189677895014605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18689443793011615440077893 3504270711189677895014605)
                ·
                  refine ⟨1314101516696129210630477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3504270711189677895014605 1314101516696129210630477)
                  ·
                    refine ⟨492788068761048453986429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314101516696129210630477 492788068761048453986429)
                    ·
                      refine ⟨184795525785393170244911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 492788068761048453986429 184795525785393170244911)
                      ·
                        rfl

theorem cell23_359888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 3].length) (baseStart_359888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359888 prefixEnd_359888 := by exact prefixLift 359888
  have htrace : WordTrace (prefixWord ++ tailWord_359888) baseStart_359888 baseEnd_359888 := by
    simpa [prefixWord, tailWord_359888, baseEnd_359888] using wordTrace_append hprefix tailTrace_359888
  have hstable : (prefixWord ++ tailWord_359888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359888).length < 2 ^ (prefixWord ++ tailWord_359888).sum := by decide
  have hdescent : baseEnd_359888 < baseStart_359888 := by decide
  rcases family_descends (prefixWord ++ tailWord_359888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359909 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 1, 2, 3]
def baseStart_359909 : Nat := 118140960795 + 359909 * 2 ^ 59
def prefixEnd_359909 : Nat := 4983230072969 + 3 ^ 40 * 359909 * 2
def baseEnd_359909 : Nat := 184806308879137588082315

theorem tailTrace_359909 : CollatzResearch.WordTrace tailWord_359909 prefixEnd_359909 184806308879137588082315 := by
  unfold tailWord_359909
  simp only [CollatzResearch.WordTrace]
  refine ⟨13126959653118635408626781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8751306435412423605751187 13126959653118635408626781)
  ·
    refine ⟨4922609869919488278235043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13126959653118635408626781 4922609869919488278235043)
    ·
      refine ⟨7383914804879232417352565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4922609869919488278235043 7383914804879232417352565)
      ·
        refine ⟨692242012957428039126803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7383914804879232417352565 692242012957428039126803)
        ·
          refine ⟨1038363019436142058690205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692242012957428039126803 1038363019436142058690205)
          ·
            refine ⟨389386132288553272008827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1038363019436142058690205 389386132288553272008827)
            ·
              refine ⟨584079198432829908013241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389386132288553272008827 584079198432829908013241)
              ·
                refine ⟨438059398824622431009931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584079198432829908013241 438059398824622431009931)
                ·
                  refine ⟨657089098236933646514897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438059398824622431009931 657089098236933646514897)
                  ·
                    refine ⟨492816823677700234886173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 657089098236933646514897 492816823677700234886173)
                    ·
                      refine ⟨184806308879137588082315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 492816823677700234886173 184806308879137588082315)
                      ·
                        rfl

theorem cell23_359909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_359909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359909 prefixEnd_359909 := by exact prefixLift 359909
  have htrace : WordTrace (prefixWord ++ tailWord_359909) baseStart_359909 baseEnd_359909 := by
    simpa [prefixWord, tailWord_359909, baseEnd_359909] using wordTrace_append hprefix tailTrace_359909
  have hstable : (prefixWord ++ tailWord_359909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359909).length < 2 ^ (prefixWord ++ tailWord_359909).sum := by decide
  have hdescent : baseEnd_359909 < baseStart_359909 := by decide
  rcases family_descends (prefixWord ++ tailWord_359909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359922 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_359922 : Nat := 118140960795 + 359922 * 2 ^ 59
def prefixEnd_359922 : Nat := 4983230072969 + 3 ^ 40 * 359922 * 2
def baseEnd_359922 : Nat := 184812984127646037219755

theorem tailTrace_359922 : CollatzResearch.WordTrace tailWord_359922 prefixEnd_359922 184812984127646037219755 := by
  unfold tailWord_359922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281858450517884657212505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8751622534714359085900013 3281858450517884657212505)
  ·
    refine ⟨2461393837888413492909379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3281858450517884657212505 2461393837888413492909379)
    ·
      refine ⟨3692090756832620239364069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2461393837888413492909379 3692090756832620239364069)
      ·
        refine ⟨692267016906116294880763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3692090756832620239364069 692267016906116294880763)
        ·
          refine ⟨1038400525359174442321145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692267016906116294880763 1038400525359174442321145)
          ·
            refine ⟨778800394019380831740859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1038400525359174442321145 778800394019380831740859)
            ·
              refine ⟨1168200591029071247611289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778800394019380831740859 1168200591029071247611289)
              ·
                refine ⟨876150443271803435708467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1168200591029071247611289 876150443271803435708467)
                ·
                  refine ⟨1314225664907705153562701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876150443271803435708467 1314225664907705153562701)
                  ·
                    refine ⟨492834624340389432586013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314225664907705153562701 492834624340389432586013)
                    ·
                      refine ⟨184812984127646037219755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 492834624340389432586013 184812984127646037219755)
                      ·
                        rfl

theorem cell23_359922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_359922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359922 prefixEnd_359922 := by exact prefixLift 359922
  have htrace : WordTrace (prefixWord ++ tailWord_359922) baseStart_359922 baseEnd_359922 := by
    simpa [prefixWord, tailWord_359922, baseEnd_359922] using wordTrace_append hprefix tailTrace_359922
  have hstable : (prefixWord ++ tailWord_359922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359922).length < 2 ^ (prefixWord ++ tailWord_359922).sum := by decide
  have hdescent : baseEnd_359922 < baseStart_359922 := by decide
  rcases family_descends (prefixWord ++ tailWord_359922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359932 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 1, 3, 2]
def baseStart_359932 : Nat := 118140960795 + 359932 * 2 ^ 59
def prefixEnd_359932 : Nat := 4983230072969 + 3 ^ 40 * 359932 * 2
def baseEnd_359932 : Nat := 184818118934190998094709

theorem tailTrace_359932 : CollatzResearch.WordTrace tailWord_359932 prefixEnd_359932 184818118934190998094709 := by
  unfold tailWord_359932
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563899266017655168357025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8751865688023540224476033 6563899266017655168357025)
  ·
    refine ⟨4922924449513241376267769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6563899266017655168357025 4922924449513241376267769)
    ·
      refine ⟨3692193337134931032200827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4922924449513241376267769 3692193337134931032200827)
      ·
        refine ⟨5538290005702396548301241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3692193337134931032200827 5538290005702396548301241)
        ·
          refine ⟨4153717504276797411225931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5538290005702396548301241 4153717504276797411225931)
          ·
            refine ⟨6230576256415196116838897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4153717504276797411225931 6230576256415196116838897)
            ·
              refine ⟨4672932192311397087629173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6230576256415196116838897 4672932192311397087629173)
              ·
                refine ⟨438087393029193476965235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4672932192311397087629173 438087393029193476965235)
                ·
                  refine ⟨657131089543790215447853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438087393029193476965235 657131089543790215447853)
                  ·
                    refine ⟨246424158578921330792945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 657131089543790215447853 246424158578921330792945)
                    ·
                      refine ⟨184818118934190998094709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246424158578921330792945 184818118934190998094709)
                      ·
                        rfl

theorem cell23_359932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_359932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359932 prefixEnd_359932 := by exact prefixLift 359932
  have htrace : WordTrace (prefixWord ++ tailWord_359932) baseStart_359932 baseEnd_359932 := by
    simpa [prefixWord, tailWord_359932, baseEnd_359932] using wordTrace_append hprefix tailTrace_359932
  have hstable : (prefixWord ++ tailWord_359932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359932).length < 2 ^ (prefixWord ++ tailWord_359932).sum := by decide
  have hdescent : baseEnd_359932 < baseStart_359932 := by decide
  rcases family_descends (prefixWord ++ tailWord_359932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359940 : List Nat := [2, 3, 2, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_359940 : Nat := 118140960795 + 359940 * 2 ^ 59
def prefixEnd_359940 : Nat := 4983230072969 + 3 ^ 40 * 359940 * 2
def baseEnd_359940 : Nat := 184822226779426966794673

theorem tailTrace_359940 : CollatzResearch.WordTrace tailWord_359940 prefixEnd_359940 184822226779426966794673 := by
  unfold tailWord_359940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6564045158003163851502637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8752060210670885135336849 6564045158003163851502637)
  ·
    refine ⟨2461516934251186444313489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6564045158003163851502637 2461516934251186444313489)
    ·
      refine ⟨1846137700688389833235117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2461516934251186444313489 1846137700688389833235117)
      ·
        refine ⟨692301637758146187463169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1846137700688389833235117 692301637758146187463169)
        ·
          refine ⟨519226228318609640597377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692301637758146187463169 519226228318609640597377)
          ·
            refine ⟨389419671238957230448033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519226228318609640597377 389419671238957230448033)
            ·
              refine ⟨292064753429217922836025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389419671238957230448033 292064753429217922836025)
              ·
                refine ⟨219048565071913442127019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292064753429217922836025 219048565071913442127019)
                ·
                  refine ⟨328572847607870163190529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219048565071913442127019 328572847607870163190529)
                  ·
                    refine ⟨246429635705902622392897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328572847607870163190529 246429635705902622392897)
                    ·
                      refine ⟨184822226779426966794673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246429635705902622392897 184822226779426966794673)
                      ·
                        rfl

theorem cell23_359940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_359940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359940 prefixEnd_359940 := by exact prefixLift 359940
  have htrace : WordTrace (prefixWord ++ tailWord_359940) baseStart_359940 baseEnd_359940 := by
    simpa [prefixWord, tailWord_359940, baseEnd_359940] using wordTrace_append hprefix tailTrace_359940
  have hstable : (prefixWord ++ tailWord_359940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359940).length < 2 ^ (prefixWord ++ tailWord_359940).sum := by decide
  have hdescent : baseEnd_359940 < baseStart_359940 := by decide
  rcases family_descends (prefixWord ++ tailWord_359940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359945 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 3, 4, 2]
def baseStart_359945 : Nat := 118140960795 + 359945 * 2 ^ 59
def prefixEnd_359945 : Nat := 4983230072969 + 3 ^ 40 * 359945 * 2
def baseEnd_359945 : Nat := 184824794182699447232149

theorem tailTrace_359945 : CollatzResearch.WordTrace tailWord_359945 prefixEnd_359945 184824794182699447232149 := by
  unfold tailWord_359945
  simp only [CollatzResearch.WordTrace]
  refine ⟨13128272680988213556937289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8752181787325475704624859 13128272680988213556937289)
  ·
    refine ⟨9846204510741160167702967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13128272680988213556937289 9846204510741160167702967)
    ·
      refine ⟨14769306766111740251554451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9846204510741160167702967 14769306766111740251554451)
      ·
        refine ⟨22153960149167610377331677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14769306766111740251554451 22153960149167610377331677)
        ·
          refine ⟨8307735055937853891499379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22153960149167610377331677 8307735055937853891499379)
          ·
            refine ⟨12461602583906780837249069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8307735055937853891499379 12461602583906780837249069)
            ·
              refine ⟨4673100968965042813968401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12461602583906780837249069 4673100968965042813968401)
              ·
                refine ⟨3504825726723782110476301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4673100968965042813968401 3504825726723782110476301)
                ·
                  refine ⟨1314309647521418291428613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3504825726723782110476301 1314309647521418291428613)
                  ·
                    refine ⟨246433058910265929642865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1314309647521418291428613 246433058910265929642865)
                    ·
                      refine ⟨184824794182699447232149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246433058910265929642865 184824794182699447232149)
                      ·
                        rfl

theorem cell23_359945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 4, 2].length) (baseStart_359945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359945 prefixEnd_359945 := by exact prefixLift 359945
  have htrace : WordTrace (prefixWord ++ tailWord_359945) baseStart_359945 baseEnd_359945 := by
    simpa [prefixWord, tailWord_359945, baseEnd_359945] using wordTrace_append hprefix tailTrace_359945
  have hstable : (prefixWord ++ tailWord_359945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359945).length < 2 ^ (prefixWord ++ tailWord_359945).sum := by decide
  have hdescent : baseEnd_359945 < baseStart_359945 := by decide
  rcases family_descends (prefixWord ++ tailWord_359945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359962 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2]
def baseStart_359962 : Nat := 118140960795 + 359962 * 2 ^ 59
def prefixEnd_359962 : Nat := 4983230072969 + 3 ^ 40 * 359962 * 2
def baseEnd_359962 : Nat := 184833523353825880719571

theorem tailTrace_359962 : CollatzResearch.WordTrace tailWord_359962 prefixEnd_359962 184833523353825880719571 := by
  unfold tailWord_359962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3282223180481656365076535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8752595147951083640204093 3282223180481656365076535)
  ·
    refine ⟨4923334770722484547614803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3282223180481656365076535 4923334770722484547614803)
    ·
      refine ⟨7385002156083726821422205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4923334770722484547614803 7385002156083726821422205)
      ·
        refine ⟨2769375808531397558033327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7385002156083726821422205 2769375808531397558033327)
        ·
          refine ⟨4154063712797096337049991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769375808531397558033327 4154063712797096337049991)
          ·
            refine ⟨6231095569195644505574987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154063712797096337049991 6231095569195644505574987)
            ·
              refine ⟨9346643353793466758362481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6231095569195644505574987 9346643353793466758362481)
              ·
                refine ⟨7009982515345100068771861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9346643353793466758362481 7009982515345100068771861)
                ·
                  refine ⟨328592930406801565723681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7009982515345100068771861 328592930406801565723681)
                  ·
                    refine ⟨246444697805101174292761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328592930406801565723681 246444697805101174292761)
                    ·
                      refine ⟨184833523353825880719571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246444697805101174292761 184833523353825880719571)
                      ·
                        rfl

theorem cell23_359962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_359962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359962 prefixEnd_359962 := by exact prefixLift 359962
  have htrace : WordTrace (prefixWord ++ tailWord_359962) baseStart_359962 baseEnd_359962 := by
    simpa [prefixWord, tailWord_359962, baseEnd_359962] using wordTrace_append hprefix tailTrace_359962
  have hstable : (prefixWord ++ tailWord_359962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359962).length < 2 ^ (prefixWord ++ tailWord_359962).sum := by decide
  have hdescent : baseEnd_359962 < baseStart_359962 := by decide
  rcases family_descends (prefixWord ++ tailWord_359962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359965 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_359965 : Nat := 118140960795 + 359965 * 2 ^ 59
def prefixEnd_359965 : Nat := 4983230072969 + 3 ^ 40 * 359965 * 2
def baseEnd_359965 : Nat := 184835063795789368982057

theorem tailTrace_359965 : CollatzResearch.WordTrace tailWord_359965 prefixEnd_359965 184835063795789368982057 := by
  unfold tailWord_359965
  simp only [CollatzResearch.WordTrace]
  refine ⟨13129002140915756972665349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8752668093943837981776899 13129002140915756972665349)
  ·
    refine ⟨2461687901421704432374753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13129002140915756972665349 2461687901421704432374753)
    ·
      refine ⟨1846265926066278324281065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2461687901421704432374753 1846265926066278324281065)
      ·
        refine ⟨1384699444549708743210799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846265926066278324281065 1384699444549708743210799)
        ·
          refine ⟨2077049166824563114816199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384699444549708743210799 2077049166824563114816199)
          ·
            refine ⟨3115573750236844672224299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077049166824563114816199 3115573750236844672224299)
            ·
              refine ⟨4673360625355267008336449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115573750236844672224299 4673360625355267008336449)
              ·
                refine ⟨3505020469016450256252337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4673360625355267008336449 3505020469016450256252337)
                ·
                  refine ⟨2628765351762337692189253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3505020469016450256252337 2628765351762337692189253)
                  ·
                    refine ⟨492893503455438317285485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2628765351762337692189253 492893503455438317285485)
                    ·
                      refine ⟨184835063795789368982057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 492893503455438317285485 184835063795789368982057)
                      ·
                        rfl

theorem cell23_359965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_359965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_359965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_359965 prefixEnd_359965 := by exact prefixLift 359965
  have htrace : WordTrace (prefixWord ++ tailWord_359965) baseStart_359965 baseEnd_359965 := by
    simpa [prefixWord, tailWord_359965, baseEnd_359965] using wordTrace_append hprefix tailTrace_359965
  have hstable : (prefixWord ++ tailWord_359965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359965).length < 2 ^ (prefixWord ++ tailWord_359965).sum := by decide
  have hdescent : baseEnd_359965 < baseStart_359965 := by decide
  rcases family_descends (prefixWord ++ tailWord_359965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360013 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_360013 : Nat := 118140960795 + 360013 * 2 ^ 59
def prefixEnd_360013 : Nat := 4983230072969 + 3 ^ 40 * 360013 * 2
def baseEnd_360013 : Nat := 184859710867205181181837

theorem tailTrace_360013 : CollatzResearch.WordTrace tailWord_360013 prefixEnd_360013 184859710867205181181837 := by
  unfold tailWord_360013
  simp only [CollatzResearch.WordTrace]
  refine ⟨13130752844741861170412693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8753835229827907446941795 13130752844741861170412693)
  ·
    refine ⟨615504039597274742363095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13130752844741861170412693 615504039597274742363095)
    ·
      refine ⟨923256059395912113544643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615504039597274742363095 923256059395912113544643)
      ·
        refine ⟨1384884089093868170316965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923256059395912113544643 1384884089093868170316965)
        ·
          refine ⟨259665766705100281934431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1384884089093868170316965 259665766705100281934431)
          ·
            refine ⟨389498650057650422901647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259665766705100281934431 389498650057650422901647)
            ·
              refine ⟨584247975086475634352471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389498650057650422901647 584247975086475634352471)
              ·
                refine ⟨876371962629713451528707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584247975086475634352471 876371962629713451528707)
                ·
                  refine ⟨1314557943944570177293061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876371962629713451528707 1314557943944570177293061)
                  ·
                    refine ⟨246479614489606908242449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1314557943944570177293061 246479614489606908242449)
                    ·
                      refine ⟨184859710867205181181837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246479614489606908242449 184859710867205181181837)
                      ·
                        rfl

theorem cell23_360013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_360013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360013 prefixEnd_360013 := by exact prefixLift 360013
  have htrace : WordTrace (prefixWord ++ tailWord_360013) baseStart_360013 baseEnd_360013 := by
    simpa [prefixWord, tailWord_360013, baseEnd_360013] using wordTrace_append hprefix tailTrace_360013
  have hstable : (prefixWord ++ tailWord_360013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360013).length < 2 ^ (prefixWord ++ tailWord_360013).sum := by decide
  have hdescent : baseEnd_360013 < baseStart_360013 := by decide
  rcases family_descends (prefixWord ++ tailWord_360013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360035 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 4]
def baseStart_360035 : Nat := 118140960795 + 360035 * 2 ^ 59
def prefixEnd_360035 : Nat := 4983230072969 + 3 ^ 40 * 360035 * 2
def baseEnd_360035 : Nat := 184871007441604095106735

theorem tailTrace_360035 : CollatzResearch.WordTrace tailWord_360035 prefixEnd_360035 184871007441604095106735 := by
  unfold tailWord_360035
  simp only [CollatzResearch.WordTrace]
  refine ⟨13131555250662158927713559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8754370167108105951809039 13131555250662158927713559)
  ·
    refine ⟨19697332875993238391570339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13131555250662158927713559 19697332875993238391570339)
    ·
      refine ⟨29545999313989857587355509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19697332875993238391570339 29545999313989857587355509)
      ·
        refine ⟨2769937435686549148814579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29545999313989857587355509 2769937435686549148814579)
        ·
          refine ⟨4154906153529823723221869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769937435686549148814579 4154906153529823723221869)
          ·
            refine ⟨1558089807573683896208201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4154906153529823723221869 1558089807573683896208201)
            ·
              refine ⟨1168567355680262922156151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1558089807573683896208201 1168567355680262922156151)
              ·
                refine ⟨1752851033520394383234227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168567355680262922156151 1752851033520394383234227)
                ·
                  refine ⟨2629276550280591574851341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752851033520394383234227 2629276550280591574851341)
                  ·
                    refine ⟨985978706355221840569253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2629276550280591574851341 985978706355221840569253)
                    ·
                      refine ⟨184871007441604095106735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 985978706355221840569253 184871007441604095106735)
                      ·
                        rfl

theorem cell23_360035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_360035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360035 prefixEnd_360035 := by exact prefixLift 360035
  have htrace : WordTrace (prefixWord ++ tailWord_360035) baseStart_360035 baseEnd_360035 := by
    simpa [prefixWord, tailWord_360035, baseEnd_360035] using wordTrace_append hprefix tailTrace_360035
  have hstable : (prefixWord ++ tailWord_360035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360035).length < 2 ^ (prefixWord ++ tailWord_360035).sum := by decide
  have hdescent : baseEnd_360035 < baseStart_360035 := by decide
  rcases family_descends (prefixWord ++ tailWord_360035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360075 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 6]
def baseStart_360075 : Nat := 118140960795 + 360075 * 2 ^ 59
def prefixEnd_360075 : Nat := 4983230072969 + 3 ^ 40 * 360075 * 2
def baseEnd_360075 : Nat := 20543505185309326511839

theorem tailTrace_360075 : CollatzResearch.WordTrace tailWord_360075 prefixEnd_360075 20543505185309326511839 := by
  unfold tailWord_360075
  simp only [CollatzResearch.WordTrace]
  refine ⟨13133014170517245759169679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8755342780344830506113119 13133014170517245759169679)
  ·
    refine ⟨19699521255775868638754519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13133014170517245759169679 19699521255775868638754519)
    ·
      refine ⟨29549281883663802958131779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19699521255775868638754519 29549281883663802958131779)
      ·
        refine ⟨44323922825495704437197669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29549281883663802958131779 44323922825495704437197669)
        ·
          refine ⟨8310735529780444581974563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44323922825495704437197669 8310735529780444581974563)
          ·
            refine ⟨12466103294670666872961845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8310735529780444581974563 12466103294670666872961845)
            ·
              refine ⟨1168697183875375019340173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12466103294670666872961845 1168697183875375019340173)
              ·
                refine ⟨438261443953265632252565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1168697183875375019340173 438261443953265632252565)
                ·
                  refine ⟨20543505185309326511839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 438261443953265632252565 20543505185309326511839)
                  ·
                    rfl

theorem cell23_360075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 6].length) (baseStart_360075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360075 prefixEnd_360075 := by exact prefixLift 360075
  have htrace : WordTrace (prefixWord ++ tailWord_360075) baseStart_360075 baseEnd_360075 := by
    simpa [prefixWord, tailWord_360075, baseEnd_360075] using wordTrace_append hprefix tailTrace_360075
  have hstable : (prefixWord ++ tailWord_360075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360075).length < 2 ^ (prefixWord ++ tailWord_360075).sum := by decide
  have hdescent : baseEnd_360075 < baseStart_360075 := by decide
  rcases family_descends (prefixWord ++ tailWord_360075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360085 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_360085 : Nat := 118140960795 + 360085 * 2 ^ 59
def prefixEnd_360085 : Nat := 4983230072969 + 3 ^ 40 * 360085 * 2
def baseEnd_360085 : Nat := 184896681474328899481505

theorem tailTrace_360085 : CollatzResearch.WordTrace tailWord_360085 prefixEnd_360085 184896681474328899481505 := by
  unfold tailWord_360085
  simp only [CollatzResearch.WordTrace]
  refine ⟨13133378900481017467033709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8755585933654011644689139 13133378900481017467033709)
  ·
    refine ⟨4925017087680381550137641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13133378900481017467033709 4925017087680381550137641)
    ·
      refine ⟨3693762815760286162603231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4925017087680381550137641 3693762815760286162603231)
      ·
        refine ⟨5540644223640429243904847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693762815760286162603231 5540644223640429243904847)
        ·
          refine ⟨8310966335460643865857271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540644223640429243904847 8310966335460643865857271)
          ·
            refine ⟨12466449503190965798785907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8310966335460643865857271 12466449503190965798785907)
            ·
              refine ⟨18699674254786448698178861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12466449503190965798785907 18699674254786448698178861)
              ·
                refine ⟨7012377845544918261817073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18699674254786448698178861 7012377845544918261817073)
                ·
                  refine ⟨5259283384158688696362805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7012377845544918261817073 5259283384158688696362805)
                  ·
                    refine ⟨493057817264877065284013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5259283384158688696362805 493057817264877065284013)
                    ·
                      refine ⟨184896681474328899481505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 493057817264877065284013 184896681474328899481505)
                      ·
                        rfl

theorem cell23_360085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_360085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360085 prefixEnd_360085 := by exact prefixLift 360085
  have htrace : WordTrace (prefixWord ++ tailWord_360085) baseStart_360085 baseEnd_360085 := by
    simpa [prefixWord, tailWord_360085, baseEnd_360085] using wordTrace_append hprefix tailTrace_360085
  have hstable : (prefixWord ++ tailWord_360085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360085).length < 2 ^ (prefixWord ++ tailWord_360085).sum := by decide
  have hdescent : baseEnd_360085 < baseStart_360085 := by decide
  rcases family_descends (prefixWord ++ tailWord_360085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360142 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_360142 : Nat := 118140960795 + 360142 * 2 ^ 59
def prefixEnd_360142 : Nat := 4983230072969 + 3 ^ 40 * 360142 * 2
def baseEnd_360142 : Nat := 184925949871635176468743

theorem tailTrace_360142 : CollatzResearch.WordTrace tailWord_360142 prefixEnd_360142 184925949871635176468743 := by
  unfold tailWord_360142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641932232659314525232335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8756971907516344134572453 1641932232659314525232335)
  ·
    refine ⟨2462898348988971787848503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1641932232659314525232335 2462898348988971787848503)
    ·
      refine ⟨3694347523483457681772755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2462898348988971787848503 3694347523483457681772755)
      ·
        refine ⟨5541521285225186522659133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3694347523483457681772755 5541521285225186522659133)
        ·
          refine ⟨2078070481959444945997175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5541521285225186522659133 2078070481959444945997175)
          ·
            refine ⟨3117105722939167418995763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078070481959444945997175 3117105722939167418995763)
            ·
              refine ⟨4675658584408751128493645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117105722939167418995763 4675658584408751128493645)
              ·
                refine ⟨1753371969153281673185117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4675658584408751128493645 1753371969153281673185117)
                ·
                  refine ⟨657514488432480627444419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1753371969153281673185117 657514488432480627444419)
                  ·
                    refine ⟨986271732648720941166629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 657514488432480627444419 986271732648720941166629)
                    ·
                      refine ⟨184925949871635176468743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 986271732648720941166629 184925949871635176468743)
                      ·
                        rfl

theorem cell23_360142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_360142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360142 prefixEnd_360142 := by exact prefixLift 360142
  have htrace : WordTrace (prefixWord ++ tailWord_360142) baseStart_360142 baseEnd_360142 := by
    simpa [prefixWord, tailWord_360142, baseEnd_360142] using wordTrace_append hprefix tailTrace_360142
  have hstable : (prefixWord ++ tailWord_360142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360142).length < 2 ^ (prefixWord ++ tailWord_360142).sum := by decide
  have hdescent : baseEnd_360142 < baseStart_360142 := by decide
  rcases family_descends (prefixWord ++ tailWord_360142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360146 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_360146 : Nat := 118140960795 + 360146 * 2 ^ 59
def prefixEnd_360146 : Nat := 4983230072969 + 3 ^ 40 * 360146 * 2
def baseEnd_360146 : Nat := 184928003794253160818725

theorem tailTrace_360146 : CollatzResearch.WordTrace tailWord_360146 prefixEnd_360146 184928003794253160818725 := by
  unfold tailWord_360146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3283900938315006221251073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8757069168840016590002861 3283900938315006221251073)
  ·
    refine ⟨2462925703736254665938305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3283900938315006221251073 2462925703736254665938305)
    ·
      refine ⟨1847194277802190999453729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2462925703736254665938305 1847194277802190999453729)
      ·
        refine ⟨1385395708351643249590297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1847194277802190999453729 1385395708351643249590297)
        ·
          refine ⟨1039046781263732437192723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1385395708351643249590297 1039046781263732437192723)
          ·
            refine ⟨1558570171895598655789085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039046781263732437192723 1558570171895598655789085)
            ·
              refine ⟨584463814460849495920907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1558570171895598655789085 584463814460849495920907)
              ·
                refine ⟨876695721691274243881361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584463814460849495920907 876695721691274243881361)
                ·
                  refine ⟨657521791268455682911021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 876695721691274243881361 657521791268455682911021)
                  ·
                    refine ⟨246570671725670881091633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 657521791268455682911021 246570671725670881091633)
                    ·
                      refine ⟨184928003794253160818725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246570671725670881091633 184928003794253160818725)
                      ·
                        rfl

theorem cell23_360146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_360146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360146 prefixEnd_360146 := by exact prefixLift 360146
  have htrace : WordTrace (prefixWord ++ tailWord_360146) baseStart_360146 baseEnd_360146 := by
    simpa [prefixWord, tailWord_360146, baseEnd_360146] using wordTrace_append hprefix tailTrace_360146
  have hstable : (prefixWord ++ tailWord_360146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360146).length < 2 ^ (prefixWord ++ tailWord_360146).sum := by decide
  have hdescent : baseEnd_360146 < baseStart_360146 := by decide
  rcases family_descends (prefixWord ++ tailWord_360146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360152 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 4, 4]
def baseStart_360152 : Nat := 118140960795 + 360152 * 2 ^ 59
def prefixEnd_360152 : Nat := 4983230072969 + 3 ^ 40 * 360152 * 2
def baseEnd_360152 : Nat := 61643694892726712447899

theorem tailTrace_360152 : CollatzResearch.WordTrace tailWord_360152 prefixEnd_360152 61643694892726712447899 := by
  unfold tailWord_360152
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567911295619143954861355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8757215060825525273148473 6567911295619143954861355)
  ·
    refine ⟨9851866943428715932292033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6567911295619143954861355 9851866943428715932292033)
    ·
      refine ⟨7388900207571536949219025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9851866943428715932292033 7388900207571536949219025)
      ·
        refine ⟨5541675155678652711914269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7388900207571536949219025 5541675155678652711914269)
        ·
          refine ⟨2078128183379494766967851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5541675155678652711914269 2078128183379494766967851)
          ·
            refine ⟨3117192275069242150451777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078128183379494766967851 3117192275069242150451777)
            ·
              refine ⟨2337894206301931612838833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3117192275069242150451777 2337894206301931612838833)
              ·
                refine ⟨1753420654726448709629125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337894206301931612838833 1753420654726448709629125)
                ·
                  refine ⟨328766372761209133055461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753420654726448709629125 328766372761209133055461)
                  ·
                    refine ⟨61643694892726712447899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 328766372761209133055461 61643694892726712447899)
                    ·
                      rfl

theorem cell23_360152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_360152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360152 prefixEnd_360152 := by exact prefixLift 360152
  have htrace : WordTrace (prefixWord ++ tailWord_360152) baseStart_360152 baseEnd_360152 := by
    simpa [prefixWord, tailWord_360152, baseEnd_360152] using wordTrace_append hprefix tailTrace_360152
  have hstable : (prefixWord ++ tailWord_360152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360152).length < 2 ^ (prefixWord ++ tailWord_360152).sum := by decide
  have hdescent : baseEnd_360152 < baseStart_360152 := by decide
  rcases family_descends (prefixWord ++ tailWord_360152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360156 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_360156 : Nat := 118140960795 + 360156 * 2 ^ 59
def prefixEnd_360156 : Nat := 4983230072969 + 3 ^ 40 * 360156 * 2
def baseEnd_360156 : Nat := 61644379533599373897893

theorem tailTrace_360156 : CollatzResearch.WordTrace tailWord_360156 prefixEnd_360156 61644379533599373897893 := by
  unfold tailWord_360156
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567984241611898296434161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8757312322149197728578881 6567984241611898296434161)
  ·
    refine ⟨4925988181208923722325621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6567984241611898296434161 4925988181208923722325621)
    ·
      refine ⟨461811391988336598968027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4925988181208923722325621 461811391988336598968027)
      ·
        refine ⟨692717087982504898452041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461811391988336598968027 692717087982504898452041)
        ·
          refine ⟨519537815986878673839031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692717087982504898452041 519537815986878673839031)
          ·
            refine ⟨779306723980318010758547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519537815986878673839031 779306723980318010758547)
            ·
              refine ⟨1168960085970477016137821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779306723980318010758547 1168960085970477016137821)
              ·
                refine ⟨438360032238928881051683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1168960085970477016137821 438360032238928881051683)
                ·
                  refine ⟨657540048358393321577525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438360032238928881051683 657540048358393321577525)
                  ·
                    refine ⟨61644379533599373897893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 657540048358393321577525 61644379533599373897893)
                    ·
                      rfl

theorem cell23_360156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_360156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360156 prefixEnd_360156 := by exact prefixLift 360156
  have htrace : WordTrace (prefixWord ++ tailWord_360156) baseStart_360156 baseEnd_360156 := by
    simpa [prefixWord, tailWord_360156, baseEnd_360156] using wordTrace_append hprefix tailTrace_360156
  have hstable : (prefixWord ++ tailWord_360156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360156).length < 2 ^ (prefixWord ++ tailWord_360156).sum := by decide
  have hdescent : baseEnd_360156 < baseStart_360156 := by decide
  rcases family_descends (prefixWord ++ tailWord_360156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360159 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 5, 2, 2]
def baseStart_360159 : Nat := 118140960795 + 360159 * 2 ^ 59
def prefixEnd_360159 : Nat := 4983230072969 + 3 ^ 40 * 360159 * 2
def baseEnd_360159 : Nat := 184934679042761609956165

theorem tailTrace_360159 : CollatzResearch.WordTrace tailWord_360159 prefixEnd_360159 184934679042761609956165 := by
  unfold tailWord_360159
  simp only [CollatzResearch.WordTrace]
  refine ⟨13136077902212928105227531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8757385268141952070151687 13136077902212928105227531)
  ·
    refine ⟨19704116853319392157841297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13136077902212928105227531 19704116853319392157841297)
    ·
      refine ⟨14778087639989544118380973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19704116853319392157841297 14778087639989544118380973)
      ·
        refine ⟨5541782864996079044392865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14778087639989544118380973 5541782864996079044392865)
        ·
          refine ⟨4156337148747059283294649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5541782864996079044392865 4156337148747059283294649)
          ·
            refine ⟨3117252861560294462470987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4156337148747059283294649 3117252861560294462470987)
            ·
              refine ⟨4675879292340441693706481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117252861560294462470987 4675879292340441693706481)
              ·
                refine ⟨3506909469255331270279861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4675879292340441693706481 3506909469255331270279861)
                ·
                  refine ⟨328772762742687306588737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3506909469255331270279861 328772762742687306588737)
                  ·
                    refine ⟨246579572057015479941553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328772762742687306588737 246579572057015479941553)
                    ·
                      refine ⟨184934679042761609956165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246579572057015479941553 184934679042761609956165)
                      ·
                        rfl

theorem cell23_360159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_360159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360159 prefixEnd_360159 := by exact prefixLift 360159
  have htrace : WordTrace (prefixWord ++ tailWord_360159) baseStart_360159 baseEnd_360159 := by
    simpa [prefixWord, tailWord_360159, baseEnd_360159] using wordTrace_append hprefix tailTrace_360159
  have hstable : (prefixWord ++ tailWord_360159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360159).length < 2 ^ (prefixWord ++ tailWord_360159).sum := by decide
  have hdescent : baseEnd_360159 < baseStart_360159 := by decide
  rcases family_descends (prefixWord ++ tailWord_360159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360165 : List Nat := [1, 3, 1, 4, 1, 1, 12]
def baseStart_360165 : Nat := 118140960795 + 360165 * 2 ^ 59
def prefixEnd_360165 : Nat := 4983230072969 + 3 ^ 40 * 360165 * 2
def baseEnd_360165 : Nat := 2283182221317143042977

theorem tailTrace_360165 : CollatzResearch.WordTrace tailWord_360165 prefixEnd_360165 2283182221317143042977 := by
  unfold tailWord_360165
  simp only [CollatzResearch.WordTrace]
  refine ⟨13136296740191191129945949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8757531160127460753297299 13136296740191191129945949)
  ·
    refine ⟨4926111277571696673729731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13136296740191191129945949 4926111277571696673729731)
    ·
      refine ⟨7389166916357545010594597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4926111277571696673729731 7389166916357545010594597)
      ·
        refine ⟨1385468796817039689486487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7389166916357545010594597 1385468796817039689486487)
        ·
          refine ⟨2078203195225559534229731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385468796817039689486487 2078203195225559534229731)
          ·
            refine ⟨3117304792838339301344597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078203195225559534229731 3117304792838339301344597)
            ·
              refine ⟨2283182221317143042977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 3117304792838339301344597 2283182221317143042977)
              ·
                rfl

theorem cell23_360165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 12].length) (baseStart_360165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360165 prefixEnd_360165 := by exact prefixLift 360165
  have htrace : WordTrace (prefixWord ++ tailWord_360165) baseStart_360165 baseEnd_360165 := by
    simpa [prefixWord, tailWord_360165, baseEnd_360165] using wordTrace_append hprefix tailTrace_360165
  have hstable : (prefixWord ++ tailWord_360165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360165).length < 2 ^ (prefixWord ++ tailWord_360165).sum := by decide
  have hdescent : baseEnd_360165 < baseStart_360165 := by decide
  rcases family_descends (prefixWord ++ tailWord_360165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360195 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 2, 7]
def baseStart_360195 : Nat := 118140960795 + 360195 * 2 ^ 59
def prefixEnd_360195 : Nat := 4983230072969 + 3 ^ 40 * 360195 * 2
def baseEnd_360195 : Nat := 61651054782107823035333

theorem tailTrace_360195 : CollatzResearch.WordTrace tailWord_360195 prefixEnd_360195 61651054782107823035333 := by
  unfold tailWord_360195
  simp only [CollatzResearch.WordTrace]
  refine ⟨13137390930082506253538039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8758260620055004169025359 13137390930082506253538039)
  ·
    refine ⟨19706086395123759380307059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13137390930082506253538039 19706086395123759380307059)
    ·
      refine ⟨29559129592685639070460589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19706086395123759380307059 29559129592685639070460589)
      ·
        refine ⟨11084673597257114651422721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29559129592685639070460589 11084673597257114651422721)
        ·
          refine ⟨8313505197942835988567041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11084673597257114651422721 8313505197942835988567041)
          ·
            refine ⟨6235128898457126991425281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8313505197942835988567041 6235128898457126991425281)
            ·
              refine ⟨4676346673842845243568961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6235128898457126991425281 4676346673842845243568961)
              ·
                refine ⟨3507260005382133932676721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4676346673842845243568961 3507260005382133932676721)
                ·
                  refine ⟨2630445004036600449507541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3507260005382133932676721 2630445004036600449507541)
                  ·
                    refine ⟨61651054782107823035333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2630445004036600449507541 61651054782107823035333)
                    ·
                      rfl

theorem cell23_360195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 7].length) (baseStart_360195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360195 prefixEnd_360195 := by exact prefixLift 360195
  have htrace : WordTrace (prefixWord ++ tailWord_360195) baseStart_360195 baseEnd_360195 := by
    simpa [prefixWord, tailWord_360195, baseEnd_360195] using wordTrace_append hprefix tailTrace_360195
  have hstable : (prefixWord ++ tailWord_360195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360195).length < 2 ^ (prefixWord ++ tailWord_360195).sum := by decide
  have hdescent : baseEnd_360195 < baseStart_360195 := by decide
  rcases family_descends (prefixWord ++ tailWord_360195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360196 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_360196 : Nat := 118140960795 + 360196 * 2 ^ 59
def prefixEnd_360196 : Nat := 4983230072969 + 3 ^ 40 * 360196 * 2
def baseEnd_360196 : Nat := 184953677826977965193495

theorem tailTrace_360196 : CollatzResearch.WordTrace tailWord_360196 prefixEnd_360196 184953677826977965193495 := by
  unfold tailWord_360196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6568713701539441712162221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8758284935385922282882961 6568713701539441712162221)
  ·
    refine ⟨2463267638077290642060833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6568713701539441712162221 2463267638077290642060833)
    ·
      refine ⟨1847450728557967981545625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2463267638077290642060833 1847450728557967981545625)
      ·
        refine ⟨1385588046418475986159219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1847450728557967981545625 1385588046418475986159219)
        ·
          refine ⟨2078382069627713979238829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385588046418475986159219 2078382069627713979238829)
          ·
            refine ⟨779393276110392742214561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2078382069627713979238829 779393276110392742214561)
            ·
              refine ⟨584544957082794556660921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779393276110392742214561 584544957082794556660921)
              ·
                refine ⟨438408717812095917495691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584544957082794556660921 438408717812095917495691)
                ·
                  refine ⟨657613076718143876243537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438408717812095917495691 657613076718143876243537)
                  ·
                    refine ⟨493209807538607907182653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 657613076718143876243537 493209807538607907182653)
                    ·
                      refine ⟨184953677826977965193495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 493209807538607907182653 184953677826977965193495)
                      ·
                        rfl

theorem cell23_360196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_360196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360196 prefixEnd_360196 := by exact prefixLift 360196
  have htrace : WordTrace (prefixWord ++ tailWord_360196) baseStart_360196 baseEnd_360196 := by
    simpa [prefixWord, tailWord_360196, baseEnd_360196] using wordTrace_append hprefix tailTrace_360196
  have hstable : (prefixWord ++ tailWord_360196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360196).length < 2 ^ (prefixWord ++ tailWord_360196).sum := by decide
  have hdescent : baseEnd_360196 < baseStart_360196 := by decide
  rcases family_descends (prefixWord ++ tailWord_360196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360226 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_360226 : Nat := 118140960795 + 360226 * 2 ^ 59
def prefixEnd_360226 : Nat := 4983230072969 + 3 ^ 40 * 360226 * 2
def baseEnd_360226 : Nat := 184969082246612847818357

theorem tailTrace_360226 : CollatzResearch.WordTrace tailWord_360226 prefixEnd_360226 184969082246612847818357 := by
  unfold tailWord_360226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284630398242549636979133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8759014395313465698611021 3284630398242549636979133)
  ·
    refine ⟨1231736399340956113867175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3284630398242549636979133 1231736399340956113867175)
    ·
      refine ⟨1847604599011434170800763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1231736399340956113867175 1847604599011434170800763)
      ·
        refine ⟨2771406898517151256201145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847604599011434170800763 2771406898517151256201145)
        ·
          refine ⟨2078555173887863442150859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2771406898517151256201145 2078555173887863442150859)
          ·
            refine ⟨3117832760831795163226289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078555173887863442150859 3117832760831795163226289)
            ·
              refine ⟨2338374570623846372419717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3117832760831795163226289 2338374570623846372419717)
              ·
                refine ⟨438445231991971194828697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2338374570623846372419717 438445231991971194828697)
                ·
                  refine ⟨328833923993978396121523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438445231991971194828697 328833923993978396121523)
                  ·
                    refine ⟨493250885990967594182285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 328833923993978396121523 493250885990967594182285)
                    ·
                      refine ⟨184969082246612847818357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 493250885990967594182285 184969082246612847818357)
                      ·
                        rfl

theorem cell23_360226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_360226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360226 prefixEnd_360226 := by exact prefixLift 360226
  have htrace : WordTrace (prefixWord ++ tailWord_360226) baseStart_360226 baseEnd_360226 := by
    simpa [prefixWord, tailWord_360226, baseEnd_360226] using wordTrace_append hprefix tailTrace_360226
  have hstable : (prefixWord ++ tailWord_360226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360226).length < 2 ^ (prefixWord ++ tailWord_360226).sum := by decide
  have hdescent : baseEnd_360226 < baseStart_360226 := by decide
  rcases family_descends (prefixWord ++ tailWord_360226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360252 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_360252 : Nat := 118140960795 + 360252 * 2 ^ 59
def prefixEnd_360252 : Nat := 4983230072969 + 3 ^ 40 * 360252 * 2
def baseEnd_360252 : Nat := 184982432743629746093237

theorem tailTrace_360252 : CollatzResearch.WordTrace tailWord_360252 prefixEnd_360252 184982432743629746093237 := by
  unfold tailWord_360252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6569734945438002494181505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8759646593917336658908673 6569734945438002494181505)
  ·
    refine ⟨4927301209078501870636129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6569734945438002494181505 4927301209078501870636129)
    ·
      refine ⟨3695475906808876402977097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4927301209078501870636129 3695475906808876402977097)
      ·
        refine ⟨2771606930106657302232823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3695475906808876402977097 2771606930106657302232823)
        ·
          refine ⟨4157410395159985953349235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771606930106657302232823 4157410395159985953349235)
          ·
            refine ⟨6236115592739978930023853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157410395159985953349235 6236115592739978930023853)
            ·
              refine ⟨2338543347277492098758945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6236115592739978930023853 2338543347277492098758945)
              ·
                refine ⟨1753907510458119074069209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2338543347277492098758945 1753907510458119074069209)
                ·
                  refine ⟨1315430632843589305551907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1753907510458119074069209 1315430632843589305551907)
                  ·
                    refine ⟨1973145949265383958327861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1315430632843589305551907 1973145949265383958327861)
                    ·
                      refine ⟨184982432743629746093237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1973145949265383958327861 184982432743629746093237)
                      ·
                        rfl

theorem cell23_360252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_360252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360252 prefixEnd_360252 := by exact prefixLift 360252
  have htrace : WordTrace (prefixWord ++ tailWord_360252) baseStart_360252 baseEnd_360252 := by
    simpa [prefixWord, tailWord_360252, baseEnd_360252] using wordTrace_append hprefix tailTrace_360252
  have hstable : (prefixWord ++ tailWord_360252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360252).length < 2 ^ (prefixWord ++ tailWord_360252).sum := by decide
  have hdescent : baseEnd_360252 < baseStart_360252 := by decide
  rcases family_descends (prefixWord ++ tailWord_360252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360253 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 1, 3, 2]
def baseStart_360253 : Nat := 118140960795 + 360253 * 2 ^ 59
def prefixEnd_360253 : Nat := 4983230072969 + 3 ^ 40 * 360253 * 2
def baseEnd_360253 : Nat := 184982946224284242180733

theorem tailTrace_360253 : CollatzResearch.WordTrace tailWord_360253 prefixEnd_360253 184982946224284242180733 := by
  unfold tailWord_360253
  simp only [CollatzResearch.WordTrace]
  refine ⟨13139506363872382159149413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8759670909248254772766275 13139506363872382159149413)
  ·
    refine ⟨2463657443226071654840515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13139506363872382159149413 2463657443226071654840515)
    ·
      refine ⟨3695486164839107482260773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2463657443226071654840515 3695486164839107482260773)
      ·
        refine ⟨692903655907332652923895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3695486164839107482260773 692903655907332652923895)
        ·
          refine ⟨1039355483860998979385843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692903655907332652923895 1039355483860998979385843)
          ·
            refine ⟨1559033225791498469078765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039355483860998979385843 1559033225791498469078765)
            ·
              refine ⟨584637459671811925904537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1559033225791498469078765 584637459671811925904537)
              ·
                refine ⟨438478094753858944428403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584637459671811925904537 438478094753858944428403)
                ·
                  refine ⟨657717142130788416642605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438478094753858944428403 657717142130788416642605)
                  ·
                    refine ⟨246643928299045656240977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 657717142130788416642605 246643928299045656240977)
                    ·
                      refine ⟨184982946224284242180733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246643928299045656240977 184982946224284242180733)
                      ·
                        rfl

theorem cell23_360253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_360253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360253 prefixEnd_360253 := by exact prefixLift 360253
  have htrace : WordTrace (prefixWord ++ tailWord_360253) baseStart_360253 baseEnd_360253 := by
    simpa [prefixWord, tailWord_360253, baseEnd_360253] using wordTrace_append hprefix tailTrace_360253
  have hstable : (prefixWord ++ tailWord_360253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360253).length < 2 ^ (prefixWord ++ tailWord_360253).sum := by decide
  have hdescent : baseEnd_360253 < baseStart_360253 := by decide
  rcases family_descends (prefixWord ++ tailWord_360253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360289 : List Nat := [1, 2, 3, 1, 1, 1, 5, 4, 5]
def baseStart_360289 : Nat := 118140960795 + 360289 * 2 ^ 59
def prefixEnd_360289 : Nat := 4983230072969 + 3 ^ 40 * 360289 * 2
def baseEnd_360289 : Nat := 20555714614205122370063

theorem tailTrace_360289 : CollatzResearch.WordTrace tailWord_360289 prefixEnd_360289 20555714614205122370063 := by
  unfold tailWord_360289
  simp only [CollatzResearch.WordTrace]
  refine ⟨13140819391741960307459921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8760546261161306871639947 13140819391741960307459921)
  ·
    refine ⟨9855614543806470230594941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13140819391741960307459921 9855614543806470230594941)
    ·
      refine ⟨3695855453927426336473103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9855614543806470230594941 3695855453927426336473103)
      ·
        refine ⟨5543783180891139504709655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3695855453927426336473103 5543783180891139504709655)
        ·
          refine ⟨8315674771336709257064483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5543783180891139504709655 8315674771336709257064483)
          ·
            refine ⟨12473512157005063885596725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8315674771336709257064483 12473512157005063885596725)
            ·
              refine ⟨1169391764719224739274693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12473512157005063885596725 1169391764719224739274693)
              ·
                refine ⟨219260955884854638614005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1169391764719224739274693 219260955884854638614005)
                ·
                  refine ⟨20555714614205122370063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 219260955884854638614005 20555714614205122370063)
                  ·
                    rfl

theorem cell23_360289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 5].length) (baseStart_360289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360289 prefixEnd_360289 := by exact prefixLift 360289
  have htrace : WordTrace (prefixWord ++ tailWord_360289) baseStart_360289 baseEnd_360289 := by
    simpa [prefixWord, tailWord_360289, baseEnd_360289] using wordTrace_append hprefix tailTrace_360289
  have hstable : (prefixWord ++ tailWord_360289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360289).length < 2 ^ (prefixWord ++ tailWord_360289).sum := by decide
  have hdescent : baseEnd_360289 < baseStart_360289 := by decide
  rcases family_descends (prefixWord ++ tailWord_360289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360334 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2]
def baseStart_360334 : Nat := 118140960795 + 360334 * 2 ^ 59
def prefixEnd_360334 : Nat := 4983230072969 + 3 ^ 40 * 360334 * 2
def baseEnd_360334 : Nat := 185024538157298425267861

theorem tailTrace_360334 : CollatzResearch.WordTrace tailWord_360334 prefixEnd_360334 185024538157298425267861 := by
  unfold tailWord_360334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1642807584572366624106007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8761640451052621995232037 1642807584572366624106007)
  ·
    refine ⟨2464211376858549936159011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1642807584572366624106007 2464211376858549936159011)
    ·
      refine ⟨3696317065287824904238517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2464211376858549936159011 3696317065287824904238517)
      ·
        refine ⟨346529724870733584772361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3696317065287824904238517 346529724870733584772361)
        ·
          refine ⟨259897293653050188579271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346529724870733584772361 259897293653050188579271)
          ·
            refine ⟨389845940479575282868907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259897293653050188579271 389845940479575282868907)
            ·
              refine ⟨584768910719362924303361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389845940479575282868907 584768910719362924303361)
              ·
                refine ⟨438576683039522193227521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584768910719362924303361 438576683039522193227521)
                ·
                  refine ⟨328932512279641644920641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438576683039522193227521 328932512279641644920641)
                  ·
                    refine ⟨246699384209731233690481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328932512279641644920641 246699384209731233690481)
                    ·
                      refine ⟨185024538157298425267861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246699384209731233690481 185024538157298425267861)
                      ·
                        rfl

theorem cell23_360334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_360334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360334 prefixEnd_360334 := by exact prefixLift 360334
  have htrace : WordTrace (prefixWord ++ tailWord_360334) baseStart_360334 baseEnd_360334 := by
    simpa [prefixWord, tailWord_360334, baseEnd_360334] using wordTrace_append hprefix tailTrace_360334
  have hstable : (prefixWord ++ tailWord_360334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360334).length < 2 ^ (prefixWord ++ tailWord_360334).sum := by decide
  have hdescent : baseEnd_360334 < baseStart_360334 := by decide
  rcases family_descends (prefixWord ++ tailWord_360334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360352 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_360352 : Nat := 118140960795 + 360352 * 2 ^ 59
def prefixEnd_360352 : Nat := 4983230072969 + 3 ^ 40 * 360352 * 2
def baseEnd_360352 : Nat := 185033780809079354842777

theorem tailTrace_360352 : CollatzResearch.WordTrace tailWord_360352 prefixEnd_360352 185033780809079354842777 := by
  unfold tailWord_360352
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571558595256861033501655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8762078127009148044668873 6571558595256861033501655)
  ·
    refine ⟨9857337892885291550252483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6571558595256861033501655 9857337892885291550252483)
    ·
      refine ⟨14786006839327937325378725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9857337892885291550252483 14786006839327937325378725)
      ·
        refine ⟨2772376282373988248508511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14786006839327937325378725 2772376282373988248508511)
        ·
          refine ⟨4158564423560982372762767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772376282373988248508511 4158564423560982372762767)
          ·
            refine ⟨6237846635341473559144151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158564423560982372762767 6237846635341473559144151)
            ·
              refine ⟨9356769953012210338716227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6237846635341473559144151 9356769953012210338716227)
              ·
                refine ⟨14035154929518315508074341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9356769953012210338716227 14035154929518315508074341)
                ·
                  refine ⟨2631591549284684157763939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14035154929518315508074341 2631591549284684157763939)
                  ·
                    refine ⟨3947387323927026236645909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2631591549284684157763939 3947387323927026236645909)
                    ·
                      refine ⟨185033780809079354842777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3947387323927026236645909 185033780809079354842777)
                      ·
                        rfl

theorem cell23_360352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_360352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360352 prefixEnd_360352 := by exact prefixLift 360352
  have htrace : WordTrace (prefixWord ++ tailWord_360352) baseStart_360352 baseEnd_360352 := by
    simpa [prefixWord, tailWord_360352, baseEnd_360352] using wordTrace_append hprefix tailTrace_360352
  have hstable : (prefixWord ++ tailWord_360352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360352).length < 2 ^ (prefixWord ++ tailWord_360352).sum := by decide
  have hdescent : baseEnd_360352 < baseStart_360352 := by decide
  rcases family_descends (prefixWord ++ tailWord_360352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360356 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 2, 4, 2]
def baseStart_360356 : Nat := 118140960795 + 360356 * 2 ^ 59
def prefixEnd_360356 : Nat := 4983230072969 + 3 ^ 40 * 360356 * 2
def baseEnd_360356 : Nat := 185035834731697339192759

theorem tailTrace_360356 : CollatzResearch.WordTrace tailWord_360356 prefixEnd_360356 185035834731697339192759 := by
  unfold tailWord_360356
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571631541249615375074461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8762175388332820500099281 6571631541249615375074461)
  ·
    refine ⟨2464361827968605765652923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6571631541249615375074461 2464361827968605765652923)
    ·
      refine ⟨3696542741952908648479385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2464361827968605765652923 3696542741952908648479385)
      ·
        refine ⟨2772407056464681486359539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3696542741952908648479385 2772407056464681486359539)
        ·
          refine ⟨4158610584697022229539309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772407056464681486359539 4158610584697022229539309)
          ·
            refine ⟨1559478969261383336077241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4158610584697022229539309 1559478969261383336077241)
            ·
              refine ⟨1169609226946037502057931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559478969261383336077241 1169609226946037502057931)
              ·
                refine ⟨1754413840419056253086897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169609226946037502057931 1754413840419056253086897)
                ·
                  refine ⟨1315810380314292189815173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1754413840419056253086897 1315810380314292189815173)
                  ·
                    refine ⟨246714446308929785590345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1315810380314292189815173 246714446308929785590345)
                    ·
                      refine ⟨185035834731697339192759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 246714446308929785590345 185035834731697339192759)
                      ·
                        rfl

theorem cell23_360356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_360356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360356 prefixEnd_360356 := by exact prefixLift 360356
  have htrace : WordTrace (prefixWord ++ tailWord_360356) baseStart_360356 baseEnd_360356 := by
    simpa [prefixWord, tailWord_360356, baseEnd_360356] using wordTrace_append hprefix tailTrace_360356
  have hstable : (prefixWord ++ tailWord_360356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360356).length < 2 ^ (prefixWord ++ tailWord_360356).sum := by decide
  have hdescent : baseEnd_360356 < baseStart_360356 := by decide
  rcases family_descends (prefixWord ++ tailWord_360356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360459 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 4]
def baseStart_360459 : Nat := 118140960795 + 360459 * 2 ^ 59
def prefixEnd_360459 : Nat := 4983230072969 + 3 ^ 40 * 360459 * 2
def baseEnd_360459 : Nat := 185088723239110436204785

theorem tailTrace_360459 : CollatzResearch.WordTrace tailWord_360459 prefixEnd_360459 185088723239110436204785 := by
  unfold tailWord_360459
  simp only [CollatzResearch.WordTrace]
  refine ⟨13147019801126079341148431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8764679867417386227432287 13147019801126079341148431)
  ·
    refine ⟨19720529701689119011722647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13147019801126079341148431 19720529701689119011722647)
    ·
      refine ⟨29580794552533678517583971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19720529701689119011722647 29580794552533678517583971)
      ·
        refine ⟨44371191828800517776375957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29580794552533678517583971 44371191828800517776375957)
        ·
          refine ⟨2079899616975024270767623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44371191828800517776375957 2079899616975024270767623)
          ·
            refine ⟨3119849425462536406151435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079899616975024270767623 3119849425462536406151435)
            ·
              refine ⟨4679774138193804609227153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119849425462536406151435 4679774138193804609227153)
              ·
                refine ⟨3509830603645353456920365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4679774138193804609227153 3509830603645353456920365)
                ·
                  refine ⟨1316186476367007546345137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3509830603645353456920365 1316186476367007546345137)
                  ·
                    refine ⟨987139857275255659758853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1316186476367007546345137 987139857275255659758853)
                    ·
                      refine ⟨185088723239110436204785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 987139857275255659758853 185088723239110436204785)
                      ·
                        rfl

theorem cell23_360459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 4].length) (baseStart_360459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_360459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_360459 prefixEnd_360459 := by exact prefixLift 360459
  have htrace : WordTrace (prefixWord ++ tailWord_360459) baseStart_360459 baseEnd_360459 := by
    simpa [prefixWord, tailWord_360459, baseEnd_360459] using wordTrace_append hprefix tailTrace_360459
  have hstable : (prefixWord ++ tailWord_360459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360459).length < 2 ^ (prefixWord ++ tailWord_360459).sum := by decide
  have hdescent : baseEnd_360459 < baseStart_360459 := by decide
  rcases family_descends (prefixWord ++ tailWord_360459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
