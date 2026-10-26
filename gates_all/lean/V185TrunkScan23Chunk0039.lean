import V185TrunkScan23Chunk0038

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_231353 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 2, 3, 2]
def baseStart_231353 : Nat := 118140960795 + 231353 * 2 ^ 59
def prefixEnd_231353 : Nat := 4983230072969 + 3 ^ 40 * 231353 * 2
def baseEnd_231353 : Nat := 118795289859738564023533

theorem tailTrace_231353 : CollatzResearch.WordTrace tailWord_231353 prefixEnd_231353 118795289859738564023533 := by
  unfold tailWord_231353
  simp only [CollatzResearch.WordTrace]
  refine ⟨8438137130855067791802713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5625424753903378527868475 8438137130855067791802713)
  ·
    refine ⟨6328602848141300843852035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8438137130855067791802713 6328602848141300843852035)
    ·
      refine ⟨9492904272211951265778053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6328602848141300843852035 9492904272211951265778053)
      ·
        refine ⟨1779919551039740862333385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9492904272211951265778053 1779919551039740862333385)
        ·
          refine ⟨1334939663279805646750039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1779919551039740862333385 1334939663279805646750039)
          ·
            refine ⟨2002409494919708470125059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334939663279805646750039 2002409494919708470125059)
            ·
              refine ⟨3003614242379562705187589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002409494919708470125059 3003614242379562705187589)
              ·
                refine ⟨563177670446168007222673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3003614242379562705187589 563177670446168007222673)
                ·
                  refine ⟨422383252834626005417005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563177670446168007222673 422383252834626005417005)
                  ·
                    refine ⟨158393719812984752031377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 422383252834626005417005 158393719812984752031377)
                    ·
                      refine ⟨118795289859738564023533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 158393719812984752031377 118795289859738564023533)
                      ·
                        rfl

theorem cell23_231353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_231353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231353 prefixEnd_231353 := by exact prefixLift 231353
  have htrace : WordTrace (prefixWord ++ tailWord_231353) baseStart_231353 baseEnd_231353 := by
    simpa [prefixWord, tailWord_231353, baseEnd_231353] using wordTrace_append hprefix tailTrace_231353
  have hstable : (prefixWord ++ tailWord_231353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231353).length < 2 ^ (prefixWord ++ tailWord_231353).sum := by decide
  have hdescent : baseEnd_231353 < baseStart_231353 := by decide
  rcases family_descends (prefixWord ++ tailWord_231353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231359 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 3, 6]
def baseStart_231359 : Nat := 118140960795 + 231359 * 2 ^ 59
def prefixEnd_231359 : Nat := 4983230072969 + 3 ^ 40 * 231359 * 2
def baseEnd_231359 : Nat := 39599456914555180182835

theorem tailTrace_231359 : CollatzResearch.WordTrace tailWord_231359 prefixEnd_231359 39599456914555180182835 := by
  unfold tailWord_231359
  simp only [CollatzResearch.WordTrace]
  refine ⟨8438355968833330816521131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5625570645888887211014087 8438355968833330816521131)
  ·
    refine ⟨12657533953249996224781697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8438355968833330816521131 12657533953249996224781697)
    ·
      refine ⟨9493150464937497168586273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12657533953249996224781697 9493150464937497168586273)
      ·
        refine ⟨7119862848703122876439705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9493150464937497168586273 7119862848703122876439705)
        ·
          refine ⟨5339897136527342157329779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7119862848703122876439705 5339897136527342157329779)
          ·
            refine ⟨8009845704791013235994669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339897136527342157329779 8009845704791013235994669)
            ·
              refine ⟨3003692139296629963498001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8009845704791013235994669 3003692139296629963498001)
              ·
                refine ⟨2252769104472472472623501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3003692139296629963498001 2252769104472472472623501)
                ·
                  refine ⟨844788414177177177233813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2252769104472472472623501 844788414177177177233813)
                  ·
                    refine ⟨39599456914555180182835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 844788414177177177233813 39599456914555180182835)
                    ·
                      rfl

theorem cell23_231359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_231359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231359 prefixEnd_231359 := by exact prefixLift 231359
  have htrace : WordTrace (prefixWord ++ tailWord_231359) baseStart_231359 baseEnd_231359 := by
    simpa [prefixWord, tailWord_231359, baseEnd_231359] using wordTrace_append hprefix tailTrace_231359
  have hstable : (prefixWord ++ tailWord_231359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231359).length < 2 ^ (prefixWord ++ tailWord_231359).sum := by decide
  have hdescent : baseEnd_231359 < baseStart_231359 := by decide
  rcases family_descends (prefixWord ++ tailWord_231359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231360 : List Nat := [2, 1, 1, 2, 3, 2, 3, 4, 1, 1, 3]
def baseStart_231360 : Nat := 118140960795 + 231360 * 2 ^ 59
def prefixEnd_231360 : Nat := 4983230072969 + 3 ^ 40 * 231360 * 2
def baseEnd_231360 : Nat := 118798884224320036636001

theorem tailTrace_231360 : CollatzResearch.WordTrace tailWord_231360 prefixEnd_231360 118798884224320036636001 := by
  unfold tailWord_231360
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219196220914853993653767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5625594961219805324871689 4219196220914853993653767)
  ·
    refine ⟨6328794331372280990480651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4219196220914853993653767 6328794331372280990480651)
    ·
      refine ⟨9493191497058421485720977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6328794331372280990480651 9493191497058421485720977)
      ·
        refine ⟨7119893622793816114290733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9493191497058421485720977 7119893622793816114290733)
        ·
          refine ⟨2669960108547681042859025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7119893622793816114290733 2669960108547681042859025)
          ·
            refine ⟨2002470081410760782144269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2669960108547681042859025 2002470081410760782144269)
            ·
              refine ⟨750926280529035293304101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2002470081410760782144269 750926280529035293304101)
              ·
                refine ⟨140798677599194117494519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 750926280529035293304101 140798677599194117494519)
                ·
                  refine ⟨211198016398791176241779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140798677599194117494519 211198016398791176241779)
                  ·
                    refine ⟨316797024598186764362669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 211198016398791176241779 316797024598186764362669)
                    ·
                      refine ⟨118798884224320036636001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 316797024598186764362669 118798884224320036636001)
                      ·
                        rfl

theorem cell23_231360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 1, 1, 3].length) (baseStart_231360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231360 prefixEnd_231360 := by exact prefixLift 231360
  have htrace : WordTrace (prefixWord ++ tailWord_231360) baseStart_231360 baseEnd_231360 := by
    simpa [prefixWord, tailWord_231360, baseEnd_231360] using wordTrace_append hprefix tailTrace_231360
  have hstable : (prefixWord ++ tailWord_231360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231360).length < 2 ^ (prefixWord ++ tailWord_231360).sum := by decide
  have hdescent : baseEnd_231360 < baseStart_231360 := by decide
  rcases family_descends (prefixWord ++ tailWord_231360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231396 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_231396 : Nat := 118140960795 + 231396 * 2 ^ 59
def prefixEnd_231396 : Nat := 4983230072969 + 3 ^ 40 * 231396 * 2
def baseEnd_231396 : Nat := 118817369527881895785835

theorem tailTrace_231396 : CollatzResearch.WordTrace tailWord_231396 prefixEnd_231396 118817369527881895785835 := by
  unfold tailWord_231396
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219852734849643067809021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5626470313132857423745361 4219852734849643067809021)
  ·
    refine ⟨1582444775568616150428383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4219852734849643067809021 1582444775568616150428383)
    ·
      refine ⟨2373667163352924225642575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582444775568616150428383 2373667163352924225642575)
      ·
        refine ⟨3560500745029386338463863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373667163352924225642575 3560500745029386338463863)
        ·
          refine ⟨5340751117544079507695795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3560500745029386338463863 5340751117544079507695795)
          ·
            refine ⟨8011126676316119261543693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5340751117544079507695795 8011126676316119261543693)
            ·
              refine ⟨3004172503618544723078885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8011126676316119261543693 3004172503618544723078885)
              ·
                refine ⟨563282344428477135577291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3004172503618544723078885 563282344428477135577291)
                ·
                  refine ⟨844923516642715703365937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563282344428477135577291 844923516642715703365937)
                  ·
                    refine ⟨633692637482036777524453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 844923516642715703365937 633692637482036777524453)
                    ·
                      refine ⟨118817369527881895785835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 633692637482036777524453 118817369527881895785835)
                      ·
                        rfl

theorem cell23_231396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_231396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231396 prefixEnd_231396 := by exact prefixLift 231396
  have htrace : WordTrace (prefixWord ++ tailWord_231396) baseStart_231396 baseEnd_231396 := by
    simpa [prefixWord, tailWord_231396, baseEnd_231396] using wordTrace_append hprefix tailTrace_231396
  have hstable : (prefixWord ++ tailWord_231396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231396).length < 2 ^ (prefixWord ++ tailWord_231396).sum := by decide
  have hdescent : baseEnd_231396 < baseStart_231396 := by decide
  rcases family_descends (prefixWord ++ tailWord_231396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231406 : List Nat := [4, 1, 2, 1, 3, 2, 10]
def baseStart_231406 : Nat := 118140960795 + 231406 * 2 ^ 59
def prefixEnd_231406 : Nat := 4983230072969 + 3 ^ 40 * 231406 * 2
def baseEnd_231406 : Nat := 1466944497955887119269

theorem tailTrace_231406 : CollatzResearch.WordTrace tailWord_231406 prefixEnd_231406 1466944497955887119269 := by
  unfold tailWord_231406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055008774957882230435259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5626713466442038562321381 1055008774957882230435259)
  ·
    refine ⟨1582513162436823345652889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1055008774957882230435259 1582513162436823345652889)
    ·
      refine ⟨1186884871827617509239667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1582513162436823345652889 1186884871827617509239667)
      ·
        refine ⟨1780327307741426263859501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1186884871827617509239667 1780327307741426263859501)
        ·
          refine ⟨667622740403034848947313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1780327307741426263859501 667622740403034848947313)
          ·
            refine ⟨500717055302276136710485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667622740403034848947313 500717055302276136710485)
            ·
              refine ⟨1466944497955887119269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 500717055302276136710485 1466944497955887119269)
              ·
                rfl

theorem cell23_231406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 10].length) (baseStart_231406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231406 prefixEnd_231406 := by exact prefixLift 231406
  have htrace : WordTrace (prefixWord ++ tailWord_231406) baseStart_231406 baseEnd_231406 := by
    simpa [prefixWord, tailWord_231406, baseEnd_231406] using wordTrace_append hprefix tailTrace_231406
  have hstable : (prefixWord ++ tailWord_231406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231406).length < 2 ^ (prefixWord ++ tailWord_231406).sum := by decide
  have hdescent : baseEnd_231406 < baseStart_231406 := by decide
  rcases family_descends (prefixWord ++ tailWord_231406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231416 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 3, 3, 3]
def baseStart_231416 : Nat := 118140960795 + 231416 * 2 ^ 59
def prefixEnd_231416 : Nat := 4983230072969 + 3 ^ 40 * 231416 * 2
def baseEnd_231416 : Nat := 118827639140971817535743

theorem tailTrace_231416 : CollatzResearch.WordTrace tailWord_231416 prefixEnd_231416 118827639140971817535743 := by
  unfold tailWord_231416
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220217464813414775673051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5626956619751219700897401 4220217464813414775673051)
  ·
    refine ⟨6330326197220122163509577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4220217464813414775673051 6330326197220122163509577)
    ·
      refine ⟨4747744647915091622632183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6330326197220122163509577 4747744647915091622632183)
      ·
        refine ⟨7121616971872637433948275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4747744647915091622632183 7121616971872637433948275)
        ·
          refine ⟨10682425457808956150922413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7121616971872637433948275 10682425457808956150922413)
          ·
            refine ⟨4005909546678358556595905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10682425457808956150922413 4005909546678358556595905)
            ·
              refine ⟨3004432160008768917446929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005909546678358556595905 3004432160008768917446929)
              ·
                refine ⟨2253324120006576688085197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3004432160008768917446929 2253324120006576688085197)
                ·
                  refine ⟨844996545002466258031949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2253324120006576688085197 844996545002466258031949)
                  ·
                    refine ⟨316873704375924846761981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844996545002466258031949 316873704375924846761981)
                    ·
                      refine ⟨118827639140971817535743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 316873704375924846761981 118827639140971817535743)
                      ·
                        rfl

theorem cell23_231416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_231416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231416 prefixEnd_231416 := by exact prefixLift 231416
  have htrace : WordTrace (prefixWord ++ tailWord_231416) baseStart_231416 baseEnd_231416 := by
    simpa [prefixWord, tailWord_231416, baseEnd_231416] using wordTrace_append hprefix tailTrace_231416
  have hstable : (prefixWord ++ tailWord_231416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231416).length < 2 ^ (prefixWord ++ tailWord_231416).sum := by decide
  have hdescent : baseEnd_231416 < baseStart_231416 := by decide
  rcases family_descends (prefixWord ++ tailWord_231416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231417 : List Nat := [1, 2, 1, 3, 1, 4, 2, 4, 1, 2, 2]
def baseStart_231417 : Nat := 118140960795 + 231417 * 2 ^ 59
def prefixEnd_231417 : Nat := 4983230072969 + 3 ^ 40 * 231417 * 2
def baseEnd_231417 : Nat := 118828152621626313623239

theorem tailTrace_231417 : CollatzResearch.WordTrace tailWord_231417 prefixEnd_231417 118828152621626313623239 := by
  unfold tailWord_231417
  simp only [CollatzResearch.WordTrace]
  refine ⟨8440471402623206722132505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5626980935082137814755003 8440471402623206722132505)
  ·
    refine ⟨6330353551967405041599379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8440471402623206722132505 6330353551967405041599379)
    ·
      refine ⟨9495530327951107562399069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6330353551967405041599379 9495530327951107562399069)
      ·
        refine ⟨3560823872981665335899651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9495530327951107562399069 3560823872981665335899651)
        ·
          refine ⟨5341235809472498003849477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3560823872981665335899651 5341235809472498003849477)
          ·
            refine ⟨1001481714276093375721777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5341235809472498003849477 1001481714276093375721777)
            ·
              refine ⟨751111285707070031791333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001481714276093375721777 751111285707070031791333)
              ·
                refine ⟨140833366070075630960875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 751111285707070031791333 140833366070075630960875)
                ·
                  refine ⟨211250049105113446441313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140833366070075630960875 211250049105113446441313)
                  ·
                    refine ⟨158437536828835084830985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211250049105113446441313 158437536828835084830985)
                    ·
                      refine ⟨118828152621626313623239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 158437536828835084830985 118828152621626313623239)
                      ·
                        rfl

theorem cell23_231417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_231417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231417 prefixEnd_231417 := by exact prefixLift 231417
  have htrace : WordTrace (prefixWord ++ tailWord_231417) baseStart_231417 baseEnd_231417 := by
    simpa [prefixWord, tailWord_231417, baseEnd_231417] using wordTrace_append hprefix tailTrace_231417
  have hstable : (prefixWord ++ tailWord_231417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231417).length < 2 ^ (prefixWord ++ tailWord_231417).sum := by decide
  have hdescent : baseEnd_231417 < baseStart_231417 := by decide
  rcases family_descends (prefixWord ++ tailWord_231417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231419 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 1, 9]
def baseStart_231419 : Nat := 118140960795 + 231419 * 2 ^ 59
def prefixEnd_231419 : Nat := 4983230072969 + 3 ^ 40 * 231419 * 2
def baseEnd_231419 : Nat := 39609726527645101932743

theorem tailTrace_231419 : CollatzResearch.WordTrace tailWord_231419 prefixEnd_231419 39609726527645101932743 := by
  unfold tailWord_231419
  simp only [CollatzResearch.WordTrace]
  refine ⟨8440544348615961063705311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5627029565743974042470207 8440544348615961063705311)
  ·
    refine ⟨12660816522923941595557967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8440544348615961063705311 12660816522923941595557967)
    ·
      refine ⟨18991224784385912393336951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12660816522923941595557967 18991224784385912393336951)
      ·
        refine ⟨28486837176578868590005427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18991224784385912393336951 28486837176578868590005427)
        ·
          refine ⟨42730255764868302885008141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28486837176578868590005427 42730255764868302885008141)
          ·
            refine ⟨16023845911825613581878053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42730255764868302885008141 16023845911825613581878053)
            ·
              refine ⟨3004471108467302546602135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16023845911825613581878053 3004471108467302546602135)
              ·
                refine ⟨4506706662700953819903203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004471108467302546602135 4506706662700953819903203)
                ·
                  refine ⟨6760059994051430729854805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506706662700953819903203 6760059994051430729854805)
                  ·
                    refine ⟨39609726527645101932743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 6760059994051430729854805 39609726527645101932743)
                    ·
                      rfl

theorem cell23_231419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 9].length) (baseStart_231419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231419 prefixEnd_231419 := by exact prefixLift 231419
  have htrace : WordTrace (prefixWord ++ tailWord_231419) baseStart_231419 baseEnd_231419 := by
    simpa [prefixWord, tailWord_231419, baseEnd_231419] using wordTrace_append hprefix tailTrace_231419
  have hstable : (prefixWord ++ tailWord_231419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231419).length < 2 ^ (prefixWord ++ tailWord_231419).sum := by decide
  have hdescent : baseEnd_231419 < baseStart_231419 := by decide
  rcases family_descends (prefixWord ++ tailWord_231419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231443 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 3, 3, 2]
def baseStart_231443 : Nat := 118140960795 + 231443 * 2 ^ 59
def prefixEnd_231443 : Nat := 4983230072969 + 3 ^ 40 * 231443 * 2
def baseEnd_231443 : Nat := 118841503118643211898119

theorem tailTrace_231443 : CollatzResearch.WordTrace tailWord_231443 prefixEnd_231443 118841503118643211898119 := by
  unfold tailWord_231443
  simp only [CollatzResearch.WordTrace]
  refine ⟨8441419700529013162578983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5627613133686008775052655 8441419700529013162578983)
  ·
    refine ⟨12662129550793519743868475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8441419700529013162578983 12662129550793519743868475)
    ·
      refine ⟨18993194326190279615802713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12662129550793519743868475 18993194326190279615802713)
      ·
        refine ⟨14244895744642709711852035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18993194326190279615802713 14244895744642709711852035)
        ·
          refine ⟨21367343616964064567778053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14244895744642709711852035 21367343616964064567778053)
          ·
            refine ⟨4006376928180762106458385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21367343616964064567778053 4006376928180762106458385)
            ·
              refine ⟨3004782696135571579843789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006376928180762106458385 3004782696135571579843789)
              ·
                refine ⟨1126793511050839342441421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3004782696135571579843789 1126793511050839342441421)
                ·
                  refine ⟨422547566644064753415533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126793511050839342441421 422547566644064753415533)
                  ·
                    refine ⟨158455337491524282530825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 422547566644064753415533 158455337491524282530825)
                    ·
                      refine ⟨118841503118643211898119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 158455337491524282530825 118841503118643211898119)
                      ·
                        rfl

theorem cell23_231443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 3, 2].length) (baseStart_231443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231443 prefixEnd_231443 := by exact prefixLift 231443
  have htrace : WordTrace (prefixWord ++ tailWord_231443) baseStart_231443 baseEnd_231443 := by
    simpa [prefixWord, tailWord_231443, baseEnd_231443] using wordTrace_append hprefix tailTrace_231443
  have hstable : (prefixWord ++ tailWord_231443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231443).length < 2 ^ (prefixWord ++ tailWord_231443).sum := by decide
  have hdescent : baseEnd_231443 < baseStart_231443 := by decide
  rcases family_descends (prefixWord ++ tailWord_231443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231513 : List Nat := [1, 2, 1, 2, 2, 1, 4, 5, 5]
def baseStart_231513 : Nat := 118140960795 + 231513 * 2 ^ 59
def prefixEnd_231513 : Nat := 4983230072969 + 3 ^ 40 * 231513 * 2
def baseEnd_231513 : Nat := 13208605196050882002533

theorem tailTrace_231513 : CollatzResearch.WordTrace tailWord_231513 prefixEnd_231513 13208605196050882002533 := by
  unfold tailWord_231513
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443972810275415117627193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5629315206850276745084795 8443972810275415117627193)
  ·
    refine ⟨6332979607706561338220395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8443972810275415117627193 6332979607706561338220395)
    ·
      refine ⟨9499469411559842007330593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6332979607706561338220395 9499469411559842007330593)
      ·
        refine ⟨7124602058669881505497945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9499469411559842007330593 7124602058669881505497945)
        ·
          refine ⟨5343451544002411129123459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7124602058669881505497945 5343451544002411129123459)
          ·
            refine ⟨8015177316003616693685189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343451544002411129123459 8015177316003616693685189)
            ·
              refine ⟨1502845746750678130065973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8015177316003616693685189 1502845746750678130065973)
              ·
                refine ⟨140891788757876074693685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1502845746750678130065973 140891788757876074693685)
                ·
                  refine ⟨13208605196050882002533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140891788757876074693685 13208605196050882002533)
                  ·
                    rfl

theorem cell23_231513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 5].length) (baseStart_231513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231513 prefixEnd_231513 := by exact prefixLift 231513
  have htrace : WordTrace (prefixWord ++ tailWord_231513) baseStart_231513 baseEnd_231513 := by
    simpa [prefixWord, tailWord_231513, baseEnd_231513] using wordTrace_append hprefix tailTrace_231513
  have hstable : (prefixWord ++ tailWord_231513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231513).length < 2 ^ (prefixWord ++ tailWord_231513).sum := by decide
  have hdescent : baseEnd_231513 < baseStart_231513 := by decide
  rcases family_descends (prefixWord ++ tailWord_231513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231560 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 2, 5]
def baseStart_231560 : Nat := 118140960795 + 231560 * 2 ^ 59
def prefixEnd_231560 : Nat := 4983230072969 + 3 ^ 40 * 231560 * 2
def baseEnd_231560 : Nat := 39633860118406418045027

theorem tailTrace_231560 : CollatzResearch.WordTrace tailWord_231560 prefixEnd_231560 39633860118406418045027 := by
  unfold tailWord_231560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4222843520552571072294067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5630458027403428096392089 4222843520552571072294067)
  ·
    refine ⟨6334265280828856608441101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4222843520552571072294067 6334265280828856608441101)
    ·
      refine ⟨2375349480310821228165413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6334265280828856608441101 2375349480310821228165413)
      ·
        refine ⟨445378027558278980281015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2375349480310821228165413 445378027558278980281015)
        ·
          refine ⟨668067041337418470421523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445378027558278980281015 668067041337418470421523)
          ·
            refine ⟨1002100562006127705632285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668067041337418470421523 1002100562006127705632285)
            ·
              refine ⟨375787710752297889612107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1002100562006127705632285 375787710752297889612107)
              ·
                refine ⟨563681566128446834418161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375787710752297889612107 563681566128446834418161)
                ·
                  refine ⟨422761174596335125813621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563681566128446834418161 422761174596335125813621)
                  ·
                    refine ⟨39633860118406418045027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 422761174596335125813621 39633860118406418045027)
                    ·
                      rfl

theorem cell23_231560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_231560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231560 prefixEnd_231560 := by exact prefixLift 231560
  have htrace : WordTrace (prefixWord ++ tailWord_231560) baseStart_231560 baseEnd_231560 := by
    simpa [prefixWord, tailWord_231560, baseEnd_231560] using wordTrace_append hprefix tailTrace_231560
  have hstable : (prefixWord ++ tailWord_231560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231560).length < 2 ^ (prefixWord ++ tailWord_231560).sum := by decide
  have hdescent : baseEnd_231560 < baseStart_231560 := by decide
  rcases family_descends (prefixWord ++ tailWord_231560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231573 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_231573 : Nat := 118140960795 + 231573 * 2 ^ 59
def prefixEnd_231573 : Nat := 4983230072969 + 3 ^ 40 * 231573 * 2
def baseEnd_231573 : Nat := 39636085201242567757507

theorem tailTrace_231573 : CollatzResearch.WordTrace tailWord_231573 prefixEnd_231573 39636085201242567757507 := by
  unfold tailWord_231573
  simp only [CollatzResearch.WordTrace]
  refine ⟨8446161190058045364811373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5630774126705363576540915 8446161190058045364811373)
  ·
    refine ⟨3167310446271767011804265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8446161190058045364811373 3167310446271767011804265)
    ·
      refine ⟨2375482834703825258853199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3167310446271767011804265 2375482834703825258853199)
      ·
        refine ⟨3563224252055737888279799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375482834703825258853199 3563224252055737888279799)
        ·
          refine ⟨5344836378083606832419699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563224252055737888279799 5344836378083606832419699)
          ·
            refine ⟨8017254567125410248629549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344836378083606832419699 8017254567125410248629549)
            ·
              refine ⟨3006470462672028843236081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8017254567125410248629549 3006470462672028843236081)
              ·
                refine ⟨2254852847004021632427061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006470462672028843236081 2254852847004021632427061)
                ·
                  refine ⟨211392454406627028040037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2254852847004021632427061 211392454406627028040037)
                  ·
                    refine ⟨39636085201242567757507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211392454406627028040037 39636085201242567757507)
                    ·
                      rfl

theorem cell23_231573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_231573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231573 prefixEnd_231573 := by exact prefixLift 231573
  have htrace : WordTrace (prefixWord ++ tailWord_231573) baseStart_231573 baseEnd_231573 := by
    simpa [prefixWord, tailWord_231573, baseEnd_231573] using wordTrace_append hprefix tailTrace_231573
  have hstable : (prefixWord ++ tailWord_231573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231573).length < 2 ^ (prefixWord ++ tailWord_231573).sum := by decide
  have hdescent : baseEnd_231573 < baseStart_231573 := by decide
  rcases family_descends (prefixWord ++ tailWord_231573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231580 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_231580 : Nat := 118140960795 + 231580 * 2 ^ 59
def prefixEnd_231580 : Nat := 4983230072969 + 3 ^ 40 * 231580 * 2
def baseEnd_231580 : Nat := 118911849968309175884989

theorem tailTrace_231580 : CollatzResearch.WordTrace tailWord_231580 prefixEnd_231580 118911849968309175884989 := by
  unfold tailWord_231580
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223208250516342780158097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5630944334021790373544129 4223208250516342780158097)
  ·
    refine ⟨3167406187887257085118573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4223208250516342780158097 3167406187887257085118573)
    ·
      refine ⟨1187777320457721406919465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3167406187887257085118573 1187777320457721406919465)
      ·
        refine ⟨890832990343291055189599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1187777320457721406919465 890832990343291055189599)
        ·
          refine ⟨1336249485514936582784399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890832990343291055189599 1336249485514936582784399)
          ·
            refine ⟨2004374228272404874176599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336249485514936582784399 2004374228272404874176599)
            ·
              refine ⟨3006561342408607311264899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004374228272404874176599 3006561342408607311264899)
              ·
                refine ⟨4509842013612910966897349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006561342408607311264899 4509842013612910966897349)
                ·
                  refine ⟨845595377552420806293253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4509842013612910966897349 845595377552420806293253)
                  ·
                    refine ⟨158549133291078901179985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 845595377552420806293253 158549133291078901179985)
                    ·
                      refine ⟨118911849968309175884989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 158549133291078901179985 118911849968309175884989)
                      ·
                        rfl

theorem cell23_231580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_231580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231580 prefixEnd_231580 := by exact prefixLift 231580
  have htrace : WordTrace (prefixWord ++ tailWord_231580) baseStart_231580 baseEnd_231580 := by
    simpa [prefixWord, tailWord_231580, baseEnd_231580] using wordTrace_append hprefix tailTrace_231580
  have hstable : (prefixWord ++ tailWord_231580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231580).length < 2 ^ (prefixWord ++ tailWord_231580).sum := by decide
  have hdescent : baseEnd_231580 < baseStart_231580 := by decide
  rcases family_descends (prefixWord ++ tailWord_231580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231596 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_231596 : Nat := 118140960795 + 231596 * 2 ^ 59
def prefixEnd_231596 : Nat := 4983230072969 + 3 ^ 40 * 231596 * 2
def baseEnd_231596 : Nat := 118920065658781113284915

theorem tailTrace_231596 : CollatzResearch.WordTrace tailWord_231596 prefixEnd_231596 118920065658781113284915 := by
  unfold tailWord_231596
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223500034487360146449321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5631333379316480195265761 4223500034487360146449321)
  ·
    refine ⟨3167625025865520109836991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4223500034487360146449321 3167625025865520109836991)
    ·
      refine ⟨4751437538798280164755487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3167625025865520109836991 4751437538798280164755487)
      ·
        refine ⟨7127156308197420247133231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4751437538798280164755487 7127156308197420247133231)
        ·
          refine ⟨10690734462296130370699847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127156308197420247133231 10690734462296130370699847)
          ·
            refine ⟨16036101693444195556049771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10690734462296130370699847 16036101693444195556049771)
            ·
              refine ⟨24054152540166293334074657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16036101693444195556049771 24054152540166293334074657)
              ·
                refine ⟨18040614405124720000555993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24054152540166293334074657 18040614405124720000555993)
                ·
                  refine ⟨13530460803843540000416995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18040614405124720000555993 13530460803843540000416995)
                  ·
                    refine ⟨20295691205765310000625493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13530460803843540000416995 20295691205765310000625493)
                    ·
                      refine ⟨118920065658781113284915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 20295691205765310000625493 118920065658781113284915)
                      ·
                        rfl

theorem cell23_231596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_231596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231596 prefixEnd_231596 := by exact prefixLift 231596
  have htrace : WordTrace (prefixWord ++ tailWord_231596) baseStart_231596 baseEnd_231596 := by
    simpa [prefixWord, tailWord_231596, baseEnd_231596] using wordTrace_append hprefix tailTrace_231596
  have hstable : (prefixWord ++ tailWord_231596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231596).length < 2 ^ (prefixWord ++ tailWord_231596).sum := by decide
  have hdescent : baseEnd_231596 < baseStart_231596 := by decide
  rcases family_descends (prefixWord ++ tailWord_231596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231597 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_231597 : Nat := 118140960795 + 231597 * 2 ^ 59
def prefixEnd_231597 : Nat := 4983230072969 + 3 ^ 40 * 231597 * 2
def baseEnd_231597 : Nat := 118920579139435609372411

theorem tailTrace_231597 : CollatzResearch.WordTrace tailWord_231597 prefixEnd_231597 118920579139435609372411 := by
  unfold tailWord_231597
  simp only [CollatzResearch.WordTrace]
  refine ⟨8447036541971097463685045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5631357694647398309123363 8447036541971097463685045)
  ·
    refine ⟨791909675809790387220473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8447036541971097463685045 791909675809790387220473)
    ·
      refine ⟨593932256857342790415355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 791909675809790387220473 593932256857342790415355)
      ·
        refine ⟨890898385286014185623033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593932256857342790415355 890898385286014185623033)
        ·
          refine ⟨668173788964510639217275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890898385286014185623033 668173788964510639217275)
          ·
            refine ⟨1002260683446765958825913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668173788964510639217275 1002260683446765958825913)
            ·
              refine ⟨751695512585074469119435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002260683446765958825913 751695512585074469119435)
              ·
                refine ⟨1127543268877611703679153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751695512585074469119435 1127543268877611703679153)
                ·
                  refine ⟨845657451658208777759365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1127543268877611703679153 845657451658208777759365)
                  ·
                    refine ⟨158560772185914145829881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 845657451658208777759365 158560772185914145829881)
                    ·
                      refine ⟨118920579139435609372411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 158560772185914145829881 118920579139435609372411)
                      ·
                        rfl

theorem cell23_231597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_231597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231597 prefixEnd_231597 := by exact prefixLift 231597
  have htrace : WordTrace (prefixWord ++ tailWord_231597) baseStart_231597 baseEnd_231597 := by
    simpa [prefixWord, tailWord_231597, baseEnd_231597] using wordTrace_append hprefix tailTrace_231597
  have hstable : (prefixWord ++ tailWord_231597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231597).length < 2 ^ (prefixWord ++ tailWord_231597).sum := by decide
  have hdescent : baseEnd_231597 < baseStart_231597 := by decide
  rcases family_descends (prefixWord ++ tailWord_231597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231613 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_231613 : Nat := 118140960795 + 231613 * 2 ^ 59
def prefixEnd_231613 : Nat := 4983230072969 + 3 ^ 40 * 231613 * 2
def baseEnd_231613 : Nat := 118928794829907546772337

theorem tailTrace_231613 : CollatzResearch.WordTrace tailWord_231613 prefixEnd_231613 118928794829907546772337 := by
  unfold tailWord_231613
  simp only [CollatzResearch.WordTrace]
  refine ⟨8447620109913132196267493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5631746739942088130844995 8447620109913132196267493)
  ·
    refine ⟨1583928770608712286800155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8447620109913132196267493 1583928770608712286800155)
    ·
      refine ⟨2375893155913068430200233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583928770608712286800155 2375893155913068430200233)
      ·
        refine ⟨1781919866934801322650175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2375893155913068430200233 1781919866934801322650175)
        ·
          refine ⟨2672879800402201983975263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1781919866934801322650175 2672879800402201983975263)
          ·
            refine ⟨4009319700603302975962895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672879800402201983975263 4009319700603302975962895)
            ·
              refine ⟨6013979550904954463944343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009319700603302975962895 6013979550904954463944343)
              ·
                refine ⟨9020969326357431695916515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6013979550904954463944343 9020969326357431695916515)
                ·
                  refine ⟨13531453989536147543874773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9020969326357431695916515 13531453989536147543874773)
                  ·
                    refine ⟨317143452879753458059565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13531453989536147543874773 317143452879753458059565)
                    ·
                      refine ⟨118928794829907546772337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 317143452879753458059565 118928794829907546772337)
                      ·
                        rfl

theorem cell23_231613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_231613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231613 prefixEnd_231613 := by exact prefixLift 231613
  have htrace : WordTrace (prefixWord ++ tailWord_231613) baseStart_231613 baseEnd_231613 := by
    simpa [prefixWord, tailWord_231613, baseEnd_231613] using wordTrace_append hprefix tailTrace_231613
  have hstable : (prefixWord ++ tailWord_231613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231613).length < 2 ^ (prefixWord ++ tailWord_231613).sum := by decide
  have hdescent : baseEnd_231613 < baseStart_231613 := by decide
  rcases family_descends (prefixWord ++ tailWord_231613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231684 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_231684 : Nat := 118140960795 + 231684 * 2 ^ 59
def prefixEnd_231684 : Nat := 4983230072969 + 3 ^ 40 * 231684 * 2
def baseEnd_231684 : Nat := 39655083985458922994837

theorem tailTrace_231684 : CollatzResearch.WordTrace tailWord_231684 prefixEnd_231684 39655083985458922994837 := by
  unfold tailWord_231684
  simp only [CollatzResearch.WordTrace]
  refine ⟨4225104846327955661051053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5633473128437274214734737 4225104846327955661051053)
  ·
    refine ⟨1584414317372983372894145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4225104846327955661051053 1584414317372983372894145)
    ·
      refine ⟨1188310738029737529670609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1584414317372983372894145 1188310738029737529670609)
      ·
        refine ⟨891233053522303147252957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1188310738029737529670609 891233053522303147252957)
        ·
          refine ⟨334212395070863680219859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 891233053522303147252957 334212395070863680219859)
          ·
            refine ⟨501318592606295520329789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334212395070863680219859 501318592606295520329789)
            ·
              refine ⟨187994472227360820123671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501318592606295520329789 187994472227360820123671)
              ·
                refine ⟨281991708341041230185507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187994472227360820123671 281991708341041230185507)
                ·
                  refine ⟨422987562511561845278261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281991708341041230185507 422987562511561845278261)
                  ·
                    refine ⟨39655083985458922994837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 422987562511561845278261 39655083985458922994837)
                    ·
                      rfl

theorem cell23_231684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_231684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231684 prefixEnd_231684 := by exact prefixLift 231684
  have htrace : WordTrace (prefixWord ++ tailWord_231684) baseStart_231684 baseEnd_231684 := by
    simpa [prefixWord, tailWord_231684, baseEnd_231684] using wordTrace_append hprefix tailTrace_231684
  have hstable : (prefixWord ++ tailWord_231684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231684).length < 2 ^ (prefixWord ++ tailWord_231684).sum := by decide
  have hdescent : baseEnd_231684 < baseStart_231684 := by decide
  rcases family_descends (prefixWord ++ tailWord_231684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231690 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_231690 : Nat := 118140960795 + 231690 * 2 ^ 59
def prefixEnd_231690 : Nat := 4983230072969 + 3 ^ 40 * 231690 * 2
def baseEnd_231690 : Nat := 118968332840303745509483

theorem tailTrace_231690 : CollatzResearch.WordTrace tailWord_231690 prefixEnd_231690 118968332840303745509483 := by
  unfold tailWord_231690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112607132658543586705131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5633619020422782897880349 2112607132658543586705131)
  ·
    refine ⟨3168910698987815380057697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2112607132658543586705131 3168910698987815380057697)
    ·
      refine ⟨2376683024240861535043273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3168910698987815380057697 2376683024240861535043273)
      ·
        refine ⟨1782512268180646151282455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2376683024240861535043273 1782512268180646151282455)
        ·
          refine ⟨2673768402270969226923683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782512268180646151282455 2673768402270969226923683)
          ·
            refine ⟨4010652603406453840385525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673768402270969226923683 4010652603406453840385525)
            ·
              refine ⟨375998681569355047536143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4010652603406453840385525 375998681569355047536143)
              ·
                refine ⟨563998022354032571304215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375998681569355047536143 563998022354032571304215)
                ·
                  refine ⟨845997033531048856956323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563998022354032571304215 845997033531048856956323)
                  ·
                    refine ⟨1268995550296573285434485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 845997033531048856956323 1268995550296573285434485)
                    ·
                      refine ⟨118968332840303745509483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1268995550296573285434485 118968332840303745509483)
                      ·
                        rfl

theorem cell23_231690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_231690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231690 prefixEnd_231690 := by exact prefixLift 231690
  have htrace : WordTrace (prefixWord ++ tailWord_231690) baseStart_231690 baseEnd_231690 := by
    simpa [prefixWord, tailWord_231690, baseEnd_231690] using wordTrace_append hprefix tailTrace_231690
  have hstable : (prefixWord ++ tailWord_231690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231690).length < 2 ^ (prefixWord ++ tailWord_231690).sum := by decide
  have hdescent : baseEnd_231690 < baseStart_231690 := by decide
  rcases family_descends (prefixWord ++ tailWord_231690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231697 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 2, 4]
def baseStart_231697 : Nat := 118140960795 + 231697 * 2 ^ 59
def prefixEnd_231697 : Nat := 4983230072969 + 3 ^ 40 * 231697 * 2
def baseEnd_231697 : Nat := 39657309068295072707317

theorem tailTrace_231697 : CollatzResearch.WordTrace tailWord_231697 prefixEnd_231697 39657309068295072707317 := by
  unfold tailWord_231697
  simp only [CollatzResearch.WordTrace]
  refine ⟨8450683841608814542325345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5633789227739209694883563 8450683841608814542325345)
  ·
    refine ⟨6338012881206610906744009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8450683841608814542325345 6338012881206610906744009)
    ·
      refine ⟨4753509660904958180058007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6338012881206610906744009 4753509660904958180058007)
      ·
        refine ⟨7130264491357437270087011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4753509660904958180058007 7130264491357437270087011)
        ·
          refine ⟨10695396737036155905130517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7130264491357437270087011 10695396737036155905130517)
          ·
            refine ⟨501346722048569808052993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10695396737036155905130517 501346722048569808052993)
            ·
              refine ⟨376010041536427356039745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501346722048569808052993 376010041536427356039745)
              ·
                refine ⟨282007531152320517029809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376010041536427356039745 282007531152320517029809)
                ·
                  refine ⟨211505648364240387772357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282007531152320517029809 211505648364240387772357)
                  ·
                    refine ⟨39657309068295072707317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211505648364240387772357 39657309068295072707317)
                    ·
                      rfl

theorem cell23_231697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_231697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231697 prefixEnd_231697 := by exact prefixLift 231697
  have htrace : WordTrace (prefixWord ++ tailWord_231697) baseStart_231697 baseEnd_231697 := by
    simpa [prefixWord, tailWord_231697, baseEnd_231697] using wordTrace_append hprefix tailTrace_231697
  have hstable : (prefixWord ++ tailWord_231697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231697).length < 2 ^ (prefixWord ++ tailWord_231697).sum := by decide
  have hdescent : baseEnd_231697 < baseStart_231697 := by decide
  rcases family_descends (prefixWord ++ tailWord_231697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231713 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_231713 : Nat := 118140960795 + 231713 * 2 ^ 59
def prefixEnd_231713 : Nat := 4983230072969 + 3 ^ 40 * 231713 * 2
def baseEnd_231713 : Nat := 118980142895357155521877

theorem tailTrace_231713 : CollatzResearch.WordTrace tailWord_231713 prefixEnd_231713 118980142895357155521877 := by
  unfold tailWord_231713
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451267409550849274907793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5634178273033899516605195 8451267409550849274907793)
  ·
    refine ⟨6338450557163136956180845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8451267409550849274907793 6338450557163136956180845)
    ·
      refine ⟨2376918958936176358567817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6338450557163136956180845 2376918958936176358567817)
      ·
        refine ⟨1782689219202132268925863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2376918958936176358567817 1782689219202132268925863)
        ·
          refine ⟨2674033828803198403388795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782689219202132268925863 2674033828803198403388795)
          ·
            refine ⟨4011050743204797605083193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674033828803198403388795 4011050743204797605083193)
            ·
              refine ⟨3008288057403598203812395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011050743204797605083193 3008288057403598203812395)
              ·
                refine ⟨4512432086105397305718593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008288057403598203812395 4512432086105397305718593)
                ·
                  refine ⟨3384324064579047979288945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4512432086105397305718593 3384324064579047979288945)
                  ·
                    refine ⟨2538243048434285984466709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3384324064579047979288945 2538243048434285984466709)
                    ·
                      refine ⟨118980142895357155521877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2538243048434285984466709 118980142895357155521877)
                      ·
                        rfl

theorem cell23_231713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_231713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231713 prefixEnd_231713 := by exact prefixLift 231713
  have htrace : WordTrace (prefixWord ++ tailWord_231713) baseStart_231713 baseEnd_231713 := by
    simpa [prefixWord, tailWord_231713, baseEnd_231713] using wordTrace_append hprefix tailTrace_231713
  have hstable : (prefixWord ++ tailWord_231713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231713).length < 2 ^ (prefixWord ++ tailWord_231713).sum := by decide
  have hdescent : baseEnd_231713 < baseStart_231713 := by decide
  rcases family_descends (prefixWord ++ tailWord_231713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231717 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 4]
def baseStart_231717 : Nat := 118140960795 + 231717 * 2 ^ 59
def prefixEnd_231717 : Nat := 4983230072969 + 3 ^ 40 * 231717 * 2
def baseEnd_231717 : Nat := 118982196817975139871859

theorem tailTrace_231717 : CollatzResearch.WordTrace tailWord_231717 prefixEnd_231717 118982196817975139871859 := by
  unfold tailWord_231717
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451413301536357958053405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5634275534357571972035603 8451413301536357958053405)
  ·
    refine ⟨3169279988076134234270027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8451413301536357958053405 3169279988076134234270027)
    ·
      refine ⟨4753919982114201351405041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3169279988076134234270027 4753919982114201351405041)
      ·
        refine ⟨3565439986585651013553781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4753919982114201351405041 3565439986585651013553781)
        ·
          refine ⟨334259998742404782520667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3565439986585651013553781 334259998742404782520667)
          ·
            refine ⟨501389998113607173781001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334259998742404782520667 501389998113607173781001)
            ·
              refine ⟨376042498585205380335751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501389998113607173781001 376042498585205380335751)
              ·
                refine ⟨564063747877808070503627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376042498585205380335751 564063747877808070503627)
                ·
                  refine ⟨846095621816712105755441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564063747877808070503627 846095621816712105755441)
                  ·
                    refine ⟨634571716362534079316581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 846095621816712105755441 634571716362534079316581)
                    ·
                      refine ⟨118982196817975139871859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 634571716362534079316581 118982196817975139871859)
                      ·
                        rfl

theorem cell23_231717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_231717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231717 prefixEnd_231717 := by exact prefixLift 231717
  have htrace : WordTrace (prefixWord ++ tailWord_231717) baseStart_231717 baseEnd_231717 := by
    simpa [prefixWord, tailWord_231717, baseEnd_231717] using wordTrace_append hprefix tailTrace_231717
  have hstable : (prefixWord ++ tailWord_231717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231717).length < 2 ^ (prefixWord ++ tailWord_231717).sum := by decide
  have hdescent : baseEnd_231717 < baseStart_231717 := by decide
  rcases family_descends (prefixWord ++ tailWord_231717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231737 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 1, 3, 3]
def baseStart_231737 : Nat := 118140960795 + 231737 * 2 ^ 59
def prefixEnd_231737 : Nat := 4983230072969 + 3 ^ 40 * 231737 * 2
def baseEnd_231737 : Nat := 118992466431065061621767

theorem tailTrace_231737 : CollatzResearch.WordTrace tailWord_231737 prefixEnd_231737 118992466431065061621767 := by
  unfold tailWord_231737
  simp only [CollatzResearch.WordTrace]
  refine ⟨8452142761463901373781465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5634761840975934249187643 8452142761463901373781465)
  ·
    refine ⟨6339107071097926030336099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8452142761463901373781465 6339107071097926030336099)
    ·
      refine ⟨9508660606646889045504149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6339107071097926030336099 9508660606646889045504149)
      ·
        refine ⟨445718465936572924008007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9508660606646889045504149 445718465936572924008007)
        ·
          refine ⟨668577698904859386012011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445718465936572924008007 668577698904859386012011)
          ·
            refine ⟨1002866548357289079018017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668577698904859386012011 1002866548357289079018017)
            ·
              refine ⟨752149911267966809263513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002866548357289079018017 752149911267966809263513)
              ·
                refine ⟨564112433450975106947635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752149911267966809263513 564112433450975106947635)
                ·
                  refine ⟨846168650176462660421453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564112433450975106947635 846168650176462660421453)
                  ·
                    refine ⟨317313243816173497658045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846168650176462660421453 317313243816173497658045)
                    ·
                      refine ⟨118992466431065061621767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 317313243816173497658045 118992466431065061621767)
                      ·
                        rfl

theorem cell23_231737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_231737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231737 prefixEnd_231737 := by exact prefixLift 231737
  have htrace : WordTrace (prefixWord ++ tailWord_231737) baseStart_231737 baseEnd_231737 := by
    simpa [prefixWord, tailWord_231737, baseEnd_231737] using wordTrace_append hprefix tailTrace_231737
  have hstable : (prefixWord ++ tailWord_231737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231737).length < 2 ^ (prefixWord ++ tailWord_231737).sum := by decide
  have hdescent : baseEnd_231737 < baseStart_231737 := by decide
  rcases family_descends (prefixWord ++ tailWord_231737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231748 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_231748 : Nat := 118140960795 + 231748 * 2 ^ 59
def prefixEnd_231748 : Nat := 4983230072969 + 3 ^ 40 * 231748 * 2
def baseEnd_231748 : Nat := 39666038239421506194739

theorem tailTrace_231748 : CollatzResearch.WordTrace tailWord_231748 prefixEnd_231748 39666038239421506194739 := by
  unfold tailWord_231748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4226271982212025126215949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5635029309616033501621265 4226271982212025126215949)
  ·
    refine ⟨1584851993329509422330981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4226271982212025126215949 1584851993329509422330981)
    ·
      refine ⟨297159748749283016687059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1584851993329509422330981 297159748749283016687059)
      ·
        refine ⟨445739623123924525030589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297159748749283016687059 445739623123924525030589)
        ·
          refine ⟨167152358671471696886471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445739623123924525030589 167152358671471696886471)
          ·
            refine ⟨250728538007207545329707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167152358671471696886471 250728538007207545329707)
            ·
              refine ⟨376092807010811317994561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250728538007207545329707 376092807010811317994561)
              ·
                refine ⟨282069605258108488495921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376092807010811317994561 282069605258108488495921)
                ·
                  refine ⟨211552203943581366371941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282069605258108488495921 211552203943581366371941)
                  ·
                    refine ⟨39666038239421506194739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211552203943581366371941 39666038239421506194739)
                    ·
                      rfl

theorem cell23_231748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_231748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231748 prefixEnd_231748 := by exact prefixLift 231748
  have htrace : WordTrace (prefixWord ++ tailWord_231748) baseStart_231748 baseEnd_231748 := by
    simpa [prefixWord, tailWord_231748, baseEnd_231748] using wordTrace_append hprefix tailTrace_231748
  have hstable : (prefixWord ++ tailWord_231748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231748).length < 2 ^ (prefixWord ++ tailWord_231748).sum := by decide
  have hdescent : baseEnd_231748 < baseStart_231748 := by decide
  rcases family_descends (prefixWord ++ tailWord_231748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231763 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 5]
def baseStart_231763 : Nat := 118140960795 + 231763 * 2 ^ 59
def prefixEnd_231763 : Nat := 4983230072969 + 3 ^ 40 * 231763 * 2
def baseEnd_231763 : Nat := 119005816928081959896647

theorem tailTrace_231763 : CollatzResearch.WordTrace tailWord_231763 prefixEnd_231763 119005816928081959896647 := by
  unfold tailWord_231763
  simp only [CollatzResearch.WordTrace]
  refine ⟨8453091059369707814227943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5635394039579805209485295 8453091059369707814227943)
  ·
    refine ⟨12679636589054561721341915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8453091059369707814227943 12679636589054561721341915)
    ·
      refine ⟨19019454883581842582012873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12679636589054561721341915 19019454883581842582012873)
      ·
        refine ⟨14264591162686381936509655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19019454883581842582012873 14264591162686381936509655)
        ·
          refine ⟨21396886744029572904764483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14264591162686381936509655 21396886744029572904764483)
          ·
            refine ⟨32095330116044359357146725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21396886744029572904764483 32095330116044359357146725)
            ·
              refine ⟨6017874396758317379465011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32095330116044359357146725 6017874396758317379465011)
              ·
                refine ⟨9026811595137476069197517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017874396758317379465011 9026811595137476069197517)
                ·
                  refine ⟨3385054348176553525949069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9026811595137476069197517 3385054348176553525949069)
                  ·
                    refine ⟨1269395380566207572230901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3385054348176553525949069 1269395380566207572230901)
                    ·
                      refine ⟨119005816928081959896647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1269395380566207572230901 119005816928081959896647)
                      ·
                        rfl

theorem cell23_231763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_231763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231763 prefixEnd_231763 := by exact prefixLift 231763
  have htrace : WordTrace (prefixWord ++ tailWord_231763) baseStart_231763 baseEnd_231763 := by
    simpa [prefixWord, tailWord_231763, baseEnd_231763] using wordTrace_append hprefix tailTrace_231763
  have hstable : (prefixWord ++ tailWord_231763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231763).length < 2 ^ (prefixWord ++ tailWord_231763).sum := by decide
  have hdescent : baseEnd_231763 < baseStart_231763 := by decide
  rcases family_descends (prefixWord ++ tailWord_231763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231780 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_231780 : Nat := 118140960795 + 231780 * 2 ^ 59
def prefixEnd_231780 : Nat := 4983230072969 + 3 ^ 40 * 231780 * 2
def baseEnd_231780 : Nat := 119014546099208393384069

theorem tailTrace_231780 : CollatzResearch.WordTrace tailWord_231780 prefixEnd_231780 119014546099208393384069 := by
  unfold tailWord_231780
  simp only [CollatzResearch.WordTrace]
  refine ⟨4226855550154059858798397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5635807400205413145064529 4226855550154059858798397)
  ·
    refine ⟨1585070831307772447049399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4226855550154059858798397 1585070831307772447049399)
    ·
      refine ⟨2377606246961658670574099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1585070831307772447049399 2377606246961658670574099)
      ·
        refine ⟨3566409370442488005861149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377606246961658670574099 3566409370442488005861149)
        ·
          refine ⟨1337403513915933002197931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3566409370442488005861149 1337403513915933002197931)
          ·
            refine ⟨2006105270873899503296897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337403513915933002197931 2006105270873899503296897)
            ·
              refine ⟨1504578953155424627472673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006105270873899503296897 1504578953155424627472673)
              ·
                refine ⟨1128434214866568470604505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504578953155424627472673 1128434214866568470604505)
                ·
                  refine ⟨846325661149926352953379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128434214866568470604505 846325661149926352953379)
                  ·
                    refine ⟨1269488491724889529430069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 846325661149926352953379 1269488491724889529430069)
                    ·
                      refine ⟨119014546099208393384069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1269488491724889529430069 119014546099208393384069)
                      ·
                        rfl

theorem cell23_231780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_231780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231780 prefixEnd_231780 := by exact prefixLift 231780
  have htrace : WordTrace (prefixWord ++ tailWord_231780) baseStart_231780 baseEnd_231780 := by
    simpa [prefixWord, tailWord_231780, baseEnd_231780] using wordTrace_append hprefix tailTrace_231780
  have hstable : (prefixWord ++ tailWord_231780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231780).length < 2 ^ (prefixWord ++ tailWord_231780).sum := by decide
  have hdescent : baseEnd_231780 < baseStart_231780 := by decide
  rcases family_descends (prefixWord ++ tailWord_231780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231794 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 4, 2, 2]
def baseStart_231794 : Nat := 118140960795 + 231794 * 2 ^ 59
def prefixEnd_231794 : Nat := 4983230072969 + 3 ^ 40 * 231794 * 2
def baseEnd_231794 : Nat := 119021734828371338609005

theorem tailTrace_231794 : CollatzResearch.WordTrace tailWord_231794 prefixEnd_231794 119021734828371338609005 := by
  unfold tailWord_231794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113555430564350027151609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5636147814838266739070957 2113555430564350027151609)
  ·
    refine ⟨1585166572923262520363707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2113555430564350027151609 1585166572923262520363707)
    ·
      refine ⟨2377749859384893780545561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1585166572923262520363707 2377749859384893780545561)
      ·
        refine ⟨1783312394538670335409171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2377749859384893780545561 1783312394538670335409171)
        ·
          refine ⟨2674968591808005503113757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783312394538670335409171 2674968591808005503113757)
          ·
            refine ⟨1003113221928002063667659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2674968591808005503113757 1003113221928002063667659)
            ·
              refine ⟨1504669832892003095501489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003113221928002063667659 1504669832892003095501489)
              ·
                refine ⟨1128502374669002321626117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504669832892003095501489 1128502374669002321626117)
                ·
                  refine ⟨211594195250437935304897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1128502374669002321626117 211594195250437935304897)
                  ·
                    refine ⟨158695646437828451478673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211594195250437935304897 158695646437828451478673)
                    ·
                      refine ⟨119021734828371338609005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 158695646437828451478673 119021734828371338609005)
                      ·
                        rfl

theorem cell23_231794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_231794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231794 prefixEnd_231794 := by exact prefixLift 231794
  have htrace : WordTrace (prefixWord ++ tailWord_231794) baseStart_231794 baseEnd_231794 := by
    simpa [prefixWord, tailWord_231794, baseEnd_231794] using wordTrace_append hprefix tailTrace_231794
  have hstable : (prefixWord ++ tailWord_231794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231794).length < 2 ^ (prefixWord ++ tailWord_231794).sum := by decide
  have hdescent : baseEnd_231794 < baseStart_231794 := by decide
  rcases family_descends (prefixWord ++ tailWord_231794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231797 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_231797 : Nat := 118140960795 + 231797 * 2 ^ 59
def prefixEnd_231797 : Nat := 4983230072969 + 3 ^ 40 * 231797 * 2
def baseEnd_231797 : Nat := 119023275270334826871491

theorem tailTrace_231797 : CollatzResearch.WordTrace tailWord_231797 prefixEnd_231797 119023275270334826871491 := by
  unfold tailWord_231797
  simp only [CollatzResearch.WordTrace]
  refine ⟨8454331141246531620965645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5636220760831021080643763 8454331141246531620965645)
  ·
    refine ⟨3170374177967449357862117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8454331141246531620965645 3170374177967449357862117)
    ·
      refine ⟨594445158368896754599147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3170374177967449357862117 594445158368896754599147)
      ·
        refine ⟨891667737553345131898721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594445158368896754599147 891667737553345131898721)
        ·
          refine ⟨668750803165008848924041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 891667737553345131898721 668750803165008848924041)
          ·
            refine ⟨501563102373756636693031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668750803165008848924041 501563102373756636693031)
            ·
              refine ⟨752344653560634955039547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501563102373756636693031 752344653560634955039547)
              ·
                refine ⟨1128516980340952432559321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752344653560634955039547 1128516980340952432559321)
                ·
                  refine ⟨846387735255714324419491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128516980340952432559321 846387735255714324419491)
                  ·
                    refine ⟨1269581602883571486629237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 846387735255714324419491 1269581602883571486629237)
                    ·
                      refine ⟨119023275270334826871491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1269581602883571486629237 119023275270334826871491)
                      ·
                        rfl

theorem cell23_231797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_231797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231797 prefixEnd_231797 := by exact prefixLift 231797
  have htrace : WordTrace (prefixWord ++ tailWord_231797) baseStart_231797 baseEnd_231797 := by
    simpa [prefixWord, tailWord_231797, baseEnd_231797] using wordTrace_append hprefix tailTrace_231797
  have hstable : (prefixWord ++ tailWord_231797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231797).length < 2 ^ (prefixWord ++ tailWord_231797).sum := by decide
  have hdescent : baseEnd_231797 < baseStart_231797 := by decide
  rcases family_descends (prefixWord ++ tailWord_231797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231817 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 7]
def baseStart_231817 : Nat := 118140960795 + 231817 * 2 ^ 59
def prefixEnd_231817 : Nat := 4983230072969 + 3 ^ 40 * 231817 * 2
def baseEnd_231817 : Nat := 13225949431491638735711

theorem tailTrace_231817 : CollatzResearch.WordTrace tailWord_231817 prefixEnd_231817 13225949431491638735711 := by
  unfold tailWord_231817
  simp only [CollatzResearch.WordTrace]
  refine ⟨8455060601174075036693705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5636707067449383357795803 8455060601174075036693705)
  ·
    refine ⟨6341295450880556277520279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8455060601174075036693705 6341295450880556277520279)
    ·
      refine ⟨9511943176320834416280419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6341295450880556277520279 9511943176320834416280419)
      ·
        refine ⟨14267914764481251624420629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9511943176320834416280419 14267914764481251624420629)
        ·
          refine ⟨668808504585058669894717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14267914764481251624420629 668808504585058669894717)
          ·
            refine ⟨250803189219397001210519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 668808504585058669894717 250803189219397001210519)
            ·
              refine ⟨376204783829095501815779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250803189219397001210519 376204783829095501815779)
              ·
                refine ⟨564307175743643252723669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376204783829095501815779 564307175743643252723669)
                ·
                  refine ⟨13225949431491638735711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 564307175743643252723669 13225949431491638735711)
                  ·
                    rfl

theorem cell23_231817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 7].length) (baseStart_231817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231817 prefixEnd_231817 := by exact prefixLift 231817
  have htrace : WordTrace (prefixWord ++ tailWord_231817) baseStart_231817 baseEnd_231817 := by
    simpa [prefixWord, tailWord_231817, baseEnd_231817] using wordTrace_append hprefix tailTrace_231817
  have hstable : (prefixWord ++ tailWord_231817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231817).length < 2 ^ (prefixWord ++ tailWord_231817).sum := by decide
  have hdescent : baseEnd_231817 < baseStart_231817 := by decide
  rcases family_descends (prefixWord ++ tailWord_231817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231828 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_231828 : Nat := 118140960795 + 231828 * 2 ^ 59
def prefixEnd_231828 : Nat := 4983230072969 + 3 ^ 40 * 231828 * 2
def baseEnd_231828 : Nat := 119039193170624205583849

theorem tailTrace_231828 : CollatzResearch.WordTrace tailWord_231828 prefixEnd_231828 119039193170624205583849 := by
  unfold tailWord_231828
  simp only [CollatzResearch.WordTrace]
  refine ⟨4227730902067111957672069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5636974536089482610229425 4227730902067111957672069)
  ·
    refine ⟨792699544137583492063513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4227730902067111957672069 792699544137583492063513)
    ·
      refine ⟨594524658103187619047635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 792699544137583492063513 594524658103187619047635)
      ·
        refine ⟨891786987154781428571453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594524658103187619047635 891786987154781428571453)
        ·
          refine ⟨334420120183043035714295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 891786987154781428571453 334420120183043035714295)
          ·
            refine ⟨501630180274564553571443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334420120183043035714295 501630180274564553571443)
            ·
              refine ⟨752445270411846830357165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501630180274564553571443 752445270411846830357165)
              ·
                refine ⟨282166976404442561383937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 752445270411846830357165 282166976404442561383937)
                ·
                  refine ⟨211625232303331921037953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282166976404442561383937 211625232303331921037953)
                  ·
                    refine ⟨158718924227498940778465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211625232303331921037953 158718924227498940778465)
                    ·
                      refine ⟨119039193170624205583849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 158718924227498940778465 119039193170624205583849)
                      ·
                        rfl

theorem cell23_231828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_231828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231828 prefixEnd_231828 := by exact prefixLift 231828
  have htrace : WordTrace (prefixWord ++ tailWord_231828) baseStart_231828 baseEnd_231828 := by
    simpa [prefixWord, tailWord_231828, baseEnd_231828] using wordTrace_append hprefix tailTrace_231828
  have hstable : (prefixWord ++ tailWord_231828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231828).length < 2 ^ (prefixWord ++ tailWord_231828).sum := by decide
  have hdescent : baseEnd_231828 < baseStart_231828 := by decide
  rcases family_descends (prefixWord ++ tailWord_231828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231847 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 2, 5]
def baseStart_231847 : Nat := 118140960795 + 231847 * 2 ^ 59
def prefixEnd_231847 : Nat := 4983230072969 + 3 ^ 40 * 231847 * 2
def baseEnd_231847 : Nat := 39682983101019877082087

theorem tailTrace_231847 : CollatzResearch.WordTrace tailWord_231847 prefixEnd_231847 39682983101019877082087 := by
  unfold tailWord_231847
  simp only [CollatzResearch.WordTrace]
  refine ⟨8456154791065390160285795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5637436527376926773523863 8456154791065390160285795)
  ·
    refine ⟨12684232186598085240428693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8456154791065390160285795 12684232186598085240428693)
    ·
      refine ⟨594573383746785245645095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12684232186598085240428693 594573383746785245645095)
      ·
        refine ⟨891860075620177868467643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594573383746785245645095 891860075620177868467643)
        ·
          refine ⟨1337790113430266802701465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891860075620177868467643 1337790113430266802701465)
          ·
            refine ⟨1003342585072700102026099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1337790113430266802701465 1003342585072700102026099)
            ·
              refine ⟨1505013877609050153039149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003342585072700102026099 1505013877609050153039149)
              ·
                refine ⟨564380204103393807389681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1505013877609050153039149 564380204103393807389681)
                ·
                  refine ⟨423285153077545355542261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564380204103393807389681 423285153077545355542261)
                  ·
                    refine ⟨39682983101019877082087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 423285153077545355542261 39682983101019877082087)
                    ·
                      rfl

theorem cell23_231847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_231847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231847 prefixEnd_231847 := by exact prefixLift 231847
  have htrace : WordTrace (prefixWord ++ tailWord_231847) baseStart_231847 baseEnd_231847 := by
    simpa [prefixWord, tailWord_231847, baseEnd_231847] using wordTrace_append hprefix tailTrace_231847
  have hstable : (prefixWord ++ tailWord_231847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231847).length < 2 ^ (prefixWord ++ tailWord_231847).sum := by decide
  have hdescent : baseEnd_231847 < baseStart_231847 := by decide
  rcases family_descends (prefixWord ++ tailWord_231847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231911 : List Nat := [1, 1, 5, 2, 1, 1, 4, 3, 1, 4]
def baseStart_231911 : Nat := 118140960795 + 231911 * 2 ^ 59
def prefixEnd_231911 : Nat := 4983230072969 + 3 ^ 40 * 231911 * 2
def baseEnd_231911 : Nat := 39693937354982460281989

theorem tailTrace_231911 : CollatzResearch.WordTrace tailWord_231911 prefixEnd_231911 39693937354982460281989 := by
  unfold tailWord_231911
  simp only [CollatzResearch.WordTrace]
  refine ⟨8458489062833529090615587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5638992708555686060410391 8458489062833529090615587)
  ·
    refine ⟨12687733594250293635923381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8458489062833529090615587 12687733594250293635923381)
    ·
      refine ⟨1189475024460965028367817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12687733594250293635923381 1189475024460965028367817)
      ·
        refine ⟨892106268345723771275863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1189475024460965028367817 892106268345723771275863)
        ·
          refine ⟨1338159402518585656913795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892106268345723771275863 1338159402518585656913795)
          ·
            refine ⟨2007239103777878485370693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338159402518585656913795 2007239103777878485370693)
            ·
              refine ⟨376357331958352216007005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2007239103777878485370693 376357331958352216007005)
              ·
                refine ⟨141133999484382081002627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376357331958352216007005 141133999484382081002627)
                ·
                  refine ⟨211700999226573121503941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141133999484382081002627 211700999226573121503941)
                  ·
                    refine ⟨39693937354982460281989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211700999226573121503941 39693937354982460281989)
                    ·
                      rfl

theorem cell23_231911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_231911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231911 prefixEnd_231911 := by exact prefixLift 231911
  have htrace : WordTrace (prefixWord ++ tailWord_231911) baseStart_231911 baseEnd_231911 := by
    simpa [prefixWord, tailWord_231911, baseEnd_231911] using wordTrace_append hprefix tailTrace_231911
  have hstable : (prefixWord ++ tailWord_231911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231911).length < 2 ^ (prefixWord ++ tailWord_231911).sum := by decide
  have hdescent : baseEnd_231911 < baseStart_231911 := by decide
  rcases family_descends (prefixWord ++ tailWord_231911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231930 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_231930 : Nat := 118140960795 + 231930 * 2 ^ 59
def prefixEnd_231930 : Nat := 4983230072969 + 3 ^ 40 * 231930 * 2
def baseEnd_231930 : Nat := 119091568197382806508379

theorem tailTrace_231930 : CollatzResearch.WordTrace tailWord_231930 prefixEnd_231930 119091568197382806508379 := by
  unfold tailWord_231930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2114795512441173833889311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5639454699843130223704829 2114795512441173833889311)
  ·
    refine ⟨3172193268661760750833967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2114795512441173833889311 3172193268661760750833967)
    ·
      refine ⟨4758289902992641126250951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3172193268661760750833967 4758289902992641126250951)
      ·
        refine ⟨7137434854488961689376427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758289902992641126250951 7137434854488961689376427)
        ·
          refine ⟨10706152281733442534064641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7137434854488961689376427 10706152281733442534064641)
          ·
            refine ⟨8029614211300081900548481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10706152281733442534064641 8029614211300081900548481)
            ·
              refine ⟨6022210658475061425411361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8029614211300081900548481 6022210658475061425411361)
              ·
                refine ⟨4516657993856296069058521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6022210658475061425411361 4516657993856296069058521)
                ·
                  refine ⟨3387493495392222051793891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4516657993856296069058521 3387493495392222051793891)
                  ·
                    refine ⟨5081240243088333077690837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3387493495392222051793891 5081240243088333077690837)
                    ·
                      refine ⟨119091568197382806508379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5081240243088333077690837 119091568197382806508379)
                      ·
                        rfl

theorem cell23_231930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_231930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231930 prefixEnd_231930 := by exact prefixLift 231930
  have htrace : WordTrace (prefixWord ++ tailWord_231930) baseStart_231930 baseEnd_231930 := by
    simpa [prefixWord, tailWord_231930, baseEnd_231930] using wordTrace_append hprefix tailTrace_231930
  have hstable : (prefixWord ++ tailWord_231930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231930).length < 2 ^ (prefixWord ++ tailWord_231930).sum := by decide
  have hdescent : baseEnd_231930 < baseStart_231930 := by decide
  rcases family_descends (prefixWord ++ tailWord_231930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231997 : List Nat := [1, 4, 1, 3, 2, 1, 1, 10]
def baseStart_231997 : Nat := 118140960795 + 231997 * 2 ^ 59
def prefixEnd_231997 : Nat := 4983230072969 + 3 ^ 40 * 231997 * 2
def baseEnd_231997 : Nat := 4412073014860520161873

theorem tailTrace_231997 : CollatzResearch.WordTrace tailWord_231997 prefixEnd_231997 4412073014860520161873 := by
  unfold tailWord_231997
  simp only [CollatzResearch.WordTrace]
  refine ⟨8461625740521965778246245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5641083827014643852164163 8461625740521965778246245)
  ·
    refine ⟨1586554826347868583421171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8461625740521965778246245 1586554826347868583421171)
    ·
      refine ⟨2379832239521802875131757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586554826347868583421171 2379832239521802875131757)
      ·
        refine ⟨892437089820676078174409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2379832239521802875131757 892437089820676078174409)
        ·
          refine ⟨669327817365507058630807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 892437089820676078174409 669327817365507058630807)
          ·
            refine ⟨1003991726048260587946211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669327817365507058630807 1003991726048260587946211)
            ·
              refine ⟨1505987589072390881919317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003991726048260587946211 1505987589072390881919317)
              ·
                refine ⟨4412073014860520161873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1505987589072390881919317 4412073014860520161873)
                ·
                  rfl

theorem cell23_231997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 10].length) (baseStart_231997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_231997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_231997 prefixEnd_231997 := by exact prefixLift 231997
  have htrace : WordTrace (prefixWord ++ tailWord_231997) baseStart_231997 baseEnd_231997 := by
    simpa [prefixWord, tailWord_231997, baseEnd_231997] using wordTrace_append hprefix tailTrace_231997
  have hstable : (prefixWord ++ tailWord_231997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231997).length < 2 ^ (prefixWord ++ tailWord_231997).sum := by decide
  have hdescent : baseEnd_231997 < baseStart_231997 := by decide
  rcases family_descends (prefixWord ++ tailWord_231997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232001 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 2, 4]
def baseStart_232001 : Nat := 118140960795 + 232001 * 2 ^ 59
def prefixEnd_232001 : Nat := 4983230072969 + 3 ^ 40 * 232001 * 2
def baseEnd_232001 : Nat := 39709341774617342906851

theorem tailTrace_232001 : CollatzResearch.WordTrace tailWord_232001 prefixEnd_232001 39709341774617342906851 := by
  unfold tailWord_232001
  simp only [CollatzResearch.WordTrace]
  refine ⟨8461771632507474461391857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5641181088338316307594571 8461771632507474461391857)
  ·
    refine ⟨6346328724380605846043893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8461771632507474461391857 6346328724380605846043893)
    ·
      refine ⟨594968317910681798066615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6346328724380605846043893 594968317910681798066615)
      ·
        refine ⟨892452476866022697099923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594968317910681798066615 892452476866022697099923)
        ·
          refine ⟨1338678715299034045649885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892452476866022697099923 1338678715299034045649885)
          ·
            refine ⟨502004518237137767118707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1338678715299034045649885 502004518237137767118707)
            ·
              refine ⟨753006777355706650678061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502004518237137767118707 753006777355706650678061)
              ·
                refine ⟨282377541508389994004273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 753006777355706650678061 282377541508389994004273)
                ·
                  refine ⟨211783156131292495503205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282377541508389994004273 211783156131292495503205)
                  ·
                    refine ⟨39709341774617342906851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211783156131292495503205 39709341774617342906851)
                    ·
                      rfl

theorem cell23_232001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_232001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232001 prefixEnd_232001 := by exact prefixLift 232001
  have htrace : WordTrace (prefixWord ++ tailWord_232001) baseStart_232001 baseEnd_232001 := by
    simpa [prefixWord, tailWord_232001, baseEnd_232001] using wordTrace_append hprefix tailTrace_232001
  have hstable : (prefixWord ++ tailWord_232001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232001).length < 2 ^ (prefixWord ++ tailWord_232001).sum := by decide
  have hdescent : baseEnd_232001 < baseStart_232001 := by decide
  rcases family_descends (prefixWord ++ tailWord_232001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232024 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 6, 1, 3]
def baseStart_232024 : Nat := 118140960795 + 232024 * 2 ^ 59
def prefixEnd_232024 : Nat := 4983230072969 + 3 ^ 40 * 232024 * 2
def baseEnd_232024 : Nat := 119139835378905438732947

theorem tailTrace_232024 : CollatzResearch.WordTrace tailWord_232024 prefixEnd_232024 119139835378905438732947 := by
  unfold tailWord_232024
  simp only [CollatzResearch.WordTrace]
  refine ⟨4231305255712074694739563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5641740340949432926319417 4231305255712074694739563)
  ·
    refine ⟨6346957883568112042109345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4231305255712074694739563 6346957883568112042109345)
    ·
      refine ⟨4760218412676084031582009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6346957883568112042109345 4760218412676084031582009)
      ·
        refine ⟨3570163809507063023686507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4760218412676084031582009 3570163809507063023686507)
        ·
          refine ⟨5355245714260594535529761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3570163809507063023686507 5355245714260594535529761)
          ·
            refine ⟨4016434285695445901647321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5355245714260594535529761 4016434285695445901647321)
            ·
              refine ⟨3012325714271584426235491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4016434285695445901647321 3012325714271584426235491)
              ·
                refine ⟨4518488571407376639353237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012325714271584426235491 4518488571407376639353237)
                ·
                  refine ⟨211804151784720779969683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4518488571407376639353237 211804151784720779969683)
                  ·
                    refine ⟨317706227677081169954525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 211804151784720779969683 317706227677081169954525)
                    ·
                      refine ⟨119139835378905438732947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 317706227677081169954525 119139835378905438732947)
                      ·
                        rfl

theorem cell23_232024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_232024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232024 prefixEnd_232024 := by exact prefixLift 232024
  have htrace : WordTrace (prefixWord ++ tailWord_232024) baseStart_232024 baseEnd_232024 := by
    simpa [prefixWord, tailWord_232024, baseEnd_232024] using wordTrace_append hprefix tailTrace_232024
  have hstable : (prefixWord ++ tailWord_232024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232024).length < 2 ^ (prefixWord ++ tailWord_232024).sum := by decide
  have hdescent : baseEnd_232024 < baseStart_232024 := by decide
  rcases family_descends (prefixWord ++ tailWord_232024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232028 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_232028 : Nat := 118140960795 + 232028 * 2 ^ 59
def prefixEnd_232028 : Nat := 4983230072969 + 3 ^ 40 * 232028 * 2
def baseEnd_232028 : Nat := 119141889301523423082929

theorem tailTrace_232028 : CollatzResearch.WordTrace tailWord_232028 prefixEnd_232028 119141889301523423082929 := by
  unfold tailWord_232028
  simp only [CollatzResearch.WordTrace]
  refine ⟨4231378201704829036312369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5641837602273105381749825 4231378201704829036312369)
  ·
    refine ⟨3173533651278621777234277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4231378201704829036312369 3173533651278621777234277)
    ·
      refine ⟨595037559614741583231427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3173533651278621777234277 595037559614741583231427)
      ·
        refine ⟨892556339422112374847141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595037559614741583231427 892556339422112374847141)
        ·
          refine ⟨167354313641646070283839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 892556339422112374847141 167354313641646070283839)
          ·
            refine ⟨251031470462469105425759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167354313641646070283839 251031470462469105425759)
            ·
              refine ⟨376547205693703658138639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251031470462469105425759 376547205693703658138639)
              ·
                refine ⟨564820808540555487207959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376547205693703658138639 564820808540555487207959)
                ·
                  refine ⟨847231212810833230811939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564820808540555487207959 847231212810833230811939)
                  ·
                    refine ⟨1270846819216249846217909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 847231212810833230811939 1270846819216249846217909)
                    ·
                      refine ⟨119141889301523423082929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1270846819216249846217909 119141889301523423082929)
                      ·
                        rfl

theorem cell23_232028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_232028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232028 prefixEnd_232028 := by exact prefixLift 232028
  have htrace : WordTrace (prefixWord ++ tailWord_232028) baseStart_232028 baseEnd_232028 := by
    simpa [prefixWord, tailWord_232028, baseEnd_232028] using wordTrace_append hprefix tailTrace_232028
  have hstable : (prefixWord ++ tailWord_232028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232028).length < 2 ^ (prefixWord ++ tailWord_232028).sum := by decide
  have hdescent : baseEnd_232028 < baseStart_232028 := by decide
  rcases family_descends (prefixWord ++ tailWord_232028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232047 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_232047 : Nat := 118140960795 + 232047 * 2 ^ 59
def prefixEnd_232047 : Nat := 4983230072969 + 3 ^ 40 * 232047 * 2
def baseEnd_232047 : Nat := 119151645433958848745341

theorem tailTrace_232047 : CollatzResearch.WordTrace tailWord_232047 prefixEnd_232047 119151645433958848745341 := by
  unfold tailWord_232047
  simp only [CollatzResearch.WordTrace]
  refine ⟨8463449390340824317566395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5642299593560549545044263 8463449390340824317566395)
  ·
    refine ⟨12695174085511236476349593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8463449390340824317566395 12695174085511236476349593)
    ·
      refine ⟨9521380564133427357262195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12695174085511236476349593 9521380564133427357262195)
      ·
        refine ⟨14282070846200141035893293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9521380564133427357262195 14282070846200141035893293)
        ·
          refine ⟨5355776567325052888459985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14282070846200141035893293 5355776567325052888459985)
          ·
            refine ⟨4016832425493789666344989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5355776567325052888459985 4016832425493789666344989)
            ·
              refine ⟨1506312159560171124879371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4016832425493789666344989 1506312159560171124879371)
              ·
                refine ⟨2259468239340256687319057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506312159560171124879371 2259468239340256687319057)
                ·
                  refine ⟨1694601179505192515489293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2259468239340256687319057 1694601179505192515489293)
                  ·
                    refine ⟨635475442314447193308485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1694601179505192515489293 635475442314447193308485)
                    ·
                      refine ⟨119151645433958848745341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 635475442314447193308485 119151645433958848745341)
                      ·
                        rfl

theorem cell23_232047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_232047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232047 prefixEnd_232047 := by exact prefixLift 232047
  have htrace : WordTrace (prefixWord ++ tailWord_232047) baseStart_232047 baseEnd_232047 := by
    simpa [prefixWord, tailWord_232047, baseEnd_232047] using wordTrace_append hprefix tailTrace_232047
  have hstable : (prefixWord ++ tailWord_232047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232047).length < 2 ^ (prefixWord ++ tailWord_232047).sum := by decide
  have hdescent : baseEnd_232047 < baseStart_232047 := by decide
  rcases family_descends (prefixWord ++ tailWord_232047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232057 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 1, 8]
def baseStart_232057 : Nat := 118140960795 + 232057 * 2 ^ 59
def prefixEnd_232057 : Nat := 4983230072969 + 3 ^ 40 * 232057 * 2
def baseEnd_232057 : Nat := 39718926746834603206765

theorem tailTrace_232057 : CollatzResearch.WordTrace tailWord_232057 prefixEnd_232057 39718926746834603206765 := by
  unfold tailWord_232057
  simp only [CollatzResearch.WordTrace]
  refine ⟨8463814120304596025430425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5642542746869730683620283 8463814120304596025430425)
  ·
    refine ⟨6347860590228447019072819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8463814120304596025430425 6347860590228447019072819)
    ·
      refine ⟨9521790885342670528609229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6347860590228447019072819 9521790885342670528609229)
      ·
        refine ⟨3570671582003501448228461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9521790885342670528609229 3570671582003501448228461)
        ·
          refine ⟨1339001843251313043085673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3570671582003501448228461 1339001843251313043085673)
          ·
            refine ⟨1004251382438484782314255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1339001843251313043085673 1004251382438484782314255)
            ·
              refine ⟨1506377073657727173471383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004251382438484782314255 1506377073657727173471383)
              ·
                refine ⟨2259565610486590760207075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506377073657727173471383 2259565610486590760207075)
                ·
                  refine ⟨3389348415729886140310613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259565610486590760207075 3389348415729886140310613)
                  ·
                    refine ⟨39718926746834603206765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3389348415729886140310613 39718926746834603206765)
                    ·
                      rfl

theorem cell23_232057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_232057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232057 prefixEnd_232057 := by exact prefixLift 232057
  have htrace : WordTrace (prefixWord ++ tailWord_232057) baseStart_232057 baseEnd_232057 := by
    simpa [prefixWord, tailWord_232057, baseEnd_232057] using wordTrace_append hprefix tailTrace_232057
  have hstable : (prefixWord ++ tailWord_232057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232057).length < 2 ^ (prefixWord ++ tailWord_232057).sum := by decide
  have hdescent : baseEnd_232057 < baseStart_232057 := by decide
  rcases family_descends (prefixWord ++ tailWord_232057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232067 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 5]
def baseStart_232067 : Nat := 118140960795 + 232067 * 2 ^ 59
def prefixEnd_232067 : Nat := 4983230072969 + 3 ^ 40 * 232067 * 2
def baseEnd_232067 : Nat := 119161915047048770495249

theorem tailTrace_232067 : CollatzResearch.WordTrace tailWord_232067 prefixEnd_232067 119161915047048770495249 := by
  unfold tailWord_232067
  simp only [CollatzResearch.WordTrace]
  refine ⟨8464178850268367733294455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5642785900178911822196303 8464178850268367733294455)
  ·
    refine ⟨12696268275402551599941683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8464178850268367733294455 12696268275402551599941683)
    ·
      refine ⟨19044402413103827399912525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12696268275402551599941683 19044402413103827399912525)
      ·
        refine ⟨7141650904913935274967197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19044402413103827399912525 7141650904913935274967197)
        ·
          refine ⟨2678119089342725728112699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7141650904913935274967197 2678119089342725728112699)
          ·
            refine ⟨4017178634014088592169049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678119089342725728112699 4017178634014088592169049)
            ·
              refine ⟨3012883975510566444126787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4017178634014088592169049 3012883975510566444126787)
              ·
                refine ⟨4519325963265849666190181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012883975510566444126787 4519325963265849666190181)
                ·
                  refine ⟨847373618112346812410659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4519325963265849666190181 847373618112346812410659)
                  ·
                    refine ⟨1271060427168520218615989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 847373618112346812410659 1271060427168520218615989)
                    ·
                      refine ⟨119161915047048770495249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1271060427168520218615989 119161915047048770495249)
                      ·
                        rfl

theorem cell23_232067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_232067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232067 prefixEnd_232067 := by exact prefixLift 232067
  have htrace : WordTrace (prefixWord ++ tailWord_232067) baseStart_232067 baseEnd_232067 := by
    simpa [prefixWord, tailWord_232067, baseEnd_232067] using wordTrace_append hprefix tailTrace_232067
  have hstable : (prefixWord ++ tailWord_232067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232067).length < 2 ^ (prefixWord ++ tailWord_232067).sum := by decide
  have hdescent : baseEnd_232067 < baseStart_232067 := by decide
  rcases family_descends (prefixWord ++ tailWord_232067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232087 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 9]
def baseStart_232087 : Nat := 118140960795 + 232087 * 2 ^ 59
def prefixEnd_232087 : Nat := 4983230072969 + 3 ^ 40 * 232087 * 2
def baseEnd_232087 : Nat := 13241353851126521360573

theorem tailTrace_232087 : CollatzResearch.WordTrace tailWord_232087 prefixEnd_232087 13241353851126521360573 := by
  unfold tailWord_232087
  simp only [CollatzResearch.WordTrace]
  refine ⟨8464908310195911149022515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5643272206797274099348343 8464908310195911149022515)
  ·
    refine ⟨12697362465293866723533773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8464908310195911149022515 12697362465293866723533773)
    ·
      refine ⟨4761510924485200021325165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12697362465293866723533773 4761510924485200021325165)
      ·
        refine ⟨1785566596681950007996937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4761510924485200021325165 1785566596681950007996937)
        ·
          refine ⟨1339174947511462505997703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1785566596681950007996937 1339174947511462505997703)
          ·
            refine ⟨2008762421267193758996555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339174947511462505997703 2008762421267193758996555)
            ·
              refine ⟨3013143631900790638494833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008762421267193758996555 3013143631900790638494833)
              ·
                refine ⟨2259857723925592978871125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3013143631900790638494833 2259857723925592978871125)
                ·
                  refine ⟨13241353851126521360573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2259857723925592978871125 13241353851126521360573)
                  ·
                    rfl

theorem cell23_232087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 9].length) (baseStart_232087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232087 prefixEnd_232087 := by exact prefixLift 232087
  have htrace : WordTrace (prefixWord ++ tailWord_232087) baseStart_232087 baseEnd_232087 := by
    simpa [prefixWord, tailWord_232087, baseEnd_232087] using wordTrace_append hprefix tailTrace_232087
  have hstable : (prefixWord ++ tailWord_232087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232087).length < 2 ^ (prefixWord ++ tailWord_232087).sum := by decide
  have hdescent : baseEnd_232087 < baseStart_232087 := by decide
  rcases family_descends (prefixWord ++ tailWord_232087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232115 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 2, 2, 2]
def baseStart_232115 : Nat := 118140960795 + 232115 * 2 ^ 59
def prefixEnd_232115 : Nat := 4983230072969 + 3 ^ 40 * 232115 * 2
def baseEnd_232115 : Nat := 119186562118464582695029

theorem tailTrace_232115 : CollatzResearch.WordTrace tailWord_232115 prefixEnd_232115 119186562118464582695029 := by
  unfold tailWord_232115
  simp only [CollatzResearch.WordTrace]
  refine ⟨8465929554094471931041799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5643953036062981287361199 8465929554094471931041799)
  ·
    refine ⟨12698894331141707896562699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8465929554094471931041799 12698894331141707896562699)
    ·
      refine ⟨19048341496712561844844049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12698894331141707896562699 19048341496712561844844049)
      ·
        refine ⟨14286256122534421383633037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19048341496712561844844049 14286256122534421383633037)
        ·
          refine ⟨5357346045950408018862389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14286256122534421383633037 5357346045950408018862389)
          ·
            refine ⟨502251191807850751768349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5357346045950408018862389 502251191807850751768349)
            ·
              refine ⟨188344196927944031913131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502251191807850751768349 188344196927944031913131)
              ·
                refine ⟨282516295391916047869697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188344196927944031913131 282516295391916047869697)
                ·
                  refine ⟨211887221543937035902273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282516295391916047869697 211887221543937035902273)
                  ·
                    refine ⟨158915416157952776926705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211887221543937035902273 158915416157952776926705)
                    ·
                      refine ⟨119186562118464582695029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 158915416157952776926705 119186562118464582695029)
                      ·
                        rfl

theorem cell23_232115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 2, 2, 2].length) (baseStart_232115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232115 prefixEnd_232115 := by exact prefixLift 232115
  have htrace : WordTrace (prefixWord ++ tailWord_232115) baseStart_232115 baseEnd_232115 := by
    simpa [prefixWord, tailWord_232115, baseEnd_232115] using wordTrace_append hprefix tailTrace_232115
  have hstable : (prefixWord ++ tailWord_232115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232115).length < 2 ^ (prefixWord ++ tailWord_232115).sum := by decide
  have hdescent : baseEnd_232115 < baseStart_232115 := by decide
  rcases family_descends (prefixWord ++ tailWord_232115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232138 : List Nat := [3, 1, 2, 1, 4, 3, 1, 3, 5]
def baseStart_232138 : Nat := 118140960795 + 232138 * 2 ^ 59
def prefixEnd_232138 : Nat := 4983230072969 + 3 ^ 40 * 232138 * 2
def baseEnd_232138 : Nat := 13244263574835332523047

theorem tailTrace_232138 : CollatzResearch.WordTrace tailWord_232138 prefixEnd_232138 13244263574835332523047 := by
  unfold tailWord_232138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2116692108252786714782267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5644512288674097906086045 2116692108252786714782267)
  ·
    refine ⟨3175038162379180072173401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2116692108252786714782267 3175038162379180072173401)
    ·
      refine ⟨2381278621784385054130051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3175038162379180072173401 2381278621784385054130051)
      ·
        refine ⟨3571917932676577581195077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381278621784385054130051 3571917932676577581195077)
        ·
          refine ⟨669734612376858296474077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3571917932676577581195077 669734612376858296474077)
          ·
            refine ⟨251150479641321861177779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 669734612376858296474077 251150479641321861177779)
            ·
              refine ⟨376725719461982791766669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251150479641321861177779 376725719461982791766669)
              ·
                refine ⟨141272144798243546912501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376725719461982791766669 141272144798243546912501)
                ·
                  refine ⟨13244263574835332523047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141272144798243546912501 13244263574835332523047)
                  ·
                    rfl

theorem cell23_232138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_232138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232138 prefixEnd_232138 := by exact prefixLift 232138
  have htrace : WordTrace (prefixWord ++ tailWord_232138) baseStart_232138 baseEnd_232138 := by
    simpa [prefixWord, tailWord_232138, baseEnd_232138] using wordTrace_append hprefix tailTrace_232138
  have hstable : (prefixWord ++ tailWord_232138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232138).length < 2 ^ (prefixWord ++ tailWord_232138).sum := by decide
  have hdescent : baseEnd_232138 < baseStart_232138 := by decide
  rcases family_descends (prefixWord ++ tailWord_232138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232215 : List Nat := [1, 1, 3, 4, 3, 1, 1, 4, 1, 4]
def baseStart_232215 : Nat := 118140960795 + 232215 * 2 ^ 59
def prefixEnd_232215 : Nat := 4983230072969 + 3 ^ 40 * 232215 * 2
def baseEnd_232215 : Nat := 39745970061304730481523

theorem tailTrace_232215 : CollatzResearch.WordTrace tailWord_232215 prefixEnd_232215 39745970061304730481523 := by
  unfold tailWord_232215
  simp only [CollatzResearch.WordTrace]
  refine ⟨8469576853732189009682099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5646384569154792673121399 8469576853732189009682099)
  ·
    refine ⟨12704365280598283514523149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8469576853732189009682099 12704365280598283514523149)
    ·
      refine ⟨4764136980224356317946181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12704365280598283514523149 4764136980224356317946181)
      ·
        refine ⟨893275683792066809614909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4764136980224356317946181 893275683792066809614909)
        ·
          refine ⟨334978381422025053605591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 893275683792066809614909 334978381422025053605591)
          ·
            refine ⟨502467572133037580408387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334978381422025053605591 502467572133037580408387)
            ·
              refine ⟨753701358199556370612581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502467572133037580408387 753701358199556370612581)
              ·
                refine ⟨141319004662416819489859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 753701358199556370612581 141319004662416819489859)
                ·
                  refine ⟨211978506993625229234789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141319004662416819489859 211978506993625229234789)
                  ·
                    refine ⟨39745970061304730481523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211978506993625229234789 39745970061304730481523)
                    ·
                      rfl

theorem cell23_232215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_232215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232215 prefixEnd_232215 := by exact prefixLift 232215
  have htrace : WordTrace (prefixWord ++ tailWord_232215) baseStart_232215 baseEnd_232215 := by
    simpa [prefixWord, tailWord_232215, baseEnd_232215] using wordTrace_append hprefix tailTrace_232215
  have hstable : (prefixWord ++ tailWord_232215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232215).length < 2 ^ (prefixWord ++ tailWord_232215).sum := by decide
  have hdescent : baseEnd_232215 < baseStart_232215 := by decide
  rcases family_descends (prefixWord ++ tailWord_232215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232241 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 1, 5]
def baseStart_232241 : Nat := 118140960795 + 232241 * 2 ^ 59
def prefixEnd_232241 : Nat := 4983230072969 + 3 ^ 40 * 232241 * 2
def baseEnd_232241 : Nat := 39750420226977029906483

theorem tailTrace_232241 : CollatzResearch.WordTrace tailWord_232241 prefixEnd_232241 39750420226977029906483 := by
  unfold tailWord_232241
  simp only [CollatzResearch.WordTrace]
  refine ⟨8470525151637995450128577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5647016767758663633419051 8470525151637995450128577)
  ·
    refine ⟨6352893863728496587596433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8470525151637995450128577 6352893863728496587596433)
    ·
      refine ⟨4764670397796372440697325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6352893863728496587596433 4764670397796372440697325)
      ·
        refine ⟨1786751399173639665261497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4764670397796372440697325 1786751399173639665261497)
        ·
          refine ⟨1340063549380229748946123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1786751399173639665261497 1340063549380229748946123)
          ·
            refine ⟨2010095324070344623419185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340063549380229748946123 2010095324070344623419185)
            ·
              refine ⟨1507571493052758467564389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2010095324070344623419185 1507571493052758467564389)
              ·
                refine ⟨282669654947392212668323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1507571493052758467564389 282669654947392212668323)
                ·
                  refine ⟨424004482421088319002485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282669654947392212668323 424004482421088319002485)
                  ·
                    refine ⟨39750420226977029906483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 424004482421088319002485 39750420226977029906483)
                    ·
                      rfl

theorem cell23_232241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_232241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232241 prefixEnd_232241 := by exact prefixLift 232241
  have htrace : WordTrace (prefixWord ++ tailWord_232241) baseStart_232241 baseEnd_232241 := by
    simpa [prefixWord, tailWord_232241, baseEnd_232241] using wordTrace_append hprefix tailTrace_232241
  have hstable : (prefixWord ++ tailWord_232241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232241).length < 2 ^ (prefixWord ++ tailWord_232241).sum := by decide
  have hdescent : baseEnd_232241 < baseStart_232241 := by decide
  rcases family_descends (prefixWord ++ tailWord_232241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232255 : List Nat := [1, 1, 2, 2, 5, 1, 1, 5, 1, 1, 3]
def baseStart_232255 : Nat := 118140960795 + 232255 * 2 ^ 59
def prefixEnd_232255 : Nat := 4983230072969 + 3 ^ 40 * 232255 * 2
def baseEnd_232255 : Nat := 119258449410094034944385

theorem tailTrace_232255 : CollatzResearch.WordTrace tailWord_232255 prefixEnd_232255 119258449410094034944385 := by
  unfold tailWord_232255
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471035773587275841138219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5647357182391517227425479 8471035773587275841138219)
  ·
    refine ⟨12706553660380913761707329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8471035773587275841138219 12706553660380913761707329)
    ·
      refine ⟨9529915245285685321280497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12706553660380913761707329 9529915245285685321280497)
      ·
        refine ⟨7147436433964263990960373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9529915245285685321280497 7147436433964263990960373)
        ·
          refine ⟨670072165684149749152535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7147436433964263990960373 670072165684149749152535)
          ·
            refine ⟨1005108248526224623728803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670072165684149749152535 1005108248526224623728803)
            ·
              refine ⟨1507662372789336935593205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005108248526224623728803 1507662372789336935593205)
              ·
                refine ⟨141343347449000337711863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1507662372789336935593205 141343347449000337711863)
                ·
                  refine ⟨212015021173500506567795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141343347449000337711863 212015021173500506567795)
                  ·
                    refine ⟨318022531760250759851693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 212015021173500506567795 318022531760250759851693)
                    ·
                      refine ⟨119258449410094034944385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 318022531760250759851693 119258449410094034944385)
                      ·
                        rfl

theorem cell23_232255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 1, 1, 3].length) (baseStart_232255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232255 prefixEnd_232255 := by exact prefixLift 232255
  have htrace : WordTrace (prefixWord ++ tailWord_232255) baseStart_232255 baseEnd_232255 := by
    simpa [prefixWord, tailWord_232255, baseEnd_232255] using wordTrace_append hprefix tailTrace_232255
  have hstable : (prefixWord ++ tailWord_232255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232255).length < 2 ^ (prefixWord ++ tailWord_232255).sum := by decide
  have hdescent : baseEnd_232255 < baseStart_232255 := by decide
  rcases family_descends (prefixWord ++ tailWord_232255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232262 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_232262 : Nat := 118140960795 + 232262 * 2 ^ 59
def prefixEnd_232262 : Nat := 4983230072969 + 3 ^ 40 * 232262 * 2
def baseEnd_232262 : Nat := 13251338197186167506317

theorem tailTrace_232262 : CollatzResearch.WordTrace tailWord_232262 prefixEnd_232262 13251338197186167506317 := by
  unfold tailWord_232262
  simp only [CollatzResearch.WordTrace]
  refine ⟨264727846392559876145095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5647527389707944024428693 264727846392559876145095)
  ·
    refine ⟨397091769588839814217643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264727846392559876145095 397091769588839814217643)
    ·
      refine ⟨595637654383259721326465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397091769588839814217643 595637654383259721326465)
      ·
        refine ⟨446728240787444790994849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595637654383259721326465 446728240787444790994849)
        ·
          refine ⟨335046180590583593246137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446728240787444790994849 335046180590583593246137)
          ·
            refine ⟨251284635442937694934603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335046180590583593246137 251284635442937694934603)
            ·
              refine ⟨376926953164406542401905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251284635442937694934603 376926953164406542401905)
              ·
                refine ⟨282695214873304906801429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376926953164406542401905 282695214873304906801429)
                ·
                  refine ⟨13251338197186167506317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282695214873304906801429 13251338197186167506317)
                  ·
                    rfl

theorem cell23_232262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_232262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232262 prefixEnd_232262 := by exact prefixLift 232262
  have htrace : WordTrace (prefixWord ++ tailWord_232262) baseStart_232262 baseEnd_232262 := by
    simpa [prefixWord, tailWord_232262, baseEnd_232262] using wordTrace_append hprefix tailTrace_232262
  have hstable : (prefixWord ++ tailWord_232262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232262).length < 2 ^ (prefixWord ++ tailWord_232262).sum := by decide
  have hdescent : baseEnd_232262 < baseStart_232262 := by decide
  rcases family_descends (prefixWord ++ tailWord_232262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232281 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 5]
def baseStart_232281 : Nat := 118140960795 + 232281 * 2 ^ 59
def prefixEnd_232281 : Nat := 4983230072969 + 3 ^ 40 * 232281 * 2
def baseEnd_232281 : Nat := 119271799907110933219265

theorem tailTrace_232281 : CollatzResearch.WordTrace tailWord_232281 prefixEnd_232281 119271799907110933219265 := by
  unfold tailWord_232281
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471984071493082281584697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5647989380995388187723131 8471984071493082281584697)
  ·
    refine ⟨6353988053619811711188523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8471984071493082281584697 6353988053619811711188523)
    ·
      refine ⟨9530982080429717566782785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6353988053619811711188523 9530982080429717566782785)
      ·
        refine ⟨7148236560322288175087089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9530982080429717566782785 7148236560322288175087089)
        ·
          refine ⟨5361177420241716131315317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7148236560322288175087089 5361177420241716131315317)
          ·
            refine ⟨502610383147660887310811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5361177420241716131315317 502610383147660887310811)
            ·
              refine ⟨753915574721491330966217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502610383147660887310811 753915574721491330966217)
              ·
                refine ⟨565436681041118498224663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753915574721491330966217 565436681041118498224663)
                ·
                  refine ⟨848155021561677747336995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565436681041118498224663 848155021561677747336995)
                  ·
                    refine ⟨1272232532342516621005493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 848155021561677747336995 1272232532342516621005493)
                    ·
                      refine ⟨119271799907110933219265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1272232532342516621005493 119271799907110933219265)
                      ·
                        rfl

theorem cell23_232281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_232281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232281 prefixEnd_232281 := by exact prefixLift 232281
  have htrace : WordTrace (prefixWord ++ tailWord_232281) baseStart_232281 baseEnd_232281 := by
    simpa [prefixWord, tailWord_232281, baseEnd_232281] using wordTrace_append hprefix tailTrace_232281
  have hstable : (prefixWord ++ tailWord_232281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232281).length < 2 ^ (prefixWord ++ tailWord_232281).sum := by decide
  have hdescent : baseEnd_232281 < baseStart_232281 := by decide
  rcases family_descends (prefixWord ++ tailWord_232281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232291 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 6]
def baseStart_232291 : Nat := 118140960795 + 232291 * 2 ^ 59
def prefixEnd_232291 : Nat := 4983230072969 + 3 ^ 40 * 232291 * 2
def baseEnd_232291 : Nat := 119276934713655894094219

theorem tailTrace_232291 : CollatzResearch.WordTrace tailWord_232291 prefixEnd_232291 119276934713655894094219 := by
  unfold tailWord_232291
  simp only [CollatzResearch.WordTrace]
  refine ⟨8472348801456853989448727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5648232534304569326299151 8472348801456853989448727)
  ·
    refine ⟨12708523202185280984173091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8472348801456853989448727 12708523202185280984173091)
    ·
      refine ⟨19062784803277921476259637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12708523202185280984173091 19062784803277921476259637)
      ·
        refine ⟨1787136075307305138399341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19062784803277921476259637 1787136075307305138399341)
        ·
          refine ⟨670176028240239426899753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1787136075307305138399341 670176028240239426899753)
          ·
            refine ⟨502632021180179570174815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670176028240239426899753 502632021180179570174815)
            ·
              refine ⟨753948031770269355262223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502632021180179570174815 753948031770269355262223)
              ·
                refine ⟨1130922047655404032893335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753948031770269355262223 1130922047655404032893335)
                ·
                  refine ⟨1696383071483106049340003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130922047655404032893335 1696383071483106049340003)
                  ·
                    refine ⟨2544574607224659074010005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1696383071483106049340003 2544574607224659074010005)
                    ·
                      refine ⟨119276934713655894094219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2544574607224659074010005 119276934713655894094219)
                      ·
                        rfl

theorem cell23_232291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_232291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232291 prefixEnd_232291 := by exact prefixLift 232291
  have htrace : WordTrace (prefixWord ++ tailWord_232291) baseStart_232291 baseEnd_232291 := by
    simpa [prefixWord, tailWord_232291, baseEnd_232291] using wordTrace_append hprefix tailTrace_232291
  have hstable : (prefixWord ++ tailWord_232291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232291).length < 2 ^ (prefixWord ++ tailWord_232291).sum := by decide
  have hdescent : baseEnd_232291 < baseStart_232291 := by decide
  rcases family_descends (prefixWord ++ tailWord_232291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232295 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_232295 : Nat := 118140960795 + 232295 * 2 ^ 59
def prefixEnd_232295 : Nat := 4983230072969 + 3 ^ 40 * 232295 * 2
def baseEnd_232295 : Nat := 119278988636273878444201

theorem tailTrace_232295 : CollatzResearch.WordTrace tailWord_232295 prefixEnd_232295 119278988636273878444201 := by
  unfold tailWord_232295
  simp only [CollatzResearch.WordTrace]
  refine ⟨8472494693442362672594339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5648329795628241781729559 8472494693442362672594339)
  ·
    refine ⟨12708742040163544008891509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8472494693442362672594339 12708742040163544008891509)
    ·
      refine ⟨1191444566265332250833579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12708742040163544008891509 1191444566265332250833579)
      ·
        refine ⟨1787166849397998376250369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191444566265332250833579 1787166849397998376250369)
        ·
          refine ⟨1340375137048498782187777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1787166849397998376250369 1340375137048498782187777)
          ·
            refine ⟨1005281352786374086640833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340375137048498782187777 1005281352786374086640833)
            ·
              refine ⟨753961014589780564980625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005281352786374086640833 753961014589780564980625)
              ·
                refine ⟨565470760942335423735469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753961014589780564980625 565470760942335423735469)
                ·
                  refine ⟨212051535353375783900801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565470760942335423735469 212051535353375783900801)
                  ·
                    refine ⟨159038651515031837925601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212051535353375783900801 159038651515031837925601)
                    ·
                      refine ⟨119278988636273878444201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159038651515031837925601 119278988636273878444201)
                      ·
                        rfl

theorem cell23_232295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_232295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232295 prefixEnd_232295 := by exact prefixLift 232295
  have htrace : WordTrace (prefixWord ++ tailWord_232295) baseStart_232295 baseEnd_232295 := by
    simpa [prefixWord, tailWord_232295, baseEnd_232295] using wordTrace_append hprefix tailTrace_232295
  have hstable : (prefixWord ++ tailWord_232295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232295).length < 2 ^ (prefixWord ++ tailWord_232295).sum := by decide
  have hdescent : baseEnd_232295 < baseStart_232295 := by decide
  rcases family_descends (prefixWord ++ tailWord_232295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232311 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 3]
def baseStart_232311 : Nat := 118140960795 + 232311 * 2 ^ 59
def prefixEnd_232311 : Nat := 4983230072969 + 3 ^ 40 * 232311 * 2
def baseEnd_232311 : Nat := 119287204326745815844127

theorem tailTrace_232311 : CollatzResearch.WordTrace tailWord_232311 prefixEnd_232311 119287204326745815844127 := by
  unfold tailWord_232311
  simp only [CollatzResearch.WordTrace]
  refine ⟨8473078261384397405176787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5648718840922931603451191 8473078261384397405176787)
  ·
    refine ⟨12709617392076596107765181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8473078261384397405176787 12709617392076596107765181)
    ·
      refine ⟨4766106522028723540411943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12709617392076596107765181 4766106522028723540411943)
      ·
        refine ⟨7149159783043085310617915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4766106522028723540411943 7149159783043085310617915)
        ·
          refine ⟨10723739674564627965926873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7149159783043085310617915 10723739674564627965926873)
          ·
            refine ⟨8042804755923470974445155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10723739674564627965926873 8042804755923470974445155)
            ·
              refine ⟨12064207133885206461667733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8042804755923470974445155 12064207133885206461667733)
              ·
                refine ⟨565509709400869052890675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12064207133885206461667733 565509709400869052890675)
                ·
                  refine ⟨848264564101303579336013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565509709400869052890675 848264564101303579336013)
                  ·
                    refine ⟨318099211537988842251005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 848264564101303579336013 318099211537988842251005)
                    ·
                      refine ⟨119287204326745815844127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 318099211537988842251005 119287204326745815844127)
                      ·
                        rfl

theorem cell23_232311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_232311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232311 prefixEnd_232311 := by exact prefixLift 232311
  have htrace : WordTrace (prefixWord ++ tailWord_232311) baseStart_232311 baseEnd_232311 := by
    simpa [prefixWord, tailWord_232311, baseEnd_232311] using wordTrace_append hprefix tailTrace_232311
  have hstable : (prefixWord ++ tailWord_232311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232311).length < 2 ^ (prefixWord ++ tailWord_232311).sum := by decide
  have hdescent : baseEnd_232311 < baseStart_232311 := by decide
  rcases family_descends (prefixWord ++ tailWord_232311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232314 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_232314 : Nat := 118140960795 + 232314 * 2 ^ 59
def prefixEnd_232314 : Nat := 4983230072969 + 3 ^ 40 * 232314 * 2
def baseEnd_232314 : Nat := 39762914922903101368871

theorem tailTrace_232314 : CollatzResearch.WordTrace tailWord_232314 prefixEnd_232314 39762914922903101368871 := by
  unfold tailWord_232314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118296920093382229383999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5648791786915685945023997 2118296920093382229383999)
  ·
    refine ⟨3177445380140073344075999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2118296920093382229383999 3177445380140073344075999)
    ·
      refine ⟨4766168070210110016113999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3177445380140073344075999 4766168070210110016113999)
      ·
        refine ⟨7149252105315165024170999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4766168070210110016113999 7149252105315165024170999)
        ·
          refine ⟨10723878157972747536256499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7149252105315165024170999 10723878157972747536256499)
          ·
            refine ⟨16085817236959121304384749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10723878157972747536256499 16085817236959121304384749)
            ·
              refine ⟨6032181463859670489144281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16085817236959121304384749 6032181463859670489144281)
              ·
                refine ⟨4524136097894752866858211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6032181463859670489144281 4524136097894752866858211)
                ·
                  refine ⟨6786204146842129300287317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4524136097894752866858211 6786204146842129300287317)
                  ·
                    refine ⟨39762914922903101368871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 6786204146842129300287317 39762914922903101368871)
                    ·
                      rfl

theorem cell23_232314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_232314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232314 prefixEnd_232314 := by exact prefixLift 232314
  have htrace : WordTrace (prefixWord ++ tailWord_232314) baseStart_232314 baseEnd_232314 := by
    simpa [prefixWord, tailWord_232314, baseEnd_232314] using wordTrace_append hprefix tailTrace_232314
  have hstable : (prefixWord ++ tailWord_232314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232314).length < 2 ^ (prefixWord ++ tailWord_232314).sum := by decide
  have hdescent : baseEnd_232314 < baseStart_232314 := by decide
  rcases family_descends (prefixWord ++ tailWord_232314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232329 : List Nat := [1, 2, 1, 1, 5, 3, 3, 2, 1, 2, 2]
def baseStart_232329 : Nat := 118140960795 + 232329 * 2 ^ 59
def prefixEnd_232329 : Nat := 4983230072969 + 3 ^ 40 * 232329 * 2
def baseEnd_232329 : Nat := 119296446978526745419045

theorem tailTrace_232329 : CollatzResearch.WordTrace tailWord_232329 prefixEnd_232329 119296446978526745419045 := by
  unfold tailWord_232329
  simp only [CollatzResearch.WordTrace]
  refine ⟨8473734775319186479332041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5649156516879457652888027 8473734775319186479332041)
  ·
    refine ⟨6355301081489389859499031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8473734775319186479332041 6355301081489389859499031)
    ·
      refine ⟨9532951622234084789248547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6355301081489389859499031 9532951622234084789248547)
      ·
        refine ⟨14299427433351127183872821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9532951622234084789248547 14299427433351127183872821)
        ·
          refine ⟨1340571321876668173488077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14299427433351127183872821 1340571321876668173488077)
          ·
            refine ⟨502714245703750565058029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1340571321876668173488077 502714245703750565058029)
            ·
              refine ⟨188517842138906461896761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502714245703750565058029 188517842138906461896761)
              ·
                refine ⟨141388381604179846422571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188517842138906461896761 141388381604179846422571)
                ·
                  refine ⟨212082572406269769633857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141388381604179846422571 212082572406269769633857)
                  ·
                    refine ⟨159061929304702327225393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212082572406269769633857 159061929304702327225393)
                    ·
                      refine ⟨119296446978526745419045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159061929304702327225393 119296446978526745419045)
                      ·
                        rfl

theorem cell23_232329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 1, 2, 2].length) (baseStart_232329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232329 prefixEnd_232329 := by exact prefixLift 232329
  have htrace : WordTrace (prefixWord ++ tailWord_232329) baseStart_232329 baseEnd_232329 := by
    simpa [prefixWord, tailWord_232329, baseEnd_232329] using wordTrace_append hprefix tailTrace_232329
  have hstable : (prefixWord ++ tailWord_232329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232329).length < 2 ^ (prefixWord ++ tailWord_232329).sum := by decide
  have hdescent : baseEnd_232329 < baseStart_232329 := by decide
  rcases family_descends (prefixWord ++ tailWord_232329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232355 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 1, 3, 2]
def baseStart_232355 : Nat := 118140960795 + 232355 * 2 ^ 59
def prefixEnd_232355 : Nat := 4983230072969 + 3 ^ 40 * 232355 * 2
def baseEnd_232355 : Nat := 119309797475543643693925

theorem tailTrace_232355 : CollatzResearch.WordTrace tailWord_232355 prefixEnd_232355 119309797475543643693925 := by
  unfold tailWord_232355
  simp only [CollatzResearch.WordTrace]
  refine ⟨8474683073224992919778519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5649788715483328613185679 8474683073224992919778519)
  ·
    refine ⟨12712024609837489379667779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8474683073224992919778519 12712024609837489379667779)
    ·
      refine ⟨19068036914756234069501669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12712024609837489379667779 19068036914756234069501669)
      ·
        refine ⟨3575256921516793888031563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19068036914756234069501669 3575256921516793888031563)
        ·
          refine ⟨5362885382275190832047345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575256921516793888031563 5362885382275190832047345)
          ·
            refine ⟨4022164036706393124035509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5362885382275190832047345 4022164036706393124035509)
            ·
              refine ⟨377077878441224355378329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4022164036706393124035509 377077878441224355378329)
              ·
                refine ⟨282808408830918266533747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377077878441224355378329 282808408830918266533747)
                ·
                  refine ⟨424212613246377399800621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282808408830918266533747 424212613246377399800621)
                  ·
                    refine ⟨159079729967391524925233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 424212613246377399800621 159079729967391524925233)
                    ·
                      refine ⟨119309797475543643693925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159079729967391524925233 119309797475543643693925)
                      ·
                        rfl

theorem cell23_232355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_232355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232355 prefixEnd_232355 := by exact prefixLift 232355
  have htrace : WordTrace (prefixWord ++ tailWord_232355) baseStart_232355 baseEnd_232355 := by
    simpa [prefixWord, tailWord_232355, baseEnd_232355] using wordTrace_append hprefix tailTrace_232355
  have hstable : (prefixWord ++ tailWord_232355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232355).length < 2 ^ (prefixWord ++ tailWord_232355).sum := by decide
  have hdescent : baseEnd_232355 < baseStart_232355 := by decide
  rcases family_descends (prefixWord ++ tailWord_232355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232398 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_232398 : Nat := 118140960795 + 232398 * 2 ^ 59
def prefixEnd_232398 : Nat := 4983230072969 + 3 ^ 40 * 232398 * 2
def baseEnd_232398 : Nat := 119331877143686975456227

theorem tailTrace_232398 : CollatzResearch.WordTrace tailWord_232398 prefixEnd_232398 119331877143686975456227 := by
  unfold tailWord_232398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1059531426508651407949231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5650834274712807509062565 1059531426508651407949231)
  ·
    refine ⟨1589297139762977111923847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1059531426508651407949231 1589297139762977111923847)
    ·
      refine ⟨2383945709644465667885771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589297139762977111923847 2383945709644465667885771)
      ·
        refine ⟨3575918564466698501828657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383945709644465667885771 3575918564466698501828657)
        ·
          refine ⟨2681938923350023876371493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3575918564466698501828657 2681938923350023876371493)
          ·
            refine ⟨502863548128129476819655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2681938923350023876371493 502863548128129476819655)
            ·
              refine ⟨754295322192194215229483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502863548128129476819655 754295322192194215229483)
              ·
                refine ⟨1131442983288291322844225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754295322192194215229483 1131442983288291322844225)
                ·
                  refine ⟨848582237466218492133169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1131442983288291322844225 848582237466218492133169)
                  ·
                    refine ⟨636436678099663869099877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 848582237466218492133169 636436678099663869099877)
                    ·
                      refine ⟨119331877143686975456227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 636436678099663869099877 119331877143686975456227)
                      ·
                        rfl

theorem cell23_232398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_232398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232398 prefixEnd_232398 := by exact prefixLift 232398
  have htrace : WordTrace (prefixWord ++ tailWord_232398) baseStart_232398 baseEnd_232398 := by
    simpa [prefixWord, tailWord_232398, baseEnd_232398] using wordTrace_append hprefix tailTrace_232398
  have hstable : (prefixWord ++ tailWord_232398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232398).length < 2 ^ (prefixWord ++ tailWord_232398).sum := by decide
  have hdescent : baseEnd_232398 < baseStart_232398 := by decide
  rcases family_descends (prefixWord ++ tailWord_232398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232402 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_232402 : Nat := 118140960795 + 232402 * 2 ^ 59
def prefixEnd_232402 : Nat := 4983230072969 + 3 ^ 40 * 232402 * 2
def baseEnd_232402 : Nat := 119333931066304959806209

theorem tailTrace_232402 : CollatzResearch.WordTrace tailWord_232402 prefixEnd_232402 119333931066304959806209 := by
  unfold tailWord_232402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119099326013679986684865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5650931536036479964492973 2119099326013679986684865)
  ·
    refine ⟨1589324494510259990013649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2119099326013679986684865 1589324494510259990013649)
    ·
      refine ⟨1191993370882694992510237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1589324494510259990013649 1191993370882694992510237)
      ·
        refine ⟨446997514081010622191339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1191993370882694992510237 446997514081010622191339)
        ·
          refine ⟨670496271121515933287009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446997514081010622191339 670496271121515933287009)
          ·
            refine ⟨502872203341136949965257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670496271121515933287009 502872203341136949965257)
            ·
              refine ⟨377154152505852712473943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502872203341136949965257 377154152505852712473943)
              ·
                refine ⟨565731228758779068710915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377154152505852712473943 565731228758779068710915)
                ·
                  refine ⟨848596843138168603066373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565731228758779068710915 848596843138168603066373)
                  ·
                    refine ⟨159111908088406613074945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 848596843138168603066373 159111908088406613074945)
                    ·
                      refine ⟨119333931066304959806209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159111908088406613074945 119333931066304959806209)
                      ·
                        rfl

theorem cell23_232402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_232402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232402 prefixEnd_232402 := by exact prefixLift 232402
  have htrace : WordTrace (prefixWord ++ tailWord_232402) baseStart_232402 baseEnd_232402 := by
    simpa [prefixWord, tailWord_232402, baseEnd_232402] using wordTrace_append hprefix tailTrace_232402
  have hstable : (prefixWord ++ tailWord_232402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232402).length < 2 ^ (prefixWord ++ tailWord_232402).sum := by decide
  have hdescent : baseEnd_232402 < baseStart_232402 := by decide
  rcases family_descends (prefixWord ++ tailWord_232402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232458 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_232458 : Nat := 118140960795 + 232458 * 2 ^ 59
def prefixEnd_232458 : Nat := 4983230072969 + 3 ^ 40 * 232458 * 2
def baseEnd_232458 : Nat := 119362685982956740705951

theorem tailTrace_232458 : CollatzResearch.WordTrace tailWord_232458 prefixEnd_232458 119362685982956740705951 := by
  unfold tailWord_232458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119609947962960377694507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5652293194567894340518685 2119609947962960377694507)
  ·
    refine ⟨3179414921944440566541761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2119609947962960377694507 3179414921944440566541761)
    ·
      refine ⟨2384561191458330424906321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3179414921944440566541761 2384561191458330424906321)
      ·
        refine ⟨1788420893593747818679741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2384561191458330424906321 1788420893593747818679741)
        ·
          refine ⟨670657835097655432004903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1788420893593747818679741 670657835097655432004903)
          ·
            refine ⟨1005986752646483148007355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670657835097655432004903 1005986752646483148007355)
            ·
              refine ⟨1508980128969724722011033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005986752646483148007355 1508980128969724722011033)
              ·
                refine ⟨1131735096727293541508275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1508980128969724722011033 1131735096727293541508275)
                ·
                  refine ⟨1697602645090940312262413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131735096727293541508275 1697602645090940312262413)
                  ·
                    refine ⟨636600991909102617098405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1697602645090940312262413 636600991909102617098405)
                    ·
                      refine ⟨119362685982956740705951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 636600991909102617098405 119362685982956740705951)
                      ·
                        rfl

theorem cell23_232458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_232458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232458 prefixEnd_232458 := by exact prefixLift 232458
  have htrace : WordTrace (prefixWord ++ tailWord_232458) baseStart_232458 baseEnd_232458 := by
    simpa [prefixWord, tailWord_232458, baseEnd_232458] using wordTrace_append hprefix tailTrace_232458
  have hstable : (prefixWord ++ tailWord_232458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232458).length < 2 ^ (prefixWord ++ tailWord_232458).sum := by decide
  have hdescent : baseEnd_232458 < baseStart_232458 := by decide
  rcases family_descends (prefixWord ++ tailWord_232458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232498 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 6]
def baseStart_232498 : Nat := 118140960795 + 232498 * 2 ^ 59
def prefixEnd_232498 : Nat := 4983230072969 + 3 ^ 40 * 232498 * 2
def baseEnd_232498 : Nat := 13264802801015176022863

theorem tailTrace_232498 : CollatzResearch.WordTrace tailWord_232498 prefixEnd_232498 13264802801015176022863 := by
  unfold tailWord_232498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119974677926732085558537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5653265807804618894822765 2119974677926732085558537)
  ·
    refine ⟨1589981008445049064168903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2119974677926732085558537 1589981008445049064168903)
    ·
      refine ⟨2384971512667573596253355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589981008445049064168903 2384971512667573596253355)
      ·
        refine ⟨3577457269001360394380033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384971512667573596253355 3577457269001360394380033)
        ·
          refine ⟨2683092951751020295785025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3577457269001360394380033 2683092951751020295785025)
          ·
            refine ⟨2012319713813265221838769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2683092951751020295785025 2012319713813265221838769)
            ·
              refine ⟨1509239785359948916379077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012319713813265221838769 1509239785359948916379077)
              ·
                refine ⟨282982459754990421821077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1509239785359948916379077 282982459754990421821077)
                ·
                  refine ⟨13264802801015176022863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282982459754990421821077 13264802801015176022863)
                  ·
                    rfl

theorem cell23_232498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_232498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232498 prefixEnd_232498 := by exact prefixLift 232498
  have htrace : WordTrace (prefixWord ++ tailWord_232498) baseStart_232498 baseEnd_232498 := by
    simpa [prefixWord, tailWord_232498, baseEnd_232498] using wordTrace_append hprefix tailTrace_232498
  have hstable : (prefixWord ++ tailWord_232498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232498).length < 2 ^ (prefixWord ++ tailWord_232498).sum := by decide
  have hdescent : baseEnd_232498 < baseStart_232498 := by decide
  rcases family_descends (prefixWord ++ tailWord_232498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232502 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_232502 : Nat := 118140960795 + 232502 * 2 ^ 59
def prefixEnd_232502 : Nat := 4983230072969 + 3 ^ 40 * 232502 * 2
def baseEnd_232502 : Nat := 39795093043918189518583

theorem tailTrace_232502 : CollatzResearch.WordTrace tailWord_232502 prefixEnd_232502 39795093043918189518583 := by
  unfold tailWord_232502
  simp only [CollatzResearch.WordTrace]
  refine ⟨530002787730777314086235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5653363069128291350253173 530002787730777314086235)
  ·
    refine ⟨795004181596165971129353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 530002787730777314086235 795004181596165971129353)
    ·
      refine ⟨596253136197124478347015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 795004181596165971129353 596253136197124478347015)
      ·
        refine ⟨894379704295686717520523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596253136197124478347015 894379704295686717520523)
        ·
          refine ⟨1341569556443530076280785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894379704295686717520523 1341569556443530076280785)
          ·
            refine ⟨1006177167332647557210589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341569556443530076280785 1006177167332647557210589)
            ·
              refine ⟨377316437749742833953971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1006177167332647557210589 377316437749742833953971)
              ·
                refine ⟨565974656624614250930957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377316437749742833953971 565974656624614250930957)
                ·
                  refine ⟨212240496234230344099109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565974656624614250930957 212240496234230344099109)
                  ·
                    refine ⟨39795093043918189518583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212240496234230344099109 39795093043918189518583)
                    ·
                      rfl

theorem cell23_232502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_232502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232502 prefixEnd_232502 := by exact prefixLift 232502
  have htrace : WordTrace (prefixWord ++ tailWord_232502) baseStart_232502 baseEnd_232502 := by
    simpa [prefixWord, tailWord_232502, baseEnd_232502] using wordTrace_append hprefix tailTrace_232502
  have hstable : (prefixWord ++ tailWord_232502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232502).length < 2 ^ (prefixWord ++ tailWord_232502).sum := by decide
  have hdescent : baseEnd_232502 < baseStart_232502 := by decide
  rcases family_descends (prefixWord ++ tailWord_232502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232511 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 2, 9]
def baseStart_232511 : Nat := 118140960795 + 232511 * 2 ^ 59
def prefixEnd_232511 : Nat := 4983230072969 + 3 ^ 40 * 232511 * 2
def baseEnd_232511 : Nat := 39796633485881677781069

theorem tailTrace_232511 : CollatzResearch.WordTrace tailWord_232511 prefixEnd_232511 39796633485881677781069 := by
  unfold tailWord_232511
  simp only [CollatzResearch.WordTrace]
  refine ⟨8480372860659831562457387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5653581907106554374971591 8480372860659831562457387)
  ·
    refine ⟨12720559290989747343686081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8480372860659831562457387 12720559290989747343686081)
    ·
      refine ⟨9540419468242310507764561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12720559290989747343686081 9540419468242310507764561)
      ·
        refine ⟨7155314601181732880823421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9540419468242310507764561 7155314601181732880823421)
        ·
          refine ⟨2683242975443149830308783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7155314601181732880823421 2683242975443149830308783)
          ·
            refine ⟨4024864463164724745463175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683242975443149830308783 4024864463164724745463175)
            ·
              refine ⟨6037296694747087118194763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024864463164724745463175 6037296694747087118194763)
              ·
                refine ⟨9055945042120630677292145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037296694747087118194763 9055945042120630677292145)
                ·
                  refine ⟨6791958781590473007969109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9055945042120630677292145 6791958781590473007969109)
                  ·
                    refine ⟨39796633485881677781069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 6791958781590473007969109 39796633485881677781069)
                    ·
                      rfl

theorem cell23_232511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_232511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232511 prefixEnd_232511 := by exact prefixLift 232511
  have htrace : WordTrace (prefixWord ++ tailWord_232511) baseStart_232511 baseEnd_232511 := by
    simpa [prefixWord, tailWord_232511, baseEnd_232511] using wordTrace_append hprefix tailTrace_232511
  have hstable : (prefixWord ++ tailWord_232511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232511).length < 2 ^ (prefixWord ++ tailWord_232511).sum := by decide
  have hdescent : baseEnd_232511 < baseStart_232511 := by decide
  rcases family_descends (prefixWord ++ tailWord_232511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232521 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_232521 : Nat := 118140960795 + 232521 * 2 ^ 59
def prefixEnd_232521 : Nat := 4983230072969 + 3 ^ 40 * 232521 * 2
def baseEnd_232521 : Nat := 119395035264189994218161

theorem tailTrace_232521 : CollatzResearch.WordTrace tailWord_232521 prefixEnd_232521 119395035264189994218161 := by
  unfold tailWord_232521
  simp only [CollatzResearch.WordTrace]
  refine ⟨8480737590623603270321417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5653825060415735513547611 8480737590623603270321417)
  ·
    refine ⟨6360553192967702452741063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8480737590623603270321417 6360553192967702452741063)
    ·
      refine ⟨9540829789451553679111595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6360553192967702452741063 9540829789451553679111595)
      ·
        refine ⟨14311244684177330518667393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9540829789451553679111595 14311244684177330518667393)
        ·
          refine ⟨10733433513132997889000545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14311244684177330518667393 10733433513132997889000545)
          ·
            refine ⟨8050075134849748416750409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10733433513132997889000545 8050075134849748416750409)
            ·
              refine ⟨6037556351137311312562807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8050075134849748416750409 6037556351137311312562807)
              ·
                refine ⟨9056334526705966968844211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037556351137311312562807 9056334526705966968844211)
                ·
                  refine ⟨13584501790058950453266317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9056334526705966968844211 13584501790058950453266317)
                  ·
                    refine ⟨5094188171272106419974869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13584501790058950453266317 5094188171272106419974869)
                    ·
                      refine ⟨119395035264189994218161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5094188171272106419974869 119395035264189994218161)
                      ·
                        rfl

theorem cell23_232521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_232521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232521 prefixEnd_232521 := by exact prefixLift 232521
  have htrace : WordTrace (prefixWord ++ tailWord_232521) baseStart_232521 baseEnd_232521 := by
    simpa [prefixWord, tailWord_232521, baseEnd_232521] using wordTrace_append hprefix tailTrace_232521
  have hstable : (prefixWord ++ tailWord_232521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232521).length < 2 ^ (prefixWord ++ tailWord_232521).sum := by decide
  have hdescent : baseEnd_232521 < baseStart_232521 := by decide
  rcases family_descends (prefixWord ++ tailWord_232521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232568 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_232568 : Nat := 118140960795 + 232568 * 2 ^ 59
def prefixEnd_232568 : Nat := 4983230072969 + 3 ^ 40 * 232568 * 2
def baseEnd_232568 : Nat := 119419168854951310330445

theorem tailTrace_232568 : CollatzResearch.WordTrace tailWord_232568 prefixEnd_232568 119419168854951310330445 := by
  unfold tailWord_232568
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241225910726665148641179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5654967880968886864854905 4241225910726665148641179)
  ·
    refine ⟨6361838866089997722961769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4241225910726665148641179 6361838866089997722961769)
    ·
      refine ⟨4771379149567498292221327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6361838866089997722961769 4771379149567498292221327)
      ·
        refine ⟨7157068724351247438331991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4771379149567498292221327 7157068724351247438331991)
        ·
          refine ⟨10735603086526871157497987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7157068724351247438331991 10735603086526871157497987)
          ·
            refine ⟨16103404629790306736246981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10735603086526871157497987 16103404629790306736246981)
            ·
              refine ⟨3019388368085682513046309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16103404629790306736246981 3019388368085682513046309)
              ·
                refine ⟨566135319016065471196183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3019388368085682513046309 566135319016065471196183)
                ·
                  refine ⟨849202978524098206794275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566135319016065471196183 849202978524098206794275)
                  ·
                    refine ⟨1273804467786147310191413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 849202978524098206794275 1273804467786147310191413)
                    ·
                      refine ⟨119419168854951310330445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1273804467786147310191413 119419168854951310330445)
                      ·
                        rfl

theorem cell23_232568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_232568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232568 prefixEnd_232568 := by exact prefixLift 232568
  have htrace : WordTrace (prefixWord ++ tailWord_232568) baseStart_232568 baseEnd_232568 := by
    simpa [prefixWord, tailWord_232568, baseEnd_232568] using wordTrace_append hprefix tailTrace_232568
  have hstable : (prefixWord ++ tailWord_232568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232568).length < 2 ^ (prefixWord ++ tailWord_232568).sum := by decide
  have hdescent : baseEnd_232568 < baseStart_232568 := by decide
  rcases family_descends (prefixWord ++ tailWord_232568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232585 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 3, 2, 3]
def baseStart_232585 : Nat := 118140960795 + 232585 * 2 ^ 59
def prefixEnd_232585 : Nat := 4983230072969 + 3 ^ 40 * 232585 * 2
def baseEnd_232585 : Nat := 119427898026077743817867

theorem tailTrace_232585 : CollatzResearch.WordTrace tailWord_232585 prefixEnd_232585 119427898026077743817867 := by
  unfold tailWord_232585
  simp only [CollatzResearch.WordTrace]
  refine ⟨8483071862391742200651209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5655381241594494800434139 8483071862391742200651209)
  ·
    refine ⟨6362303896793806650488407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8483071862391742200651209 6362303896793806650488407)
    ·
      refine ⟨9543455845190709975732611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6362303896793806650488407 9543455845190709975732611)
      ·
        refine ⟨14315183767786064963598917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9543455845190709975732611 14315183767786064963598917)
        ·
          refine ⟨2684096956459887180674797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14315183767786064963598917 2684096956459887180674797)
          ·
            refine ⟨1006536358672457692753049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2684096956459887180674797 1006536358672457692753049)
            ·
              refine ⟨754902269004343269564787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006536358672457692753049 754902269004343269564787)
              ·
                refine ⟨1132353403506514904347181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754902269004343269564787 1132353403506514904347181)
                ·
                  refine ⟨424632526314943089130193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1132353403506514904347181 424632526314943089130193)
                  ·
                    refine ⟨318474394736207316847645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 424632526314943089130193 318474394736207316847645)
                    ·
                      refine ⟨119427898026077743817867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 318474394736207316847645 119427898026077743817867)
                      ·
                        rfl

theorem cell23_232585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2, 3].length) (baseStart_232585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232585 prefixEnd_232585 := by exact prefixLift 232585
  have htrace : WordTrace (prefixWord ++ tailWord_232585) baseStart_232585 baseEnd_232585 := by
    simpa [prefixWord, tailWord_232585, baseEnd_232585] using wordTrace_append hprefix tailTrace_232585
  have hstable : (prefixWord ++ tailWord_232585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232585).length < 2 ^ (prefixWord ++ tailWord_232585).sum := by decide
  have hdescent : baseEnd_232585 < baseStart_232585 := by decide
  rcases family_descends (prefixWord ++ tailWord_232585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232599 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 1, 1, 4]
def baseStart_232599 : Nat := 118140960795 + 232599 * 2 ^ 59
def prefixEnd_232599 : Nat := 4983230072969 + 3 ^ 40 * 232599 * 2
def baseEnd_232599 : Nat := 119435086755240689042803

theorem tailTrace_232599 : CollatzResearch.WordTrace tailWord_232599 prefixEnd_232599 119435086755240689042803 := by
  unfold tailWord_232599
  simp only [CollatzResearch.WordTrace]
  refine ⟨8483582484341022591660851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5655721656227348394440567 8483582484341022591660851)
  ·
    refine ⟨12725373726511533887491277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8483582484341022591660851 12725373726511533887491277)
    ·
      refine ⟨4772015147441825207809229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12725373726511533887491277 4772015147441825207809229)
      ·
        refine ⟨1789505680290684452928461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4772015147441825207809229 1789505680290684452928461)
        ·
          refine ⟨671064630109006669848173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1789505680290684452928461 671064630109006669848173)
          ·
            refine ⟨251649236290877501193065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 671064630109006669848173 251649236290877501193065)
            ·
              refine ⟨188736927218158125894799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251649236290877501193065 188736927218158125894799)
              ·
                refine ⟨283105390827237188842199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188736927218158125894799 283105390827237188842199)
                ·
                  refine ⟨424658086240855783263299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283105390827237188842199 424658086240855783263299)
                  ·
                    refine ⟨636987129361283674894949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 424658086240855783263299 636987129361283674894949)
                    ·
                      refine ⟨119435086755240689042803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 636987129361283674894949 119435086755240689042803)
                      ·
                        rfl

theorem cell23_232599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_232599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232599 prefixEnd_232599 := by exact prefixLift 232599
  have htrace : WordTrace (prefixWord ++ tailWord_232599) baseStart_232599 baseEnd_232599 := by
    simpa [prefixWord, tailWord_232599, baseEnd_232599] using wordTrace_append hprefix tailTrace_232599
  have hstable : (prefixWord ++ tailWord_232599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232599).length < 2 ^ (prefixWord ++ tailWord_232599).sum := by decide
  have hdescent : baseEnd_232599 < baseStart_232599 := by decide
  rcases family_descends (prefixWord ++ tailWord_232599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232648 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 1, 8]
def baseStart_232648 : Nat := 118140960795 + 232648 * 2 ^ 59
def prefixEnd_232648 : Nat := 4983230072969 + 3 ^ 40 * 232648 * 2
def baseEnd_232648 : Nat := 39820082435770332443359

theorem tailTrace_232648 : CollatzResearch.WordTrace tailWord_232648 prefixEnd_232648 39820082435770332443359 := by
  unfold tailWord_232648
  simp only [CollatzResearch.WordTrace]
  refine ⟨4242684830581751980097299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5656913107442335973463065 4242684830581751980097299)
  ·
    refine ⟨6364027245872627970145949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4242684830581751980097299 6364027245872627970145949)
    ·
      refine ⟨2386510217202235488804731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6364027245872627970145949 2386510217202235488804731)
      ·
        refine ⟨3579765325803353233207097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2386510217202235488804731 3579765325803353233207097)
        ·
          refine ⟨2684823994352514924905323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3579765325803353233207097 2684823994352514924905323)
          ·
            refine ⟨4027235991528772387357985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684823994352514924905323 4027235991528772387357985)
            ·
              refine ⟨3020426993646579290518489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4027235991528772387357985 3020426993646579290518489)
              ·
                refine ⟨2265320245234934467888867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3020426993646579290518489 2265320245234934467888867)
                ·
                  refine ⟨3397980367852401701833301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265320245234934467888867 3397980367852401701833301)
                  ·
                    refine ⟨39820082435770332443359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3397980367852401701833301 39820082435770332443359)
                    ·
                      rfl

theorem cell23_232648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_232648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232648 prefixEnd_232648 := by exact prefixLift 232648
  have htrace : WordTrace (prefixWord ++ tailWord_232648) baseStart_232648 baseEnd_232648 := by
    simpa [prefixWord, tailWord_232648, baseEnd_232648] using wordTrace_append hprefix tailTrace_232648
  have hstable : (prefixWord ++ tailWord_232648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232648).length < 2 ^ (prefixWord ++ tailWord_232648).sum := by decide
  have hdescent : baseEnd_232648 < baseStart_232648 := by decide
  rcases family_descends (prefixWord ++ tailWord_232648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232706 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_232706 : Nat := 118140960795 + 232706 * 2 ^ 59
def prefixEnd_232706 : Nat := 4983230072969 + 3 ^ 40 * 232706 * 2
def baseEnd_232706 : Nat := 119490029185271770404811

theorem tailTrace_232706 : CollatzResearch.WordTrace tailWord_232706 prefixEnd_232706 119490029185271770404811 := by
  unfold tailWord_232706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121871273738344966451493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5658323396635586577203981 2121871273738344966451493)
  ·
    refine ⟨397850863825939681209655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2121871273738344966451493 397850863825939681209655)
    ·
      refine ⟨596776295738909521814483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397850863825939681209655 596776295738909521814483)
      ·
        refine ⟨895164443608364282721725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596776295738909521814483 895164443608364282721725)
        ·
          refine ⟨335686666353136606020647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 895164443608364282721725 335686666353136606020647)
          ·
            refine ⟨503529999529704909030971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335686666353136606020647 503529999529704909030971)
            ·
              refine ⟨755294999294557363546457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503529999529704909030971 755294999294557363546457)
              ·
                refine ⟨566471249470918022659843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755294999294557363546457 566471249470918022659843)
                ·
                  refine ⟨849706874206377033989765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566471249470918022659843 849706874206377033989765)
                  ·
                    refine ⟨159320038913695693873081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 849706874206377033989765 159320038913695693873081)
                    ·
                      refine ⟨119490029185271770404811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159320038913695693873081 119490029185271770404811)
                      ·
                        rfl

theorem cell23_232706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_232706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232706 prefixEnd_232706 := by exact prefixLift 232706
  have htrace : WordTrace (prefixWord ++ tailWord_232706) baseStart_232706 baseEnd_232706 := by
    simpa [prefixWord, tailWord_232706, baseEnd_232706] using wordTrace_append hprefix tailTrace_232706
  have hstable : (prefixWord ++ tailWord_232706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232706).length < 2 ^ (prefixWord ++ tailWord_232706).sum := by decide
  have hdescent : baseEnd_232706 < baseStart_232706 := by decide
  rcases family_descends (prefixWord ++ tailWord_232706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232732 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_232732 : Nat := 118140960795 + 232732 * 2 ^ 59
def prefixEnd_232732 : Nat := 4983230072969 + 3 ^ 40 * 232732 * 2
def baseEnd_232732 : Nat := 119503379682288668679691

theorem tailTrace_232732 : CollatzResearch.WordTrace tailWord_232732 prefixEnd_232732 119503379682288668679691 := by
  unfold tailWord_232732
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244216696429593153126225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5658955595239457537501633 4244216696429593153126225)
  ·
    refine ⟨3183162522322194864844669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4244216696429593153126225 3183162522322194864844669)
    ·
      refine ⟨1193685945870823074316751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3183162522322194864844669 1193685945870823074316751)
      ·
        refine ⟨1790528918806234611475127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193685945870823074316751 1790528918806234611475127)
        ·
          refine ⟨2685793378209351917212691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790528918806234611475127 2685793378209351917212691)
          ·
            refine ⟨4028690067314027875819037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685793378209351917212691 4028690067314027875819037)
            ·
              refine ⟨1510758775242760453432139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4028690067314027875819037 1510758775242760453432139)
              ·
                refine ⟨2266138162864140680148209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510758775242760453432139 2266138162864140680148209)
                ·
                  refine ⟨1699603622148105510111157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2266138162864140680148209 1699603622148105510111157)
                  ·
                    refine ⟨159337839576384891572921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1699603622148105510111157 159337839576384891572921)
                    ·
                      refine ⟨119503379682288668679691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159337839576384891572921 119503379682288668679691)
                      ·
                        rfl

theorem cell23_232732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_232732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232732 prefixEnd_232732 := by exact prefixLift 232732
  have htrace : WordTrace (prefixWord ++ tailWord_232732) baseStart_232732 baseEnd_232732 := by
    simpa [prefixWord, tailWord_232732, baseEnd_232732] using wordTrace_append hprefix tailTrace_232732
  have hstable : (prefixWord ++ tailWord_232732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232732).length < 2 ^ (prefixWord ++ tailWord_232732).sum := by decide
  have hdescent : baseEnd_232732 < baseStart_232732 := by decide
  rcases family_descends (prefixWord ++ tailWord_232732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232762 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2]
def baseStart_232762 : Nat := 118140960795 + 232762 * 2 ^ 59
def prefixEnd_232762 : Nat := 4983230072969 + 3 ^ 40 * 232762 * 2
def baseEnd_232762 : Nat := 119518784101923551304553

theorem tailTrace_232762 : CollatzResearch.WordTrace tailWord_232762 prefixEnd_232762 119518784101923551304553 := by
  unfold tailWord_232762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122381895687625357461135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5659685055167000953229693 2122381895687625357461135)
  ·
    refine ⟨3183572843531438036191703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2122381895687625357461135 3183572843531438036191703)
    ·
      refine ⟨4775359265297157054287555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3183572843531438036191703 4775359265297157054287555)
      ·
        refine ⟨7163038897945735581431333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4775359265297157054287555 7163038897945735581431333)
        ·
          refine ⟨1343069793364825421518375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7163038897945735581431333 1343069793364825421518375)
          ·
            refine ⟨2014604690047238132277563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343069793364825421518375 2014604690047238132277563)
            ·
              refine ⟨3021907035070857198416345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014604690047238132277563 3021907035070857198416345)
              ·
                refine ⟨2266430276303142898812259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3021907035070857198416345 2266430276303142898812259)
                ·
                  refine ⟨3399645414454714348218389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266430276303142898812259 3399645414454714348218389)
                  ·
                    refine ⟨159358378802564735072737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3399645414454714348218389 159358378802564735072737)
                    ·
                      refine ⟨119518784101923551304553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159358378802564735072737 119518784101923551304553)
                      ·
                        rfl

theorem cell23_232762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_232762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232762 prefixEnd_232762 := by exact prefixLift 232762
  have htrace : WordTrace (prefixWord ++ tailWord_232762) baseStart_232762 baseEnd_232762 := by
    simpa [prefixWord, tailWord_232762, baseEnd_232762] using wordTrace_append hprefix tailTrace_232762
  have hstable : (prefixWord ++ tailWord_232762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232762).length < 2 ^ (prefixWord ++ tailWord_232762).sum := by decide
  have hdescent : baseEnd_232762 < baseStart_232762 := by decide
  rcases family_descends (prefixWord ++ tailWord_232762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232774 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_232774 : Nat := 118140960795 + 232774 * 2 ^ 59
def prefixEnd_232774 : Nat := 4983230072969 + 3 ^ 40 * 232774 * 2
def baseEnd_232774 : Nat := 119524945869777504354499

theorem tailTrace_232774 : CollatzResearch.WordTrace tailWord_232774 prefixEnd_232774 119524945869777504354499 := by
  unfold tailWord_232774
  simp only [CollatzResearch.WordTrace]
  refine ⟨265311414334594608727543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5659976839138018319520917 265311414334594608727543)
  ·
    refine ⟨397967121501891913091315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265311414334594608727543 397967121501891913091315)
    ·
      refine ⟨596950682252837869636973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397967121501891913091315 596950682252837869636973)
      ·
        refine ⟨223856505844814201113865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596950682252837869636973 223856505844814201113865)
        ·
          refine ⟨167892379383610650835399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223856505844814201113865 167892379383610650835399)
          ·
            refine ⟨251838569075415976253099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167892379383610650835399 251838569075415976253099)
            ·
              refine ⟨377757853613123964379649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251838569075415976253099 377757853613123964379649)
              ·
                refine ⟨283318390209842973284737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377757853613123964379649 283318390209842973284737)
                ·
                  refine ⟨212488792657382229963553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283318390209842973284737 212488792657382229963553)
                  ·
                    refine ⟨159366594493036672472665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212488792657382229963553 159366594493036672472665)
                    ·
                      refine ⟨119524945869777504354499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159366594493036672472665 119524945869777504354499)
                      ·
                        rfl

theorem cell23_232774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_232774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232774 prefixEnd_232774 := by exact prefixLift 232774
  have htrace : WordTrace (prefixWord ++ tailWord_232774) baseStart_232774 baseEnd_232774 := by
    simpa [prefixWord, tailWord_232774, baseEnd_232774] using wordTrace_append hprefix tailTrace_232774
  have hstable : (prefixWord ++ tailWord_232774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232774).length < 2 ^ (prefixWord ++ tailWord_232774).sum := by decide
  have hdescent : baseEnd_232774 < baseStart_232774 := by decide
  rcases family_descends (prefixWord ++ tailWord_232774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232775 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_232775 : Nat := 118140960795 + 232775 * 2 ^ 59
def prefixEnd_232775 : Nat := 4983230072969 + 3 ^ 40 * 232775 * 2
def baseEnd_232775 : Nat := 119525459350432000441993

theorem tailTrace_232775 : CollatzResearch.WordTrace tailWord_232775 prefixEnd_232775 119525459350432000441993 := by
  unfold tailWord_232775
  simp only [CollatzResearch.WordTrace]
  refine ⟨8490001731703404650067779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5660001154468936433378519 8490001731703404650067779)
  ·
    refine ⟨12735002597555106975101669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8490001731703404650067779 12735002597555106975101669)
    ·
      refine ⟨2387812987041582557831563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12735002597555106975101669 2387812987041582557831563)
      ·
        refine ⟨3581719480562373836747345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387812987041582557831563 3581719480562373836747345)
        ·
          refine ⟨2686289610421780377560509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3581719480562373836747345 2686289610421780377560509)
          ·
            refine ⟨1007358603908167641585191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2686289610421780377560509 1007358603908167641585191)
            ·
              refine ⟨1511037905862251462377787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007358603908167641585191 1511037905862251462377787)
              ·
                refine ⟨2266556858793377193566681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511037905862251462377787 2266556858793377193566681)
                ·
                  refine ⟨1699917644095032895175011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2266556858793377193566681 1699917644095032895175011)
                  ·
                    refine ⟨2549876466142549342762517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1699917644095032895175011 2549876466142549342762517)
                    ·
                      refine ⟨119525459350432000441993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2549876466142549342762517 119525459350432000441993)
                      ·
                        rfl

theorem cell23_232775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_232775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232775 prefixEnd_232775 := by exact prefixLift 232775
  have htrace : WordTrace (prefixWord ++ tailWord_232775) baseStart_232775 baseEnd_232775 := by
    simpa [prefixWord, tailWord_232775, baseEnd_232775] using wordTrace_append hprefix tailTrace_232775
  have hstable : (prefixWord ++ tailWord_232775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232775).length < 2 ^ (prefixWord ++ tailWord_232775).sum := by decide
  have hdescent : baseEnd_232775 < baseStart_232775 := by decide
  rcases family_descends (prefixWord ++ tailWord_232775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232782 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_232782 : Nat := 118140960795 + 232782 * 2 ^ 59
def prefixEnd_232782 : Nat := 4983230072969 + 3 ^ 40 * 232782 * 2
def baseEnd_232782 : Nat := 119529053715013473054461

theorem tailTrace_232782 : CollatzResearch.WordTrace tailWord_232782 prefixEnd_232782 119529053715013473054461 := by
  unfold tailWord_232782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061282130334755605696575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5660171361785363230381733 1061282130334755605696575)
  ·
    refine ⟨1591923195502133408544863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1061282130334755605696575 1591923195502133408544863)
    ·
      refine ⟨2387884793253200112817295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1591923195502133408544863 2387884793253200112817295)
      ·
        refine ⟨3581827189879800169225943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387884793253200112817295 3581827189879800169225943)
        ·
          refine ⟨5372740784819700253838915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3581827189879800169225943 5372740784819700253838915)
          ·
            refine ⟨8059111177229550380758373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5372740784819700253838915 8059111177229550380758373)
            ·
              refine ⟨1511083345730540696392195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8059111177229550380758373 1511083345730540696392195)
              ·
                refine ⟨2266625018595811044588293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511083345730540696392195 2266625018595811044588293)
                ·
                  refine ⟨424992190986714570860305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266625018595811044588293 424992190986714570860305)
                  ·
                    refine ⟨318744143240035928145229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 424992190986714570860305 318744143240035928145229)
                    ·
                      refine ⟨119529053715013473054461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 318744143240035928145229 119529053715013473054461)
                      ·
                        rfl

theorem cell23_232782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_232782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232782 prefixEnd_232782 := by exact prefixLift 232782
  have htrace : WordTrace (prefixWord ++ tailWord_232782) baseStart_232782 baseEnd_232782 := by
    simpa [prefixWord, tailWord_232782, baseEnd_232782] using wordTrace_append hprefix tailTrace_232782
  have hstable : (prefixWord ++ tailWord_232782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232782).length < 2 ^ (prefixWord ++ tailWord_232782).sum := by decide
  have hdescent : baseEnd_232782 < baseStart_232782 := by decide
  rcases family_descends (prefixWord ++ tailWord_232782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232785 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 8]
def baseStart_232785 : Nat := 118140960795 + 232785 * 2 ^ 59
def prefixEnd_232785 : Nat := 4983230072969 + 3 ^ 40 * 232785 * 2
def baseEnd_232785 : Nat := 13281177128552995701883

theorem tailTrace_232785 : CollatzResearch.WordTrace tailWord_232785 prefixEnd_232785 13281177128552995701883 := by
  unfold tailWord_232785
  simp only [CollatzResearch.WordTrace]
  refine ⟨8490366461667176357931809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5660244307778117571954539 8490366461667176357931809)
  ·
    refine ⟨6367774846250382268448857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8490366461667176357931809 6367774846250382268448857)
    ·
      refine ⟨4775831134687786701336643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6367774846250382268448857 4775831134687786701336643)
      ·
        refine ⟨7163746702031680052004965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4775831134687786701336643 7163746702031680052004965)
        ·
          refine ⟨1343202506630940009750931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7163746702031680052004965 1343202506630940009750931)
          ·
            refine ⟨2014803759946410014626397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343202506630940009750931 2014803759946410014626397)
            ·
              refine ⟨755551409979903755484899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2014803759946410014626397 755551409979903755484899)
              ·
                refine ⟨1133327114969855633227349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755551409979903755484899 1133327114969855633227349)
                ·
                  refine ⟨13281177128552995701883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1133327114969855633227349 13281177128552995701883)
                  ·
                    rfl

theorem cell23_232785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 8].length) (baseStart_232785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232785 prefixEnd_232785 := by exact prefixLift 232785
  have htrace : WordTrace (prefixWord ++ tailWord_232785) baseStart_232785 baseEnd_232785 := by
    simpa [prefixWord, tailWord_232785, baseEnd_232785] using wordTrace_append hprefix tailTrace_232785
  have hstable : (prefixWord ++ tailWord_232785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232785).length < 2 ^ (prefixWord ++ tailWord_232785).sum := by decide
  have hdescent : baseEnd_232785 < baseStart_232785 := by decide
  rcases family_descends (prefixWord ++ tailWord_232785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232789 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_232789 : Nat := 118140960795 + 232789 * 2 ^ 59
def prefixEnd_232789 : Nat := 4983230072969 + 3 ^ 40 * 232789 * 2
def baseEnd_232789 : Nat := 39844216026531648555643

theorem tailTrace_232789 : CollatzResearch.WordTrace tailWord_232789 prefixEnd_232789 39844216026531648555643 := by
  unfold tailWord_232789
  simp only [CollatzResearch.WordTrace]
  refine ⟨8490512353652685041077421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5660341569101790027384947 8490512353652685041077421)
  ·
    refine ⟨3183942132619756890404033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8490512353652685041077421 3183942132619756890404033)
    ·
      refine ⟨2387956599464817667803025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3183942132619756890404033 2387956599464817667803025)
      ·
        refine ⟨1790967449598613250852269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2387956599464817667803025 1790967449598613250852269)
        ·
          refine ⟨671612793599479969069601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1790967449598613250852269 671612793599479969069601)
          ·
            refine ⟨503709595199609976802201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671612793599479969069601 503709595199609976802201)
            ·
              refine ⟨377782196399707482601651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503709595199609976802201 377782196399707482601651)
              ·
                refine ⟨566673294599561223902477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377782196399707482601651 566673294599561223902477)
                ·
                  refine ⟨212502485474835458963429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566673294599561223902477 212502485474835458963429)
                  ·
                    refine ⟨39844216026531648555643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212502485474835458963429 39844216026531648555643)
                    ·
                      rfl

theorem cell23_232789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_232789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232789 prefixEnd_232789 := by exact prefixLift 232789
  have htrace : WordTrace (prefixWord ++ tailWord_232789) baseStart_232789 baseEnd_232789 := by
    simpa [prefixWord, tailWord_232789, baseEnd_232789] using wordTrace_append hprefix tailTrace_232789
  have hstable : (prefixWord ++ tailWord_232789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232789).length < 2 ^ (prefixWord ++ tailWord_232789).sum := by decide
  have hdescent : baseEnd_232789 < baseStart_232789 := by decide
  rcases family_descends (prefixWord ++ tailWord_232789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232805 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_232805 : Nat := 118140960795 + 232805 * 2 ^ 59
def prefixEnd_232805 : Nat := 4983230072969 + 3 ^ 40 * 232805 * 2
def baseEnd_232805 : Nat := 119540863770066883066855

theorem tailTrace_232805 : CollatzResearch.WordTrace tailWord_232805 prefixEnd_232805 119540863770066883066855 := by
  unfold tailWord_232805
  simp only [CollatzResearch.WordTrace]
  refine ⟨8491095921594719773659869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5660730614396479849106579 8491095921594719773659869)
  ·
    refine ⟨3184160970598019915122451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8491095921594719773659869 3184160970598019915122451)
    ·
      refine ⟨4776241455897029872683677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3184160970598019915122451 4776241455897029872683677)
      ·
        refine ⟨1791090545961386202256379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4776241455897029872683677 1791090545961386202256379)
        ·
          refine ⟨2686635818942079303384569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791090545961386202256379 2686635818942079303384569)
          ·
            refine ⟨2014976864206559477538427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2686635818942079303384569 2014976864206559477538427)
            ·
              refine ⟨3022465296309839216307641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014976864206559477538427 3022465296309839216307641)
              ·
                refine ⟨2266848972232379412230731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022465296309839216307641 2266848972232379412230731)
                ·
                  refine ⟨3400273458348569118346097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266848972232379412230731 3400273458348569118346097)
                  ·
                    refine ⟨2550205093761426838759573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3400273458348569118346097 2550205093761426838759573)
                    ·
                      refine ⟨119540863770066883066855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2550205093761426838759573 119540863770066883066855)
                      ·
                        rfl

theorem cell23_232805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_232805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232805 prefixEnd_232805 := by exact prefixLift 232805
  have htrace : WordTrace (prefixWord ++ tailWord_232805) baseStart_232805 baseEnd_232805 := by
    simpa [prefixWord, tailWord_232805, baseEnd_232805] using wordTrace_append hprefix tailTrace_232805
  have hstable : (prefixWord ++ tailWord_232805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232805).length < 2 ^ (prefixWord ++ tailWord_232805).sum := by decide
  have hdescent : baseEnd_232805 < baseStart_232805 := by decide
  rcases family_descends (prefixWord ++ tailWord_232805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232839 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 4, 3, 2]
def baseStart_232839 : Nat := 118140960795 + 232839 * 2 ^ 59
def prefixEnd_232839 : Nat := 4983230072969 + 3 ^ 40 * 232839 * 2
def baseEnd_232839 : Nat := 119558322112319750041699

theorem tailTrace_232839 : CollatzResearch.WordTrace tailWord_232839 prefixEnd_232839 119558322112319750041699 := by
  unfold tailWord_232839
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492336003471543580397571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5661557335647695720265047 8492336003471543580397571)
  ·
    refine ⟨12738504005207315370596357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8492336003471543580397571 12738504005207315370596357)
    ·
      refine ⟨2388469500976371631986817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12738504005207315370596357 2388469500976371631986817)
      ·
        refine ⟨1791352125732278723990113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2388469500976371631986817 1791352125732278723990113)
        ·
          refine ⟨1343514094299209042992585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1791352125732278723990113 1343514094299209042992585)
          ·
            refine ⟨1007635570724406782244439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1343514094299209042992585 1007635570724406782244439)
            ·
              refine ⟨1511453356086610173366659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007635570724406782244439 1511453356086610173366659)
              ·
                refine ⟨2267180034129915260049989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511453356086610173366659 2267180034129915260049989)
                ·
                  refine ⟨425096256399359111259373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2267180034129915260049989 425096256399359111259373)
                  ·
                    refine ⟨159411096149759666722265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 425096256399359111259373 159411096149759666722265)
                    ·
                      refine ⟨119558322112319750041699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159411096149759666722265 119558322112319750041699)
                      ·
                        rfl

theorem cell23_232839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_232839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232839 prefixEnd_232839 := by exact prefixLift 232839
  have htrace : WordTrace (prefixWord ++ tailWord_232839) baseStart_232839 baseEnd_232839 := by
    simpa [prefixWord, tailWord_232839, baseEnd_232839] using wordTrace_append hprefix tailTrace_232839
  have hstable : (prefixWord ++ tailWord_232839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232839).length < 2 ^ (prefixWord ++ tailWord_232839).sum := by decide
  have hdescent : baseEnd_232839 < baseStart_232839 := by decide
  rcases family_descends (prefixWord ++ tailWord_232839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232866 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_232866 : Nat := 118140960795 + 232866 * 2 ^ 59
def prefixEnd_232866 : Nat := 4983230072969 + 3 ^ 40 * 232866 * 2
def baseEnd_232866 : Nat := 39857395363330381468025

theorem tailTrace_232866 : CollatzResearch.WordTrace tailWord_232866 prefixEnd_232866 39857395363330381468025 := by
  unfold tailWord_232866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2123330193593431797907613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5662213849582484794420301 2123330193593431797907613)
  ·
    refine ⟨796248822597536924215355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2123330193593431797907613 796248822597536924215355)
    ·
      refine ⟨1194373233896305386323033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796248822597536924215355 1194373233896305386323033)
      ·
        refine ⟨895779925422229039742275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1194373233896305386323033 895779925422229039742275)
        ·
          refine ⟨1343669888133343559613413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895779925422229039742275 1343669888133343559613413)
          ·
            refine ⟨251938104025001917427515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1343669888133343559613413 251938104025001917427515)
            ·
              refine ⟨377907156037502876141273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251938104025001917427515 377907156037502876141273)
              ·
                refine ⟨283430367028127157105955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377907156037502876141273 283430367028127157105955)
                ·
                  refine ⟨425145550542190735658933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283430367028127157105955 425145550542190735658933)
                  ·
                    refine ⟨39857395363330381468025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 425145550542190735658933 39857395363330381468025)
                    ·
                      rfl

theorem cell23_232866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_232866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232866 prefixEnd_232866 := by exact prefixLift 232866
  have htrace : WordTrace (prefixWord ++ tailWord_232866) baseStart_232866 baseEnd_232866 := by
    simpa [prefixWord, tailWord_232866, baseEnd_232866] using wordTrace_append hprefix tailTrace_232866
  have hstable : (prefixWord ++ tailWord_232866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232866).length < 2 ^ (prefixWord ++ tailWord_232866).sum := by decide
  have hdescent : baseEnd_232866 < baseStart_232866 := by decide
  rcases family_descends (prefixWord ++ tailWord_232866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232892 : List Nat := [2, 2, 2, 4, 2, 11]
def baseStart_232892 : Nat := 118140960795 + 232892 * 2 ^ 59
def prefixEnd_232892 : Nat := 4983230072969 + 3 ^ 40 * 232892 * 2
def baseEnd_232892 : Nat := 492121549740773838185

theorem tailTrace_232892 : CollatzResearch.WordTrace tailWord_232892 prefixEnd_232892 492121549740773838185 := by
  unfold tailWord_232892
  simp only [CollatzResearch.WordTrace]
  refine ⟨4247134536139766816038465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5662846048186355754717953 4247134536139766816038465)
  ·
    refine ⟨3185350902104825112028849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4247134536139766816038465 3185350902104825112028849)
    ·
      refine ⟨2389013176578618834021637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3185350902104825112028849 2389013176578618834021637)
      ·
        refine ⟨447939970608491031379057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2389013176578618834021637 447939970608491031379057)
        ·
          refine ⟨335954977956368273534293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447939970608491031379057 335954977956368273534293)
          ·
            refine ⟨492121549740773838185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 335954977956368273534293 492121549740773838185)
            ·
              rfl

theorem cell23_232892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 11].length) (baseStart_232892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232892 prefixEnd_232892 := by exact prefixLift 232892
  have htrace : WordTrace (prefixWord ++ tailWord_232892) baseStart_232892 baseEnd_232892 := by
    simpa [prefixWord, tailWord_232892, baseEnd_232892] using wordTrace_append hprefix tailTrace_232892
  have hstable : (prefixWord ++ tailWord_232892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232892).length < 2 ^ (prefixWord ++ tailWord_232892).sum := by decide
  have hdescent : baseEnd_232892 < baseStart_232892 := by decide
  rcases family_descends (prefixWord ++ tailWord_232892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232903 : List Nat := [1, 1, 4, 1, 1, 3, 3, 4, 1, 2, 2]
def baseStart_232903 : Nat := 118140960795 + 232903 * 2 ^ 59
def prefixEnd_232903 : Nat := 4983230072969 + 3 ^ 40 * 232903 * 2
def baseEnd_232903 : Nat := 119591184874207499641405

theorem tailTrace_232903 : CollatzResearch.WordTrace tailWord_232903 prefixEnd_232903 119591184874207499641405 := by
  unfold tailWord_232903
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494670275239682510727363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5663113516826455007151575 8494670275239682510727363)
  ·
    refine ⟨12742005412859523766091045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8494670275239682510727363 12742005412859523766091045)
    ·
      refine ⟨2389126014911160706142071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12742005412859523766091045 2389126014911160706142071)
      ·
        refine ⟨3583689022366741059213107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2389126014911160706142071 3583689022366741059213107)
        ·
          refine ⟨5375533533550111588819661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583689022366741059213107 5375533533550111588819661)
          ·
            refine ⟨2015825075081291845807373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5375533533550111588819661 2015825075081291845807373)
            ·
              refine ⟨755934403155484442177765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2015825075081291845807373 755934403155484442177765)
              ·
                refine ⟨141737700591653332908331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 755934403155484442177765 141737700591653332908331)
                ·
                  refine ⟨212606550887479999362497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141737700591653332908331 212606550887479999362497)
                  ·
                    refine ⟨159454913165609999521873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212606550887479999362497 159454913165609999521873)
                    ·
                      refine ⟨119591184874207499641405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159454913165609999521873 119591184874207499641405)
                      ·
                        rfl

theorem cell23_232903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_232903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232903 prefixEnd_232903 := by exact prefixLift 232903
  have htrace : WordTrace (prefixWord ++ tailWord_232903) baseStart_232903 baseEnd_232903 := by
    simpa [prefixWord, tailWord_232903, baseEnd_232903] using wordTrace_append hprefix tailTrace_232903
  have hstable : (prefixWord ++ tailWord_232903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232903).length < 2 ^ (prefixWord ++ tailWord_232903).sum := by decide
  have hdescent : baseEnd_232903 < baseStart_232903 := by decide
  rcases family_descends (prefixWord ++ tailWord_232903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232916 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_232916 : Nat := 118140960795 + 232916 * 2 ^ 59
def prefixEnd_232916 : Nat := 4983230072969 + 3 ^ 40 * 232916 * 2
def baseEnd_232916 : Nat := 119597860122715948778845

theorem tailTrace_232916 : CollatzResearch.WordTrace tailWord_232916 prefixEnd_232916 119597860122715948778845 := by
  unfold tailWord_232916
  simp only [CollatzResearch.WordTrace]
  refine ⟨4247572212096292865475301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5663429616128390487300401 4247572212096292865475301)
  ·
    refine ⟨796419789768054912276619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4247572212096292865475301 796419789768054912276619)
    ·
      refine ⟨1194629684652082368414929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796419789768054912276619 1194629684652082368414929)
      ·
        refine ⟨895972263489061776311197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1194629684652082368414929 895972263489061776311197)
        ·
          refine ⟨335989598808398166116699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 895972263489061776311197 335989598808398166116699)
          ·
            refine ⟨503984398212597249175049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335989598808398166116699 503984398212597249175049)
            ·
              refine ⟨377988298659447936881287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503984398212597249175049 377988298659447936881287)
              ·
                refine ⟨566982447989171905321931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377988298659447936881287 566982447989171905321931)
                ·
                  refine ⟨850473671983757857982897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566982447989171905321931 850473671983757857982897)
                  ·
                    refine ⟨637855253987818393487173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 850473671983757857982897 637855253987818393487173)
                    ·
                      refine ⟨119597860122715948778845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 637855253987818393487173 119597860122715948778845)
                      ·
                        rfl

theorem cell23_232916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_232916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232916 prefixEnd_232916 := by exact prefixLift 232916
  have htrace : WordTrace (prefixWord ++ tailWord_232916) baseStart_232916 baseEnd_232916 := by
    simpa [prefixWord, tailWord_232916, baseEnd_232916] using wordTrace_append hprefix tailTrace_232916
  have hstable : (prefixWord ++ tailWord_232916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232916).length < 2 ^ (prefixWord ++ tailWord_232916).sum := by decide
  have hdescent : baseEnd_232916 < baseStart_232916 := by decide
  rcases family_descends (prefixWord ++ tailWord_232916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232952 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 2, 6]
def baseStart_232952 : Nat := 118140960795 + 232952 * 2 ^ 59
def prefixEnd_232952 : Nat := 4983230072969 + 3 ^ 40 * 232952 * 2
def baseEnd_232952 : Nat := 39872115142092602642893

theorem tailTrace_232952 : CollatzResearch.WordTrace tailWord_232952 prefixEnd_232952 39872115142092602642893 := by
  unfold tailWord_232952
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248228726031081939630555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5664304968041442586174073 4248228726031081939630555)
  ·
    refine ⟨6372343089046622909445833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4248228726031081939630555 6372343089046622909445833)
    ·
      refine ⟨4779257316784967182084375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6372343089046622909445833 4779257316784967182084375)
      ·
        refine ⟨7168885975177450773126563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779257316784967182084375 7168885975177450773126563)
        ·
          refine ⟨10753328962766176159689845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7168885975177450773126563 10753328962766176159689845)
          ·
            refine ⟨1008124590259329014970923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10753328962766176159689845 1008124590259329014970923)
            ·
              refine ⟨1512186885388993522456385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008124590259329014970923 1512186885388993522456385)
              ·
                refine ⟨1134140164041745141842289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512186885388993522456385 1134140164041745141842289)
                ·
                  refine ⟨850605123031308856381717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1134140164041745141842289 850605123031308856381717)
                  ·
                    refine ⟨39872115142092602642893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 850605123031308856381717 39872115142092602642893)
                    ·
                      rfl

theorem cell23_232952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_232952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_232952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_232952 prefixEnd_232952 := by exact prefixLift 232952
  have htrace : WordTrace (prefixWord ++ tailWord_232952) baseStart_232952 baseEnd_232952 := by
    simpa [prefixWord, tailWord_232952, baseEnd_232952] using wordTrace_append hprefix tailTrace_232952
  have hstable : (prefixWord ++ tailWord_232952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232952).length < 2 ^ (prefixWord ++ tailWord_232952).sum := by decide
  have hdescent : baseEnd_232952 < baseStart_232952 := by decide
  rcases family_descends (prefixWord ++ tailWord_232952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233066 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_233066 : Nat := 118140960795 + 233066 * 2 ^ 59
def prefixEnd_233066 : Nat := 4983230072969 + 3 ^ 40 * 233066 * 2
def baseEnd_233066 : Nat := 119674882220890361903155

theorem tailTrace_233066 : CollatzResearch.WordTrace tailWord_233066 prefixEnd_233066 119674882220890361903155 := by
  unfold tailWord_233066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2125153843412290337227763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5667076915766107565940701 2125153843412290337227763)
  ·
    refine ⟨3187730765118435505841645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2125153843412290337227763 3187730765118435505841645)
    ·
      refine ⟨1195399036919413314690617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3187730765118435505841645 1195399036919413314690617)
      ·
        refine ⟨896549277689559986017963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1195399036919413314690617 896549277689559986017963)
        ·
          refine ⟨1344823916534339979026945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896549277689559986017963 1344823916534339979026945)
          ·
            refine ⟨1008617937400754984270209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344823916534339979026945 1008617937400754984270209)
            ·
              refine ⟨756463453050566238202657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008617937400754984270209 756463453050566238202657)
              ·
                refine ⟨567347589787924678651993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756463453050566238202657 567347589787924678651993)
                ·
                  refine ⟨425510692340943508988995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567347589787924678651993 425510692340943508988995)
                  ·
                    refine ⟨638266038511415263483493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 425510692340943508988995 638266038511415263483493)
                    ·
                      refine ⟨119674882220890361903155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 638266038511415263483493 119674882220890361903155)
                      ·
                        rfl

theorem cell23_233066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_233066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233066 prefixEnd_233066 := by exact prefixLift 233066
  have htrace : WordTrace (prefixWord ++ tailWord_233066) baseStart_233066 baseEnd_233066 := by
    simpa [prefixWord, tailWord_233066, baseEnd_233066] using wordTrace_append hprefix tailTrace_233066
  have hstable : (prefixWord ++ tailWord_233066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233066).length < 2 ^ (prefixWord ++ tailWord_233066).sum := by decide
  have hdescent : baseEnd_233066 < baseStart_233066 := by decide
  rcases family_descends (prefixWord ++ tailWord_233066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233159 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_233159 : Nat := 118140960795 + 233159 * 2 ^ 59
def prefixEnd_233159 : Nat := 4983230072969 + 3 ^ 40 * 233159 * 2
def baseEnd_233159 : Nat := 119722635921758498040227

theorem tailTrace_233159 : CollatzResearch.WordTrace tailWord_233159 prefixEnd_233159 119722635921758498040227 := by
  unfold tailWord_233159
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504007362312238232046531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5669338241541492154697687 8504007362312238232046531)
  ·
    refine ⟨12756011043468357348069797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8504007362312238232046531 12756011043468357348069797)
    ·
      refine ⟨2391752070650317002763087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12756011043468357348069797 2391752070650317002763087)
      ·
        refine ⟨3587628105975475504144631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391752070650317002763087 3587628105975475504144631)
        ·
          refine ⟨5381442158963213256216947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3587628105975475504144631 5381442158963213256216947)
          ·
            refine ⟨8072163238444819884325421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5381442158963213256216947 8072163238444819884325421)
            ·
              refine ⟨3027061214416807456622033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8072163238444819884325421 3027061214416807456622033)
              ·
                refine ⟨2270295910812605592466525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3027061214416807456622033 2270295910812605592466525)
                ·
                  refine ⟨851360966554727097174947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2270295910812605592466525 851360966554727097174947)
                  ·
                    refine ⟨1277041449832090645762421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851360966554727097174947 1277041449832090645762421)
                    ·
                      refine ⟨119722635921758498040227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1277041449832090645762421 119722635921758498040227)
                      ·
                        rfl

theorem cell23_233159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_233159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233159 prefixEnd_233159 := by exact prefixLift 233159
  have htrace : WordTrace (prefixWord ++ tailWord_233159) baseStart_233159 baseEnd_233159 := by
    simpa [prefixWord, tailWord_233159, baseEnd_233159] using wordTrace_append hprefix tailTrace_233159
  have hstable : (prefixWord ++ tailWord_233159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233159).length < 2 ^ (prefixWord ++ tailWord_233159).sum := by decide
  have hdescent : baseEnd_233159 < baseStart_233159 := by decide
  rcases family_descends (prefixWord ++ tailWord_233159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233166 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_233166 : Nat := 118140960795 + 233166 * 2 ^ 59
def prefixEnd_233166 : Nat := 4983230072969 + 3 ^ 40 * 233166 * 2
def baseEnd_233166 : Nat := 39908743428779990217565

theorem tailTrace_233166 : CollatzResearch.WordTrace tailWord_233166 prefixEnd_233166 39908743428779990217565 := by
  unfold tailWord_233166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063032834160859803443919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5669508448857918951700901 1063032834160859803443919)
  ·
    refine ⟨1594549251241289705165879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1063032834160859803443919 1594549251241289705165879)
    ·
      refine ⟨2391823876861934557748819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1594549251241289705165879 2391823876861934557748819)
      ·
        refine ⟨3587735815292901836623229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391823876861934557748819 3587735815292901836623229)
        ·
          refine ⟨1345400930734838188733711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3587735815292901836623229 1345400930734838188733711)
          ·
            refine ⟨2018101396102257283100567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345400930734838188733711 2018101396102257283100567)
            ·
              refine ⟨3027152094153385924650851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018101396102257283100567 3027152094153385924650851)
              ·
                refine ⟨4540728141230078886976277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027152094153385924650851 4540728141230078886976277)
                ·
                  refine ⟨212846631620159947827013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4540728141230078886976277 212846631620159947827013)
                  ·
                    refine ⟨39908743428779990217565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212846631620159947827013 39908743428779990217565)
                    ·
                      rfl

theorem cell23_233166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_233166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233166 prefixEnd_233166 := by exact prefixLift 233166
  have htrace : WordTrace (prefixWord ++ tailWord_233166) baseStart_233166 baseEnd_233166 := by
    simpa [prefixWord, tailWord_233166, baseEnd_233166] using wordTrace_append hprefix tailTrace_233166
  have hstable : (prefixWord ++ tailWord_233166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233166).length < 2 ^ (prefixWord ++ tailWord_233166).sum := by decide
  have hdescent : baseEnd_233166 < baseStart_233166 := by decide
  rcases family_descends (prefixWord ++ tailWord_233166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233176 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 1, 1, 5]
def baseStart_233176 : Nat := 118140960795 + 233176 * 2 ^ 59
def prefixEnd_233176 : Nat := 4983230072969 + 3 ^ 40 * 233176 * 2
def baseEnd_233176 : Nat := 119731365092884931527649

theorem tailTrace_233176 : CollatzResearch.WordTrace tailWord_233176 prefixEnd_233176 119731365092884931527649 := by
  unfold tailWord_233176
  simp only [CollatzResearch.WordTrace]
  refine ⟨4252313701625325067707691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5669751602167100090276921 4252313701625325067707691)
  ·
    refine ⟨6378470552437987601561537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4252313701625325067707691 6378470552437987601561537)
    ·
      refine ⟨4783852914328490701171153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6378470552437987601561537 4783852914328490701171153)
      ·
        refine ⟨3587889685746368025878365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4783852914328490701171153 3587889685746368025878365)
        ·
          refine ⟨1345458632154888009704387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3587889685746368025878365 1345458632154888009704387)
          ·
            refine ⟨2018187948232332014556581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345458632154888009704387 2018187948232332014556581)
            ·
              refine ⟨378410240293562252729359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2018187948232332014556581 378410240293562252729359)
              ·
                refine ⟨567615360440343379094039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378410240293562252729359 567615360440343379094039)
                ·
                  refine ⟨851423040660515068641059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567615360440343379094039 851423040660515068641059)
                  ·
                    refine ⟨1277134560990772602961589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851423040660515068641059 1277134560990772602961589)
                    ·
                      refine ⟨119731365092884931527649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1277134560990772602961589 119731365092884931527649)
                      ·
                        rfl

theorem cell23_233176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_233176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233176 prefixEnd_233176 := by exact prefixLift 233176
  have htrace : WordTrace (prefixWord ++ tailWord_233176) baseStart_233176 baseEnd_233176 := by
    simpa [prefixWord, tailWord_233176, baseEnd_233176] using wordTrace_append hprefix tailTrace_233176
  have hstable : (prefixWord ++ tailWord_233176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233176).length < 2 ^ (prefixWord ++ tailWord_233176).sum := by decide
  have hdescent : baseEnd_233176 < baseStart_233176 := by decide
  rcases family_descends (prefixWord ++ tailWord_233176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233199 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_233199 : Nat := 118140960795 + 233199 * 2 ^ 59
def prefixEnd_233199 : Nat := 4983230072969 + 3 ^ 40 * 233199 * 2
def baseEnd_233199 : Nat := 119743175147938341540043

theorem tailTrace_233199 : CollatzResearch.WordTrace tailWord_233199 prefixEnd_233199 119743175147938341540043 := by
  unfold tailWord_233199
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505466282167325063502651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5670310854778216709001767 8505466282167325063502651)
  ·
    refine ⟨12758199423250987595253977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8505466282167325063502651 12758199423250987595253977)
    ·
      refine ⟨9568649567438240696440483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12758199423250987595253977 9568649567438240696440483)
      ·
        refine ⟨14352974351157361044660725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9568649567438240696440483 14352974351157361044660725)
        ·
          refine ⟨1345591345421002597936943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14352974351157361044660725 1345591345421002597936943)
          ·
            refine ⟨2018387018131503896905415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345591345421002597936943 2018387018131503896905415)
            ·
              refine ⟨3027580527197255845358123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018387018131503896905415 3027580527197255845358123)
              ·
                refine ⟨4541370790795883768037185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027580527197255845358123 4541370790795883768037185)
                ·
                  refine ⟨3406028093096912826027889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4541370790795883768037185 3406028093096912826027889)
                  ·
                    refine ⟨2554521069822684619520917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3406028093096912826027889 2554521069822684619520917)
                    ·
                      refine ⟨119743175147938341540043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2554521069822684619520917 119743175147938341540043)
                      ·
                        rfl

theorem cell23_233199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_233199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233199 prefixEnd_233199 := by exact prefixLift 233199
  have htrace : WordTrace (prefixWord ++ tailWord_233199) baseStart_233199 baseEnd_233199 := by
    simpa [prefixWord, tailWord_233199, baseEnd_233199] using wordTrace_append hprefix tailTrace_233199
  have hstable : (prefixWord ++ tailWord_233199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233199).length < 2 ^ (prefixWord ++ tailWord_233199).sum := by decide
  have hdescent : baseEnd_233199 < baseStart_233199 := by decide
  rcases family_descends (prefixWord ++ tailWord_233199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233216 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 2, 7, 2]
def baseStart_233216 : Nat := 118140960795 + 233216 * 2 ^ 59
def prefixEnd_233216 : Nat := 4983230072969 + 3 ^ 40 * 233216 * 2
def baseEnd_233216 : Nat := 119751904319064775027465

theorem tailTrace_233216 : CollatzResearch.WordTrace tailWord_233216 prefixEnd_233216 119751904319064775027465 := by
  unfold tailWord_233216
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253043161552868483435751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5670724215403824644581001 4253043161552868483435751)
  ·
    refine ⟨6379564742329302725153627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4253043161552868483435751 6379564742329302725153627)
    ·
      refine ⟨9569347113493954087730441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6379564742329302725153627 9569347113493954087730441)
      ·
        refine ⟨7177010335120465565797831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9569347113493954087730441 7177010335120465565797831)
        ·
          refine ⟨10765515502680698348696747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177010335120465565797831 10765515502680698348696747)
          ·
            refine ⟨16148273254021047523045121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10765515502680698348696747 16148273254021047523045121)
            ·
              refine ⟨12111204940515785642283841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16148273254021047523045121 12111204940515785642283841)
              ·
                refine ⟨9083403705386839231712881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12111204940515785642283841 9083403705386839231712881)
                ·
                  refine ⟨6812552779040129423784661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9083403705386839231712881 6812552779040129423784661)
                  ·
                    refine ⟨159669205758753033369953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6812552779040129423784661 159669205758753033369953)
                    ·
                      refine ⟨119751904319064775027465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159669205758753033369953 119751904319064775027465)
                      ·
                        rfl

theorem cell23_233216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_233216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233216 prefixEnd_233216 := by exact prefixLift 233216
  have htrace : WordTrace (prefixWord ++ tailWord_233216) baseStart_233216 baseEnd_233216 := by
    simpa [prefixWord, tailWord_233216, baseEnd_233216] using wordTrace_append hprefix tailTrace_233216
  have hstable : (prefixWord ++ tailWord_233216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233216).length < 2 ^ (prefixWord ++ tailWord_233216).sum := by decide
  have hdescent : baseEnd_233216 < baseStart_233216 := by decide
  rcases family_descends (prefixWord ++ tailWord_233216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233219 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 5]
def baseStart_233219 : Nat := 118140960795 + 233219 * 2 ^ 59
def prefixEnd_233219 : Nat := 4983230072969 + 3 ^ 40 * 233219 * 2
def baseEnd_233219 : Nat := 119753444761028263289951

theorem tailTrace_233219 : CollatzResearch.WordTrace tailWord_233219 prefixEnd_233219 119753444761028263289951 := by
  unfold tailWord_233219
  simp only [CollatzResearch.WordTrace]
  refine ⟨8506195742094868479230711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5670797161396578986153807 8506195742094868479230711)
  ·
    refine ⟨12759293613142302718846067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8506195742094868479230711 12759293613142302718846067)
    ·
      refine ⟨19138940419713454078269101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12759293613142302718846067 19138940419713454078269101)
      ·
        refine ⟨7177102657392545279350913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19138940419713454078269101 7177102657392545279350913)
        ·
          refine ⟨5382826993044408959513185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7177102657392545279350913 5382826993044408959513185)
          ·
            refine ⟨4037120244783306719634889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5382826993044408959513185 4037120244783306719634889)
            ·
              refine ⟨3027840183587480039726167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4037120244783306719634889 3027840183587480039726167)
              ·
                refine ⟨4541760275381220059589251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027840183587480039726167 4541760275381220059589251)
                ·
                  refine ⟨6812640413071830089383877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4541760275381220059589251 6812640413071830089383877)
                  ·
                    refine ⟨1277370077450968141759477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6812640413071830089383877 1277370077450968141759477)
                    ·
                      refine ⟨119753444761028263289951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1277370077450968141759477 119753444761028263289951)
                      ·
                        rfl

theorem cell23_233219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_233219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233219 prefixEnd_233219 := by exact prefixLift 233219
  have htrace : WordTrace (prefixWord ++ tailWord_233219) baseStart_233219 baseEnd_233219 := by
    simpa [prefixWord, tailWord_233219, baseEnd_233219] using wordTrace_append hprefix tailTrace_233219
  have hstable : (prefixWord ++ tailWord_233219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233219).length < 2 ^ (prefixWord ++ tailWord_233219).sum := by decide
  have hdescent : baseEnd_233219 < baseStart_233219 := by decide
  rcases family_descends (prefixWord ++ tailWord_233219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233256 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 1, 8]
def baseStart_233256 : Nat := 118140960795 + 233256 * 2 ^ 59
def prefixEnd_233256 : Nat := 4983230072969 + 3 ^ 40 * 233256 * 2
def baseEnd_233256 : Nat := 39924147848414872842427

theorem tailTrace_233256 : CollatzResearch.WordTrace tailWord_233256 prefixEnd_233256 39924147848414872842427 := by
  unfold tailWord_233256
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253772621480411899163811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5671696828640549198885081 4253772621480411899163811)
  ·
    refine ⟨6380658932220617848745717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4253772621480411899163811 6380658932220617848745717)
    ·
      refine ⟨598186774895682923319911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6380658932220617848745717 598186774895682923319911)
      ·
        refine ⟨897280162343524384979867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598186774895682923319911 897280162343524384979867)
        ·
          refine ⟨1345920243515286577469801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897280162343524384979867 1345920243515286577469801)
          ·
            refine ⟨1009440182636464933102351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1345920243515286577469801 1009440182636464933102351)
            ·
              refine ⟨1514160273954697399653527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009440182636464933102351 1514160273954697399653527)
              ·
                refine ⟨2271240410932046099480291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514160273954697399653527 2271240410932046099480291)
                ·
                  refine ⟨3406860616398069149220437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271240410932046099480291 3406860616398069149220437)
                  ·
                    refine ⟨39924147848414872842427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3406860616398069149220437 39924147848414872842427)
                    ·
                      rfl

theorem cell23_233256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_233256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233256 prefixEnd_233256 := by exact prefixLift 233256
  have htrace : WordTrace (prefixWord ++ tailWord_233256) baseStart_233256 baseEnd_233256 := by
    simpa [prefixWord, tailWord_233256, baseEnd_233256] using wordTrace_append hprefix tailTrace_233256
  have hstable : (prefixWord ++ tailWord_233256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233256).length < 2 ^ (prefixWord ++ tailWord_233256).sum := by decide
  have hdescent : baseEnd_233256 < baseStart_233256 := by decide
  rcases family_descends (prefixWord ++ tailWord_233256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233297 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 2, 2, 2]
def baseStart_233297 : Nat := 118140960795 + 233297 * 2 ^ 59
def prefixEnd_233297 : Nat := 4983230072969 + 3 ^ 40 * 233297 * 2
def baseEnd_233297 : Nat := 119793496252078958114593

theorem tailTrace_233297 : CollatzResearch.WordTrace tailWord_233297 prefixEnd_233297 119793496252078958114593 := by
  unfold tailWord_233297
  simp only [CollatzResearch.WordTrace]
  refine ⟨8509040635812287800570145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5672693757208191867046763 8509040635812287800570145)
  ·
    refine ⟨6381780476859215850427609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8509040635812287800570145 6381780476859215850427609)
    ·
      refine ⟨4786335357644411887820707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6381780476859215850427609 4786335357644411887820707)
      ·
        refine ⟨7179503036466617831731061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4786335357644411887820707 7179503036466617831731061)
        ·
          refine ⟨673078409668745421724787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7179503036466617831731061 673078409668745421724787)
          ·
            refine ⟨1009617614503118132587181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673078409668745421724787 1009617614503118132587181)
            ·
              refine ⟨378606605438669299720193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1009617614503118132587181 378606605438669299720193)
              ·
                refine ⟨283954954079001974790145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378606605438669299720193 283954954079001974790145)
                ·
                  refine ⟨212966215559251481092609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283954954079001974790145 212966215559251481092609)
                  ·
                    refine ⟨159724661669438610819457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212966215559251481092609 159724661669438610819457)
                    ·
                      refine ⟨119793496252078958114593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159724661669438610819457 119793496252078958114593)
                      ·
                        rfl

theorem cell23_233297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_233297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233297 prefixEnd_233297 := by exact prefixLift 233297
  have htrace : WordTrace (prefixWord ++ tailWord_233297) baseStart_233297 baseEnd_233297 := by
    simpa [prefixWord, tailWord_233297, baseEnd_233297] using wordTrace_append hprefix tailTrace_233297
  have hstable : (prefixWord ++ tailWord_233297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233297).length < 2 ^ (prefixWord ++ tailWord_233297).sum := by decide
  have hdescent : baseEnd_233297 < baseStart_233297 := by decide
  rcases family_descends (prefixWord ++ tailWord_233297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233303 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 7]
def baseStart_233303 : Nat := 118140960795 + 233303 * 2 ^ 59
def prefixEnd_233303 : Nat := 4983230072969 + 3 ^ 40 * 233303 * 2
def baseEnd_233303 : Nat := 13310730792889548293285

theorem tailTrace_233303 : CollatzResearch.WordTrace tailWord_233303 prefixEnd_233303 13310730792889548293285 := by
  unfold tailWord_233303
  simp only [CollatzResearch.WordTrace]
  refine ⟨8509259473790550825288563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5672839649193700550192375 8509259473790550825288563)
  ·
    refine ⟨12763889210685826237932845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8509259473790550825288563 12763889210685826237932845)
    ·
      refine ⟨4786458454007184839224817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12763889210685826237932845 4786458454007184839224817)
      ·
        refine ⟨3589843840505388629418613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4786458454007184839224817 3589843840505388629418613)
        ·
          refine ⟨336547860047380184007995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3589843840505388629418613 336547860047380184007995)
          ·
            refine ⟨504821790071070276011993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336547860047380184007995 504821790071070276011993)
            ·
              refine ⟨378616342553302707008995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504821790071070276011993 378616342553302707008995)
              ·
                refine ⟨567924513829954060513493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378616342553302707008995 567924513829954060513493)
                ·
                  refine ⟨13310730792889548293285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 567924513829954060513493 13310730792889548293285)
                  ·
                    rfl

theorem cell23_233303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 7].length) (baseStart_233303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233303 prefixEnd_233303 := by exact prefixLift 233303
  have htrace : WordTrace (prefixWord ++ tailWord_233303) baseStart_233303 baseEnd_233303 := by
    simpa [prefixWord, tailWord_233303, baseEnd_233303] using wordTrace_append hprefix tailTrace_233303
  have hstable : (prefixWord ++ tailWord_233303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233303).length < 2 ^ (prefixWord ++ tailWord_233303).sum := by decide
  have hdescent : baseEnd_233303 < baseStart_233303 := by decide
  rcases family_descends (prefixWord ++ tailWord_233303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233333 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_233333 : Nat := 118140960795 + 233333 * 2 ^ 59
def prefixEnd_233333 : Nat := 4983230072969 + 3 ^ 40 * 233333 * 2
def baseEnd_233333 : Nat := 39937327185213605754809

theorem tailTrace_233333 : CollatzResearch.WordTrace tailWord_233333 prefixEnd_233333 39937327185213605754809 := by
  unfold tailWord_233333
  simp only [CollatzResearch.WordTrace]
  refine ⟨8510353663681865948880653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5673569109121243965920435 8510353663681865948880653)
  ·
    refine ⟨3191382623880699730830245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8510353663681865948880653 3191382623880699730830245)
    ·
      refine ⟨598384241977631199530671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3191382623880699730830245 598384241977631199530671)
      ·
        refine ⟨897576362966446799296007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598384241977631199530671 897576362966446799296007)
        ·
          refine ⟨1346364544449670198944011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897576362966446799296007 1346364544449670198944011)
          ·
            refine ⟨2019546816674505298416017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346364544449670198944011 2019546816674505298416017)
            ·
              refine ⟨1514660112505878973812013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019546816674505298416017 1514660112505878973812013)
              ·
                refine ⟨567997542189704615179505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1514660112505878973812013 567997542189704615179505)
                ·
                  refine ⟨425998156642278461384629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567997542189704615179505 425998156642278461384629)
                  ·
                    refine ⟨39937327185213605754809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 425998156642278461384629 39937327185213605754809)
                    ·
                      rfl

theorem cell23_233333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_233333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233333 prefixEnd_233333 := by exact prefixLift 233333
  have htrace : WordTrace (prefixWord ++ tailWord_233333) baseStart_233333 baseEnd_233333 := by
    simpa [prefixWord, tailWord_233333, baseEnd_233333] using wordTrace_append hprefix tailTrace_233333
  have hstable : (prefixWord ++ tailWord_233333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233333).length < 2 ^ (prefixWord ++ tailWord_233333).sum := by decide
  have hdescent : baseEnd_233333 < baseStart_233333 := by decide
  rcases family_descends (prefixWord ++ tailWord_233333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233353 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 4]
def baseStart_233353 : Nat := 118140960795 + 233353 * 2 ^ 59
def prefixEnd_233353 : Nat := 4983230072969 + 3 ^ 40 * 233353 * 2
def baseEnd_233353 : Nat := 119822251168730739014335

theorem tailTrace_233353 : CollatzResearch.WordTrace tailWord_233353 prefixEnd_233353 119822251168730739014335 := by
  unfold tailWord_233353
  simp only [CollatzResearch.WordTrace]
  refine ⟨8511083123609409364608713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5674055415739606243072475 8511083123609409364608713)
  ·
    refine ⟨6383312342707057023456535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8511083123609409364608713 6383312342707057023456535)
    ·
      refine ⟨9574968514060585535184803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383312342707057023456535 9574968514060585535184803)
      ·
        refine ⟨14362452771090878302777205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9574968514060585535184803 14362452771090878302777205)
        ·
          refine ⟨1346479947289769840885363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14362452771090878302777205 1346479947289769840885363)
          ·
            refine ⟨2019719920934654761328045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346479947289769840885363 2019719920934654761328045)
            ·
              refine ⟨757394970350495535498017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2019719920934654761328045 757394970350495535498017)
              ·
                refine ⟨568046227762871651623513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757394970350495535498017 568046227762871651623513)
                ·
                  refine ⟨426034670822153738717635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568046227762871651623513 426034670822153738717635)
                  ·
                    refine ⟨639052006233230608076453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 426034670822153738717635 639052006233230608076453)
                    ·
                      refine ⟨119822251168730739014335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 639052006233230608076453 119822251168730739014335)
                      ·
                        rfl

theorem cell23_233353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_233353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233353 prefixEnd_233353 := by exact prefixLift 233353
  have htrace : WordTrace (prefixWord ++ tailWord_233353) baseStart_233353 baseEnd_233353 := by
    simpa [prefixWord, tailWord_233353, baseEnd_233353] using wordTrace_append hprefix tailTrace_233353
  have hstable : (prefixWord ++ tailWord_233353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233353).length < 2 ^ (prefixWord ++ tailWord_233353).sum := by decide
  have hdescent : baseEnd_233353 < baseStart_233353 := by decide
  rcases family_descends (prefixWord ++ tailWord_233353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233447 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_233447 : Nat := 118140960795 + 233447 * 2 ^ 59
def prefixEnd_233447 : Nat := 4983230072969 + 3 ^ 40 * 233447 * 2
def baseEnd_233447 : Nat := 119870518350253371238903

theorem tailTrace_233447 : CollatzResearch.WordTrace tailWord_233447 prefixEnd_233447 119870518350253371238903 := by
  unfold tailWord_233447
  simp only [CollatzResearch.WordTrace]
  refine ⟨8514511585268863418530595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5676341056845908945687063 8514511585268863418530595)
  ·
    refine ⟨12771767377903295127795893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8514511585268863418530595 12771767377903295127795893)
    ·
      refine ⟨1197353191678433918230865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12771767377903295127795893 1197353191678433918230865)
      ·
        refine ⟨898014893758825438673149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1197353191678433918230865 898014893758825438673149)
        ·
          refine ⟨336755585159559539502431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 898014893758825438673149 336755585159559539502431)
          ·
            refine ⟨505133377739339309253647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336755585159559539502431 505133377739339309253647)
            ·
              refine ⟨757700066609008963880471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505133377739339309253647 757700066609008963880471)
              ·
                refine ⟨1136550099913513445820707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757700066609008963880471 1136550099913513445820707)
                ·
                  refine ⟨1704825149870270168731061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136550099913513445820707 1704825149870270168731061)
                  ·
                    refine ⟨159827357800337828318537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1704825149870270168731061 159827357800337828318537)
                    ·
                      refine ⟨119870518350253371238903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159827357800337828318537 119870518350253371238903)
                      ·
                        rfl

theorem cell23_233447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_233447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233447 prefixEnd_233447 := by exact prefixLift 233447
  have htrace : WordTrace (prefixWord ++ tailWord_233447) baseStart_233447 baseEnd_233447 := by
    simpa [prefixWord, tailWord_233447, baseEnd_233447] using wordTrace_append hprefix tailTrace_233447
  have hstable : (prefixWord ++ tailWord_233447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233447).length < 2 ^ (prefixWord ++ tailWord_233447).sum := by decide
  have hdescent : baseEnd_233447 < baseStart_233447 := by decide
  rcases family_descends (prefixWord ++ tailWord_233447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233454 : List Nat := [4, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_233454 : Nat := 118140960795 + 233454 * 2 ^ 59
def prefixEnd_233454 : Nat := 4983230072969 + 3 ^ 40 * 233454 * 2
def baseEnd_233454 : Nat := 119874112714834843851371

theorem tailTrace_233454 : CollatzResearch.WordTrace tailWord_233454 prefixEnd_233454 119874112714834843851371 := by
  unfold tailWord_233454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064345862030437951754427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5676511264162335742690277 1064345862030437951754427)
  ·
    refine ⟨1596518793045656927631641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1064345862030437951754427 1596518793045656927631641)
    ·
      refine ⟨1197389094784242695723731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1596518793045656927631641 1197389094784242695723731)
      ·
        refine ⟨1796083642176364043585597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197389094784242695723731 1796083642176364043585597)
        ·
          refine ⟨673531365816136516344599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1796083642176364043585597 673531365816136516344599)
          ·
            refine ⟨1010297048724204774516899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673531365816136516344599 1010297048724204774516899)
            ·
              refine ⟨1515445573086307161775349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010297048724204774516899 1515445573086307161775349)
              ·
                refine ⟨142073022476841296416439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1515445573086307161775349 142073022476841296416439)
                ·
                  refine ⟨213109533715261944624659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142073022476841296416439 213109533715261944624659)
                  ·
                    refine ⟨319664300572892916936989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213109533715261944624659 319664300572892916936989)
                    ·
                      refine ⟨119874112714834843851371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 319664300572892916936989 119874112714834843851371)
                      ·
                        rfl

theorem cell23_233454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_233454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233454 prefixEnd_233454 := by exact prefixLift 233454
  have htrace : WordTrace (prefixWord ++ tailWord_233454) baseStart_233454 baseEnd_233454 := by
    simpa [prefixWord, tailWord_233454, baseEnd_233454] using wordTrace_append hprefix tailTrace_233454
  have hstable : (prefixWord ++ tailWord_233454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233454).length < 2 ^ (prefixWord ++ tailWord_233454).sum := by decide
  have hdescent : baseEnd_233454 < baseStart_233454 := by decide
  rcases family_descends (prefixWord ++ tailWord_233454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233473 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_233473 : Nat := 118140960795 + 233473 * 2 ^ 59
def prefixEnd_233473 : Nat := 4983230072969 + 3 ^ 40 * 233473 * 2
def baseEnd_233473 : Nat := 119883868847270269513783

theorem tailTrace_233473 : CollatzResearch.WordTrace tailWord_233473 prefixEnd_233473 119883868847270269513783 := by
  unfold tailWord_233473
  simp only [CollatzResearch.WordTrace]
  refine ⟨8515459883174669858977073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5676973255449779905984715 8515459883174669858977073)
  ·
    refine ⟨6386594912381002394232805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8515459883174669858977073 6386594912381002394232805)
    ·
      refine ⟨1197486546071437948918651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6386594912381002394232805 1197486546071437948918651)
      ·
        refine ⟨1796229819107156923377977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197486546071437948918651 1796229819107156923377977)
        ·
          refine ⟨1347172364330367692533483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796229819107156923377977 1347172364330367692533483)
          ·
            refine ⟨2020758546495551538800225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347172364330367692533483 2020758546495551538800225)
            ·
              refine ⟨1515568909871663654100169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2020758546495551538800225 1515568909871663654100169)
              ·
                refine ⟨1136676682403747740575127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515568909871663654100169 1136676682403747740575127)
                ·
                  refine ⟨1705015023605621610862691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136676682403747740575127 1705015023605621610862691)
                  ·
                    refine ⟨2557522535408432416294037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1705015023605621610862691 2557522535408432416294037)
                    ·
                      refine ⟨119883868847270269513783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2557522535408432416294037 119883868847270269513783)
                      ·
                        rfl

theorem cell23_233473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_233473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233473 prefixEnd_233473 := by exact prefixLift 233473
  have htrace : WordTrace (prefixWord ++ tailWord_233473) baseStart_233473 baseEnd_233473 := by
    simpa [prefixWord, tailWord_233473, baseEnd_233473] using wordTrace_append hprefix tailTrace_233473
  have hstable : (prefixWord ++ tailWord_233473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233473).length < 2 ^ (prefixWord ++ tailWord_233473).sum := by decide
  have hdescent : baseEnd_233473 < baseStart_233473 := by decide
  rcases family_descends (prefixWord ++ tailWord_233473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233477 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 3, 2, 2]
def baseStart_233477 : Nat := 118140960795 + 233477 * 2 ^ 59
def prefixEnd_233477 : Nat := 4983230072969 + 3 ^ 40 * 233477 * 2
def baseEnd_233477 : Nat := 119885922769888253863765

theorem tailTrace_233477 : CollatzResearch.WordTrace tailWord_233477 prefixEnd_233477 119885922769888253863765 := by
  unfold tailWord_233477
  simp only [CollatzResearch.WordTrace]
  refine ⟨8515605775160178542122685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5677070516773452361415123 8515605775160178542122685)
  ·
    refine ⟨3193352165685066953296007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8515605775160178542122685 3193352165685066953296007)
    ·
      refine ⟨4790028248527600429944011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3193352165685066953296007 4790028248527600429944011)
      ·
        refine ⟨7185042372791400644916017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790028248527600429944011 7185042372791400644916017)
        ·
          refine ⟨5388781779593550483687013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7185042372791400644916017 5388781779593550483687013)
          ·
            refine ⟨1010396583673790715691315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5388781779593550483687013 1010396583673790715691315)
            ·
              refine ⟨1515594875510686073536973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010396583673790715691315 1515594875510686073536973)
              ·
                refine ⟨568348078316507277576365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1515594875510686073536973 568348078316507277576365)
                ·
                  refine ⟨213130529368690229091137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568348078316507277576365 213130529368690229091137)
                  ·
                    refine ⟨159847897026517671818353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213130529368690229091137 159847897026517671818353)
                    ·
                      refine ⟨119885922769888253863765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159847897026517671818353 119885922769888253863765)
                      ·
                        rfl

theorem cell23_233477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_233477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233477 prefixEnd_233477 := by exact prefixLift 233477
  have htrace : WordTrace (prefixWord ++ tailWord_233477) baseStart_233477 baseEnd_233477 := by
    simpa [prefixWord, tailWord_233477, baseEnd_233477] using wordTrace_append hprefix tailTrace_233477
  have hstable : (prefixWord ++ tailWord_233477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233477).length < 2 ^ (prefixWord ++ tailWord_233477).sum := by decide
  have hdescent : baseEnd_233477 < baseStart_233477 := by decide
  rcases family_descends (prefixWord ++ tailWord_233477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233478 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_233478 : Nat := 118140960795 + 233478 * 2 ^ 59
def prefixEnd_233478 : Nat := 4983230072969 + 3 ^ 40 * 233478 * 2
def baseEnd_233478 : Nat := 13320715138949194439029

theorem tailTrace_233478 : CollatzResearch.WordTrace tailWord_233478 prefixEnd_233478 13320715138949194439029 := by
  unfold tailWord_233478
  simp only [CollatzResearch.WordTrace]
  refine ⟨266113820254892366028409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5677094832104370475272725 266113820254892366028409)
  ·
    refine ⟨199585365191169274521307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266113820254892366028409 199585365191169274521307)
    ·
      refine ⟨299378047786753911781961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199585365191169274521307 299378047786753911781961)
      ·
        refine ⟨224533535840065433836471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299378047786753911781961 224533535840065433836471)
        ·
          refine ⟨336800303760098150754707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224533535840065433836471 336800303760098150754707)
          ·
            refine ⟨505200455640147226132061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336800303760098150754707 505200455640147226132061)
            ·
              refine ⟨189450170865055209799523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505200455640147226132061 189450170865055209799523)
              ·
                refine ⟨284175256297582814699285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189450170865055209799523 284175256297582814699285)
                ·
                  refine ⟨13320715138949194439029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 284175256297582814699285 13320715138949194439029)
                  ·
                    rfl

theorem cell23_233478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_233478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233478 prefixEnd_233478 := by exact prefixLift 233478
  have htrace : WordTrace (prefixWord ++ tailWord_233478) baseStart_233478 baseEnd_233478 := by
    simpa [prefixWord, tailWord_233478, baseEnd_233478] using wordTrace_append hprefix tailTrace_233478
  have hstable : (prefixWord ++ tailWord_233478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233478).length < 2 ^ (prefixWord ++ tailWord_233478).sum := by decide
  have hdescent : baseEnd_233478 < baseStart_233478 := by decide
  rcases family_descends (prefixWord ++ tailWord_233478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233500 : List Nat := [2, 2, 3, 1, 3, 1, 4, 7]
def baseStart_233500 : Nat := 118140960795 + 233500 * 2 ^ 59
def prefixEnd_233500 : Nat := 4983230072969 + 3 ^ 40 * 233500 * 2
def baseEnd_233500 : Nat := 4440656771294135699117

theorem tailTrace_233500 : CollatzResearch.WordTrace tailWord_233500 prefixEnd_233500 4440656771294135699117 := by
  unfold tailWord_233500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4258222327038426735104977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5677629769384568980139969 4258222327038426735104977)
  ·
    refine ⟨3193666745278820051328733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4258222327038426735104977 3193666745278820051328733)
    ·
      refine ⟨1197625029479557519248275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3193666745278820051328733 1197625029479557519248275)
      ·
        refine ⟨1796437544219336278872413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197625029479557519248275 1796437544219336278872413)
        ·
          refine ⟨673664079082251104577155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1796437544219336278872413 673664079082251104577155)
          ·
            refine ⟨1010496118623376656865733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673664079082251104577155 1010496118623376656865733)
            ·
              refine ⟨189468022241883123162325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1010496118623376656865733 189468022241883123162325)
              ·
                refine ⟨4440656771294135699117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 189468022241883123162325 4440656771294135699117)
                ·
                  rfl

theorem cell23_233500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 7].length) (baseStart_233500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233500 prefixEnd_233500 := by exact prefixLift 233500
  have htrace : WordTrace (prefixWord ++ tailWord_233500) baseStart_233500 baseEnd_233500 := by
    simpa [prefixWord, tailWord_233500, baseEnd_233500] using wordTrace_append hprefix tailTrace_233500
  have hstable : (prefixWord ++ tailWord_233500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233500).length < 2 ^ (prefixWord ++ tailWord_233500).sum := by decide
  have hdescent : baseEnd_233500 < baseStart_233500 := by decide
  rcases family_descends (prefixWord ++ tailWord_233500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233528 : List Nat := [2, 1, 2, 1, 6, 1, 3, 2, 1, 2, 2]
def baseStart_233528 : Nat := 118140960795 + 233528 * 2 ^ 59
def prefixEnd_233528 : Nat := 4983230072969 + 3 ^ 40 * 233528 * 2
def baseEnd_233528 : Nat := 119912110283267554326031

theorem tailTrace_233528 : CollatzResearch.WordTrace tailWord_233528 prefixEnd_233528 119912110283267554326031 := by
  unfold tailWord_233528
  simp only [CollatzResearch.WordTrace]
  refine ⟨4258732948987707126114619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5678310598650276168152825 4258732948987707126114619)
  ·
    refine ⟨6388099423481560689171929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4258732948987707126114619 6388099423481560689171929)
    ·
      refine ⟨4791074567611170516878947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6388099423481560689171929 4791074567611170516878947)
      ·
        refine ⟨7186611851416755775318421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4791074567611170516878947 7186611851416755775318421)
        ·
          refine ⟨336872430535160426968051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7186611851416755775318421 336872430535160426968051)
          ·
            refine ⟨505308645802740640452077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336872430535160426968051 505308645802740640452077)
            ·
              refine ⟨189490742176027740169529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505308645802740640452077 189490742176027740169529)
              ·
                refine ⟨142118056632020805127147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189490742176027740169529 142118056632020805127147)
                ·
                  refine ⟨213177084948031207690721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142118056632020805127147 213177084948031207690721)
                  ·
                    refine ⟨159882813711023405768041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213177084948031207690721 159882813711023405768041)
                    ·
                      refine ⟨119912110283267554326031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159882813711023405768041 119912110283267554326031)
                      ·
                        rfl

theorem cell23_233528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 1, 2, 2].length) (baseStart_233528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233528 prefixEnd_233528 := by exact prefixLift 233528
  have htrace : WordTrace (prefixWord ++ tailWord_233528) baseStart_233528 baseEnd_233528 := by
    simpa [prefixWord, tailWord_233528, baseEnd_233528] using wordTrace_append hprefix tailTrace_233528
  have hstable : (prefixWord ++ tailWord_233528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233528).length < 2 ^ (prefixWord ++ tailWord_233528).sum := by decide
  have hdescent : baseEnd_233528 < baseStart_233528 := by decide
  rcases family_descends (prefixWord ++ tailWord_233528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233543 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 1, 8]
def baseStart_233543 : Nat := 118140960795 + 233543 * 2 ^ 59
def prefixEnd_233543 : Nat := 4983230072969 + 3 ^ 40 * 233543 * 2
def baseEnd_233543 : Nat := 39973270831028331879487

theorem tailTrace_233543 : CollatzResearch.WordTrace tailWord_233543 prefixEnd_233543 39973270831028331879487 := by
  unfold tailWord_233543
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518012992921071814025283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5678675328614047876016855 8518012992921071814025283)
  ·
    refine ⟨12777019489381607721037925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8518012992921071814025283 12777019489381607721037925)
    ·
      refine ⟨2395691154259051447694611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12777019489381607721037925 2395691154259051447694611)
      ·
        refine ⟨3593536731388577171541917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2395691154259051447694611 3593536731388577171541917)
        ·
          refine ⟨1347576274270716439328219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3593536731388577171541917 1347576274270716439328219)
          ·
            refine ⟨2021364411406074658992329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347576274270716439328219 2021364411406074658992329)
            ·
              refine ⟨1516023308554555994244247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021364411406074658992329 1516023308554555994244247)
              ·
                refine ⟨2274034962831833991366371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516023308554555994244247 2274034962831833991366371)
                ·
                  refine ⟨3411052444247750987049557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274034962831833991366371 3411052444247750987049557)
                  ·
                    refine ⟨39973270831028331879487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3411052444247750987049557 39973270831028331879487)
                    ·
                      rfl

theorem cell23_233543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_233543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233543 prefixEnd_233543 := by exact prefixLift 233543
  have htrace : WordTrace (prefixWord ++ tailWord_233543) baseStart_233543 baseEnd_233543 := by
    simpa [prefixWord, tailWord_233543, baseEnd_233543] using wordTrace_append hprefix tailTrace_233543
  have hstable : (prefixWord ++ tailWord_233543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233543).length < 2 ^ (prefixWord ++ tailWord_233543).sum := by decide
  have hdescent : baseEnd_233543 < baseStart_233543 := by decide
  rcases family_descends (prefixWord ++ tailWord_233543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233554 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_233554 : Nat := 118140960795 + 233554 * 2 ^ 59
def prefixEnd_233554 : Nat := 4983230072969 + 3 ^ 40 * 233554 * 2
def baseEnd_233554 : Nat := 119925460780284452600911

theorem tailTrace_233554 : CollatzResearch.WordTrace tailWord_233554 prefixEnd_233554 119925460780284452600911 := by
  unfold tailWord_233554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2129603548970305173168929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5678942797254147128450477 2129603548970305173168929)
  ·
    refine ⟨1597202661727728879876697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2129603548970305173168929 1597202661727728879876697)
    ·
      refine ⟨1197901996295796659907523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1597202661727728879876697 1197901996295796659907523)
      ·
        refine ⟨1796852994443694989861285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197901996295796659907523 1796852994443694989861285)
        ·
          refine ⟨336909936458192810598991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1796852994443694989861285 336909936458192810598991)
          ·
            refine ⟨505364904687289215898487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336909936458192810598991 505364904687289215898487)
            ·
              refine ⟨758047357030933823847731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505364904687289215898487 758047357030933823847731)
              ·
                refine ⟨1137071035546400735771597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758047357030933823847731 1137071035546400735771597)
                ·
                  refine ⟨426401638329900275914349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137071035546400735771597 426401638329900275914349)
                  ·
                    refine ⟨159900614373712603467881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426401638329900275914349 159900614373712603467881)
                    ·
                      refine ⟨119925460780284452600911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159900614373712603467881 119925460780284452600911)
                      ·
                        rfl

theorem cell23_233554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_233554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233554 prefixEnd_233554 := by exact prefixLift 233554
  have htrace : WordTrace (prefixWord ++ tailWord_233554) baseStart_233554 baseEnd_233554 := by
    simpa [prefixWord, tailWord_233554, baseEnd_233554] using wordTrace_append hprefix tailTrace_233554
  have hstable : (prefixWord ++ tailWord_233554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233554).length < 2 ^ (prefixWord ++ tailWord_233554).sum := by decide
  have hdescent : baseEnd_233554 < baseStart_233554 := by decide
  rcases family_descends (prefixWord ++ tailWord_233554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233567 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 4, 2, 2]
def baseStart_233567 : Nat := 118140960795 + 233567 * 2 ^ 59
def prefixEnd_233567 : Nat := 4983230072969 + 3 ^ 40 * 233567 * 2
def baseEnd_233567 : Nat := 119932136028792901738351

theorem tailTrace_233567 : CollatzResearch.WordTrace tailWord_233567 prefixEnd_233567 119932136028792901738351 := by
  unfold tailWord_233567
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518888344834123912898955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5679258896556082608599303 8518888344834123912898955)
  ·
    refine ⟨12778332517251185869348433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8518888344834123912898955 12778332517251185869348433)
    ·
      refine ⟨9583749387938389402011325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12778332517251185869348433 9583749387938389402011325)
      ·
        refine ⟨3593906020476896025754247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9583749387938389402011325 3593906020476896025754247)
        ·
          refine ⟨5390859030715344038631371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3593906020476896025754247 5390859030715344038631371)
          ·
            refine ⟨8086288546073016057947057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390859030715344038631371 8086288546073016057947057)
            ·
              refine ⟨6064716409554762043460293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8086288546073016057947057 6064716409554762043460293)
              ·
                refine ⟨1137134326791517883148805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6064716409554762043460293 1137134326791517883148805)
                ·
                  refine ⟨213212686273409603090401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137134326791517883148805 213212686273409603090401)
                  ·
                    refine ⟨159909514705057202317801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213212686273409603090401 159909514705057202317801)
                    ·
                      refine ⟨119932136028792901738351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159909514705057202317801 119932136028792901738351)
                      ·
                        rfl

theorem cell23_233567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_233567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233567 prefixEnd_233567 := by exact prefixLift 233567
  have htrace : WordTrace (prefixWord ++ tailWord_233567) baseStart_233567 baseEnd_233567 := by
    simpa [prefixWord, tailWord_233567, baseEnd_233567] using wordTrace_append hprefix tailTrace_233567
  have hstable : (prefixWord ++ tailWord_233567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233567).length < 2 ^ (prefixWord ++ tailWord_233567).sum := by decide
  have hdescent : baseEnd_233567 < baseStart_233567 := by decide
  rcases family_descends (prefixWord ++ tailWord_233567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233584 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 2, 2, 2]
def baseStart_233584 : Nat := 118140960795 + 233584 * 2 ^ 59
def prefixEnd_233584 : Nat := 4983230072969 + 3 ^ 40 * 233584 * 2
def baseEnd_233584 : Nat := 119940865199919335225773

theorem tailTrace_233584 : CollatzResearch.WordTrace tailWord_233584 prefixEnd_233584 119940865199919335225773 := by
  unfold tailWord_233584
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259754192886267908133903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5679672257181690544178537 4259754192886267908133903)
  ·
    refine ⟨6389631289329401862200855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4259754192886267908133903 6389631289329401862200855)
    ·
      refine ⟨9584446933994102793301283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6389631289329401862200855 9584446933994102793301283)
      ·
        refine ⟨14376670400991154189951925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9584446933994102793301283 14376670400991154189951925)
        ·
          refine ⟨1347812850092920705307993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14376670400991154189951925 1347812850092920705307993)
          ·
            refine ⟨1010859637569690528980995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347812850092920705307993 1010859637569690528980995)
            ·
              refine ⟨1516289456354535793471493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010859637569690528980995 1516289456354535793471493)
              ·
                refine ⟨284304273066475461275905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1516289456354535793471493 284304273066475461275905)
                ·
                  refine ⟨213228204799856595956929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284304273066475461275905 213228204799856595956929)
                  ·
                    refine ⟨159921153599892446967697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213228204799856595956929 159921153599892446967697)
                    ·
                      refine ⟨119940865199919335225773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159921153599892446967697 119940865199919335225773)
                      ·
                        rfl

theorem cell23_233584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2, 2, 2].length) (baseStart_233584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233584 prefixEnd_233584 := by exact prefixLift 233584
  have htrace : WordTrace (prefixWord ++ tailWord_233584) baseStart_233584 baseEnd_233584 := by
    simpa [prefixWord, tailWord_233584, baseEnd_233584] using wordTrace_append hprefix tailTrace_233584
  have hstable : (prefixWord ++ tailWord_233584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233584).length < 2 ^ (prefixWord ++ tailWord_233584).sum := by decide
  have hdescent : baseEnd_233584 < baseStart_233584 := by decide
  rcases family_descends (prefixWord ++ tailWord_233584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233622 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_233622 : Nat := 118140960795 + 233622 * 2 ^ 59
def prefixEnd_233622 : Nat := 4983230072969 + 3 ^ 40 * 233622 * 2
def baseEnd_233622 : Nat := 119960377464790186550599

theorem tailTrace_233622 : CollatzResearch.WordTrace tailWord_233622 prefixEnd_233622 119960377464790186550599 := by
  unfold tailWord_233622
  simp only [CollatzResearch.WordTrace]
  refine ⟨532555897477179269134445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5680596239756578870767413 532555897477179269134445)
  ·
    refine ⟨199708461553942225925417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 532555897477179269134445 199708461553942225925417)
    ·
      refine ⟨149781346165456669444063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199708461553942225925417 149781346165456669444063)
      ·
        refine ⟨224672019248185004166095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149781346165456669444063 224672019248185004166095)
        ·
          refine ⟨337008028872277506249143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224672019248185004166095 337008028872277506249143)
          ·
            refine ⟨505512043308416259373715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337008028872277506249143 505512043308416259373715)
            ·
              refine ⟨758268064962624389060573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505512043308416259373715 758268064962624389060573)
              ·
                refine ⟨284350524360984145897715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 758268064962624389060573 284350524360984145897715)
                ·
                  refine ⟨426525786541476218846573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284350524360984145897715 426525786541476218846573)
                  ·
                    refine ⟨159947169953053582067465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426525786541476218846573 159947169953053582067465)
                    ·
                      refine ⟨119960377464790186550599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159947169953053582067465 119960377464790186550599)
                      ·
                        rfl

theorem cell23_233622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_233622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233622 prefixEnd_233622 := by exact prefixLift 233622
  have htrace : WordTrace (prefixWord ++ tailWord_233622) baseStart_233622 baseEnd_233622 := by
    simpa [prefixWord, tailWord_233622, baseEnd_233622] using wordTrace_append hprefix tailTrace_233622
  have hstable : (prefixWord ++ tailWord_233622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233622).length < 2 ^ (prefixWord ++ tailWord_233622).sum := by decide
  have hdescent : baseEnd_233622 < baseStart_233622 := by decide
  rcases family_descends (prefixWord ++ tailWord_233622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233624 : List Nat := [2, 1, 2, 4, 3, 1, 2, 3, 5]
def baseStart_233624 : Nat := 118140960795 + 233624 * 2 ^ 59
def prefixEnd_233624 : Nat := 4983230072969 + 3 ^ 40 * 233624 * 2
def baseEnd_233624 : Nat := 13329044936233242080621

theorem tailTrace_233624 : CollatzResearch.WordTrace tailWord_233624 prefixEnd_233624 13329044936233242080621 := by
  unfold tailWord_233624
  simp only [CollatzResearch.WordTrace]
  refine ⟨4260483652813811323861963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5680644870418415098482617 4260483652813811323861963)
  ·
    refine ⟨6390725479220716985792945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4260483652813811323861963 6390725479220716985792945)
    ·
      refine ⟨4793044109415537739344709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6390725479220716985792945 4793044109415537739344709)
      ·
        refine ⟨898695770515413326127133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4793044109415537739344709 898695770515413326127133)
        ·
          refine ⟨337010913943279997297675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 898695770515413326127133 337010913943279997297675)
          ·
            refine ⟨505516370914919995946513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337010913943279997297675 505516370914919995946513)
            ·
              refine ⟨379137278186189996959885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505516370914919995946513 379137278186189996959885)
              ·
                refine ⟨142176479319821248859957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379137278186189996959885 142176479319821248859957)
                ·
                  refine ⟨13329044936233242080621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142176479319821248859957 13329044936233242080621)
                  ·
                    rfl

theorem cell23_233624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 5].length) (baseStart_233624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233624 prefixEnd_233624 := by exact prefixLift 233624
  have htrace : WordTrace (prefixWord ++ tailWord_233624) baseStart_233624 baseEnd_233624 := by
    simpa [prefixWord, tailWord_233624, baseEnd_233624] using wordTrace_append hprefix tailTrace_233624
  have hstable : (prefixWord ++ tailWord_233624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233624).length < 2 ^ (prefixWord ++ tailWord_233624).sum := by decide
  have hdescent : baseEnd_233624 < baseStart_233624 := by decide
  rcases family_descends (prefixWord ++ tailWord_233624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233652 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_233652 : Nat := 118140960795 + 233652 * 2 ^ 59
def prefixEnd_233652 : Nat := 4983230072969 + 3 ^ 40 * 233652 * 2
def baseEnd_233652 : Nat := 119975781884425069175461

theorem tailTrace_233652 : CollatzResearch.WordTrace tailWord_233652 prefixEnd_233652 119975781884425069175461 := by
  unfold tailWord_233652
  simp only [CollatzResearch.WordTrace]
  refine ⟨4260994274763091714871605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5681325699684122286495473 4260994274763091714871605)
  ·
    refine ⟨399468213259039848269213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4260994274763091714871605 399468213259039848269213)
    ·
      refine ⟨149800579972139943100955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399468213259039848269213 149800579972139943100955)
      ·
        refine ⟨224700869958209914651433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149800579972139943100955 224700869958209914651433)
        ·
          refine ⟨168525652468657435988575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224700869958209914651433 168525652468657435988575)
          ·
            refine ⟨252788478702986153982863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168525652468657435988575 252788478702986153982863)
            ·
              refine ⟨379182718054479230974295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252788478702986153982863 379182718054479230974295)
              ·
                refine ⟨568774077081718846461443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379182718054479230974295 568774077081718846461443)
                ·
                  refine ⟨853161115622578269692165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568774077081718846461443 853161115622578269692165)
                  ·
                    refine ⟨159967709179233425567281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 853161115622578269692165 159967709179233425567281)
                    ·
                      refine ⟨119975781884425069175461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159967709179233425567281 119975781884425069175461)
                      ·
                        rfl

theorem cell23_233652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_233652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233652 prefixEnd_233652 := by exact prefixLift 233652
  have htrace : WordTrace (prefixWord ++ tailWord_233652) baseStart_233652 baseEnd_233652 := by
    simpa [prefixWord, tailWord_233652, baseEnd_233652] using wordTrace_append hprefix tailTrace_233652
  have hstable : (prefixWord ++ tailWord_233652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233652).length < 2 ^ (prefixWord ++ tailWord_233652).sum := by decide
  have hdescent : baseEnd_233652 < baseStart_233652 := by decide
  rcases family_descends (prefixWord ++ tailWord_233652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233657 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 2, 4, 2]
def baseStart_233657 : Nat := 118140960795 + 233657 * 2 ^ 59
def prefixEnd_233657 : Nat := 4983230072969 + 3 ^ 40 * 233657 * 2
def baseEnd_233657 : Nat := 119978349287697549612937

theorem tailTrace_233657 : CollatzResearch.WordTrace tailWord_233657 prefixEnd_233657 119978349287697549612937 := by
  unfold tailWord_233657
  simp only [CollatzResearch.WordTrace]
  refine ⟨8522170914508069283675225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5681447276338712855783483 8522170914508069283675225)
  ·
    refine ⟨6391628185881051962756419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8522170914508069283675225 6391628185881051962756419)
    ·
      refine ⟨9587442278821577944134629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6391628185881051962756419 9587442278821577944134629)
      ·
        refine ⟨1797645427279045864525243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9587442278821577944134629 1797645427279045864525243)
        ·
          refine ⟨2696468140918568796787865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797645427279045864525243 2696468140918568796787865)
          ·
            refine ⟨2022351105688926597590899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2696468140918568796787865 2022351105688926597590899)
            ·
              refine ⟨3033526658533389896386349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2022351105688926597590899 3033526658533389896386349)
              ·
                refine ⟨1137572496950021211144881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3033526658533389896386349 1137572496950021211144881)
                ·
                  refine ⟨853179372712515908358661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1137572496950021211144881 853179372712515908358661)
                  ·
                    refine ⟨159971132383596732817249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 853179372712515908358661 159971132383596732817249)
                    ·
                      refine ⟨119978349287697549612937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 159971132383596732817249 119978349287697549612937)
                      ·
                        rfl

theorem cell23_233657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_233657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233657 prefixEnd_233657 := by exact prefixLift 233657
  have htrace : WordTrace (prefixWord ++ tailWord_233657) baseStart_233657 baseEnd_233657 := by
    simpa [prefixWord, tailWord_233657, baseEnd_233657] using wordTrace_append hprefix tailTrace_233657
  have hstable : (prefixWord ++ tailWord_233657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233657).length < 2 ^ (prefixWord ++ tailWord_233657).sum := by decide
  have hdescent : baseEnd_233657 < baseStart_233657 := by decide
  rcases family_descends (prefixWord ++ tailWord_233657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233710 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_233710 : Nat := 118140960795 + 233710 * 2 ^ 59
def prefixEnd_233710 : Nat := 4983230072969 + 3 ^ 40 * 233710 * 2
def baseEnd_233710 : Nat := 40001854587461947416731

theorem tailTrace_233710 : CollatzResearch.WordTrace tailWord_233710 prefixEnd_233710 40001854587461947416731 := by
  unfold tailWord_233710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065512997914507416919323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5682735988877372890236389 1065512997914507416919323)
  ·
    refine ⟨1598269496871761125378985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1065512997914507416919323 1598269496871761125378985)
    ·
      refine ⟨1198702122653820844034239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1598269496871761125378985 1198702122653820844034239)
      ·
        refine ⟨1798053183980731266051359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1198702122653820844034239 1798053183980731266051359)
        ·
          refine ⟨2697079775971096899077039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798053183980731266051359 2697079775971096899077039)
          ·
            refine ⟨4045619663956645348615559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697079775971096899077039 4045619663956645348615559)
            ·
              refine ⟨6068429495934968022923339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045619663956645348615559 6068429495934968022923339)
              ·
                refine ⟨9102644243902452034385009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068429495934968022923339 9102644243902452034385009)
                ·
                  refine ⟨6826983182926839025788757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9102644243902452034385009 6826983182926839025788757)
                  ·
                    refine ⟨40001854587461947416731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 6826983182926839025788757 40001854587461947416731)
                    ·
                      rfl

theorem cell23_233710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_233710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233710 prefixEnd_233710 := by exact prefixLift 233710
  have htrace : WordTrace (prefixWord ++ tailWord_233710) baseStart_233710 baseEnd_233710 := by
    simpa [prefixWord, tailWord_233710, baseEnd_233710] using wordTrace_append hprefix tailTrace_233710
  have hstable : (prefixWord ++ tailWord_233710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233710).length < 2 ^ (prefixWord ++ tailWord_233710).sum := by decide
  have hdescent : baseEnd_233710 < baseStart_233710 := by decide
  rcases family_descends (prefixWord ++ tailWord_233710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233714 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 6]
def baseStart_233714 : Nat := 118140960795 + 233714 * 2 ^ 59
def prefixEnd_233714 : Nat := 4983230072969 + 3 ^ 40 * 233714 * 2
def baseEnd_233714 : Nat := 13334179742778202955575

theorem tailTrace_233714 : CollatzResearch.WordTrace tailWord_233714 prefixEnd_233714 13334179742778202955575 := by
  unfold tailWord_233714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131062468825392004625049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5682833250201045345666797 2131062468825392004625049)
  ·
    refine ⟨1598296851619044003468787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2131062468825392004625049 1598296851619044003468787)
    ·
      refine ⟨2397445277428566005203181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1598296851619044003468787 2397445277428566005203181)
      ·
        refine ⟨899041979035712251951193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2397445277428566005203181 899041979035712251951193)
        ·
          refine ⟨674281484276784188963395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899041979035712251951193 674281484276784188963395)
          ·
            refine ⟨1011422226415176283445093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674281484276784188963395 1011422226415176283445093)
            ·
              refine ⟨189641667452845553145955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1011422226415176283445093 189641667452845553145955)
              ·
                refine ⟨284462501179268329718933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189641667452845553145955 284462501179268329718933)
                ·
                  refine ⟨13334179742778202955575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 284462501179268329718933 13334179742778202955575)
                  ·
                    rfl

theorem cell23_233714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_233714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233714 prefixEnd_233714 := by exact prefixLift 233714
  have htrace : WordTrace (prefixWord ++ tailWord_233714) baseStart_233714 baseEnd_233714 := by
    simpa [prefixWord, tailWord_233714, baseEnd_233714] using wordTrace_append hprefix tailTrace_233714
  have hstable : (prefixWord ++ tailWord_233714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233714).length < 2 ^ (prefixWord ++ tailWord_233714).sum := by decide
  have hdescent : baseEnd_233714 < baseStart_233714 := by decide
  rcases family_descends (prefixWord ++ tailWord_233714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233747 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 4]
def baseStart_233747 : Nat := 118140960795 + 233747 * 2 ^ 59
def prefixEnd_233747 : Nat := 4983230072969 + 3 ^ 40 * 233747 * 2
def baseEnd_233747 : Nat := 120024562546602197487523

theorem tailTrace_233747 : CollatzResearch.WordTrace tailWord_233747 prefixEnd_233747 120024562546602197487523 := by
  unfold tailWord_233747
  simp only [CollatzResearch.WordTrace]
  refine ⟨8525453484182014654451495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5683635656121343102967663 8525453484182014654451495)
  ·
    refine ⟨12788180226273021981677243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8525453484182014654451495 12788180226273021981677243)
    ·
      refine ⟨19182270339409532972515865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12788180226273021981677243 19182270339409532972515865)
      ·
        refine ⟨14386702754557149729386899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19182270339409532972515865 14386702754557149729386899)
        ·
          refine ⟨21580054131835724594080349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14386702754557149729386899 21580054131835724594080349)
          ·
            refine ⟨8092520299438396722780131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21580054131835724594080349 8092520299438396722780131)
            ·
              refine ⟨12138780449157595084170197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092520299438396722780131 12138780449157595084170197)
              ·
                refine ⟨284502666777131134785239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12138780449157595084170197 284502666777131134785239)
                ·
                  refine ⟨426754000165696702177859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284502666777131134785239 426754000165696702177859)
                  ·
                    refine ⟨640131000248545053266789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 426754000165696702177859 640131000248545053266789)
                    ·
                      refine ⟨120024562546602197487523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 640131000248545053266789 120024562546602197487523)
                      ·
                        rfl

theorem cell23_233747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 4].length) (baseStart_233747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233747 prefixEnd_233747 := by exact prefixLift 233747
  have htrace : WordTrace (prefixWord ++ tailWord_233747) baseStart_233747 baseEnd_233747 := by
    simpa [prefixWord, tailWord_233747, baseEnd_233747] using wordTrace_append hprefix tailTrace_233747
  have hstable : (prefixWord ++ tailWord_233747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233747).length < 2 ^ (prefixWord ++ tailWord_233747).sum := by decide
  have hdescent : baseEnd_233747 < baseStart_233747 := by decide
  rcases family_descends (prefixWord ++ tailWord_233747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233781 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_233781 : Nat := 118140960795 + 233781 * 2 ^ 59
def prefixEnd_233781 : Nat := 4983230072969 + 3 ^ 40 * 233781 * 2
def baseEnd_233781 : Nat := 120042020888855064462367

theorem tailTrace_233781 : CollatzResearch.WordTrace tailWord_233781 prefixEnd_233781 120042020888855064462367 := by
  unfold tailWord_233781
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526693566058838461189197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5684462377372558974126131 8526693566058838461189197)
  ·
    refine ⟨3197510087272064422945949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8526693566058838461189197 3197510087272064422945949)
    ·
      refine ⟨1199066282727024158604731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3197510087272064422945949 1199066282727024158604731)
      ·
        refine ⟨1798599424090536237907097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199066282727024158604731 1798599424090536237907097)
        ·
          refine ⟨1348949568067902178430323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1798599424090536237907097 1348949568067902178430323)
          ·
            refine ⟨2023424352101853267645485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348949568067902178430323 2023424352101853267645485)
            ·
              refine ⟨758784132038194975367057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2023424352101853267645485 758784132038194975367057)
              ·
                refine ⟨569088099028646231525293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758784132038194975367057 569088099028646231525293)
                ·
                  refine ⟨213408037135742336821985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569088099028646231525293 213408037135742336821985)
                  ·
                    refine ⟨160056027851806752616489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213408037135742336821985 160056027851806752616489)
                    ·
                      refine ⟨120042020888855064462367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160056027851806752616489 120042020888855064462367)
                      ·
                        rfl

theorem cell23_233781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_233781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233781 prefixEnd_233781 := by exact prefixLift 233781
  have htrace : WordTrace (prefixWord ++ tailWord_233781) baseStart_233781 baseEnd_233781 := by
    simpa [prefixWord, tailWord_233781, baseEnd_233781] using wordTrace_append hprefix tailTrace_233781
  have hstable : (prefixWord ++ tailWord_233781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233781).length < 2 ^ (prefixWord ++ tailWord_233781).sum := by decide
  have hdescent : baseEnd_233781 < baseStart_233781 := by decide
  rcases family_descends (prefixWord ++ tailWord_233781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233831 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_233831 : Nat := 118140960795 + 233831 * 2 ^ 59
def prefixEnd_233831 : Nat := 4983230072969 + 3 ^ 40 * 233831 * 2
def baseEnd_233831 : Nat := 120067694921579868837137

theorem tailTrace_233831 : CollatzResearch.WordTrace tailWord_233831 prefixEnd_233831 120067694921579868837137 := by
  unfold tailWord_233831
  simp only [CollatzResearch.WordTrace]
  refine ⟨8528517215877697000509347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5685678143918464667006231 8528517215877697000509347)
  ·
    refine ⟨12792775823816545500764021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8528517215877697000509347 12792775823816545500764021)
    ·
      refine ⟨1199322733482801140696627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12792775823816545500764021 1199322733482801140696627)
      ·
        refine ⟨1798984100224201711044941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199322733482801140696627 1798984100224201711044941)
        ·
          refine ⟨674619037584075641641853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1798984100224201711044941 674619037584075641641853)
          ·
            refine ⟨252982139094028365615695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 674619037584075641641853 252982139094028365615695)
            ·
              refine ⟨379473208641042548423543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252982139094028365615695 379473208641042548423543)
              ·
                refine ⟨569209812961563822635315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379473208641042548423543 569209812961563822635315)
                ·
                  refine ⟨853814719442345733952973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569209812961563822635315 853814719442345733952973)
                  ·
                    refine ⟨320180519790879650232365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 853814719442345733952973 320180519790879650232365)
                    ·
                      refine ⟨120067694921579868837137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 320180519790879650232365 120067694921579868837137)
                      ·
                        rfl

theorem cell23_233831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_233831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233831 prefixEnd_233831 := by exact prefixLift 233831
  have htrace : WordTrace (prefixWord ++ tailWord_233831) baseStart_233831 baseEnd_233831 := by
    simpa [prefixWord, tailWord_233831, baseEnd_233831] using wordTrace_append hprefix tailTrace_233831
  have hstable : (prefixWord ++ tailWord_233831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233831).length < 2 ^ (prefixWord ++ tailWord_233831).sum := by decide
  have hdescent : baseEnd_233831 < baseStart_233831 := by decide
  rcases family_descends (prefixWord ++ tailWord_233831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233888 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 2, 2, 2]
def baseStart_233888 : Nat := 118140960795 + 233888 * 2 ^ 59
def prefixEnd_233888 : Nat := 4983230072969 + 3 ^ 40 * 233888 * 2
def baseEnd_233888 : Nat := 120096963318886145824375

theorem tailTrace_233888 : CollatzResearch.WordTrace tailWord_233888 prefixEnd_233888 120096963318886145824375 := by
  unfold tailWord_233888
  simp only [CollatzResearch.WordTrace]
  refine ⟨4265298088335597867667159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5687064117780797156889545 4265298088335597867667159)
  ·
    refine ⟨6397947132503396801500739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4265298088335597867667159 6397947132503396801500739)
    ·
      refine ⟨9596920698755095202251109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6397947132503396801500739 9596920698755095202251109)
      ·
        refine ⟨1799422631016580350422083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9596920698755095202251109 1799422631016580350422083)
        ·
          refine ⟨2699133946524870525633125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1799422631016580350422083 2699133946524870525633125)
          ·
            refine ⟨506087614973413223556211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2699133946524870525633125 506087614973413223556211)
            ·
              refine ⟨759131422460119835334317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506087614973413223556211 759131422460119835334317)
              ·
                refine ⟨284674283422544938250369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 759131422460119835334317 284674283422544938250369)
                ·
                  refine ⟨213505712566908703687777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284674283422544938250369 213505712566908703687777)
                  ·
                    refine ⟨160129284425181527765833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213505712566908703687777 160129284425181527765833)
                    ·
                      refine ⟨120096963318886145824375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160129284425181527765833 120096963318886145824375)
                      ·
                        rfl

theorem cell23_233888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_233888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233888 prefixEnd_233888 := by exact prefixLift 233888
  have htrace : WordTrace (prefixWord ++ tailWord_233888) baseStart_233888 baseEnd_233888 := by
    simpa [prefixWord, tailWord_233888, baseEnd_233888] using wordTrace_append hprefix tailTrace_233888
  have hstable : (prefixWord ++ tailWord_233888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233888).length < 2 ^ (prefixWord ++ tailWord_233888).sum := by decide
  have hdescent : baseEnd_233888 < baseStart_233888 := by decide
  rcases family_descends (prefixWord ++ tailWord_233888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233914 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2]
def baseStart_233914 : Nat := 118140960795 + 233914 * 2 ^ 59
def prefixEnd_233914 : Nat := 4983230072969 + 3 ^ 40 * 233914 * 2
def baseEnd_233914 : Nat := 120110313815903044099255

theorem tailTrace_233914 : CollatzResearch.WordTrace tailWord_233914 prefixEnd_233914 120110313815903044099255 := by
  unfold tailWord_233914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132886118644250543945199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5687696316384668117187197 2132886118644250543945199)
  ·
    refine ⟨3199329177966375815917799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2132886118644250543945199 3199329177966375815917799)
    ·
      refine ⟨4798993766949563723876699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3199329177966375815917799 4798993766949563723876699)
      ·
        refine ⟨7198490650424345585815049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4798993766949563723876699 7198490650424345585815049)
        ·
          refine ⟨5398867987818259189361287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7198490650424345585815049 5398867987818259189361287)
          ·
            refine ⟨8098301981727388784041931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398867987818259189361287 8098301981727388784041931)
            ·
              refine ⟨12147452972591083176062897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8098301981727388784041931 12147452972591083176062897)
              ·
                refine ⟨9110589729443312382047173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12147452972591083176062897 9110589729443312382047173)
                ·
                  refine ⟨1708235574270621071633845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9110589729443312382047173 1708235574270621071633845)
                  ·
                    refine ⟨160147085087870725465673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1708235574270621071633845 160147085087870725465673)
                    ·
                      refine ⟨120110313815903044099255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160147085087870725465673 120110313815903044099255)
                      ·
                        rfl

theorem cell23_233914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_233914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233914 prefixEnd_233914 := by exact prefixLift 233914
  have htrace : WordTrace (prefixWord ++ tailWord_233914) baseStart_233914 baseEnd_233914 := by
    simpa [prefixWord, tailWord_233914, baseEnd_233914] using wordTrace_append hprefix tailTrace_233914
  have hstable : (prefixWord ++ tailWord_233914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233914).length < 2 ^ (prefixWord ++ tailWord_233914).sum := by decide
  have hdescent : baseEnd_233914 < baseStart_233914 := by decide
  rcases family_descends (prefixWord ++ tailWord_233914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233928 : List Nat := [2, 1, 3, 1, 3, 4, 2, 2, 5]
def baseStart_233928 : Nat := 118140960795 + 233928 * 2 ^ 59
def prefixEnd_233928 : Nat := 4983230072969 + 3 ^ 40 * 233928 * 2
def baseEnd_233928 : Nat := 13346389171673998813799

theorem tailTrace_233928 : CollatzResearch.WordTrace tailWord_233928 prefixEnd_233928 13346389171673998813799 := by
  unfold tailWord_233928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4266027548263141283395219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5688036731017521711193625 4266027548263141283395219)
  ·
    refine ⟨6399041322394711925092829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4266027548263141283395219 6399041322394711925092829)
    ·
      refine ⟨2399640495898016971909811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6399041322394711925092829 2399640495898016971909811)
      ·
        refine ⟨3599460743847025457864717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399640495898016971909811 3599460743847025457864717)
        ·
          refine ⟨1349797778942634546699269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3599460743847025457864717 1349797778942634546699269)
          ·
            refine ⟨253087083551743977506113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1349797778942634546699269 253087083551743977506113)
            ·
              refine ⟨189815312663807983129585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253087083551743977506113 189815312663807983129585)
              ·
                refine ⟨142361484497855987347189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189815312663807983129585 142361484497855987347189)
                ·
                  refine ⟨13346389171673998813799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142361484497855987347189 13346389171673998813799)
                  ·
                    rfl

theorem cell23_233928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 5].length) (baseStart_233928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233928 prefixEnd_233928 := by exact prefixLift 233928
  have htrace : WordTrace (prefixWord ++ tailWord_233928) baseStart_233928 baseEnd_233928 := by
    simpa [prefixWord, tailWord_233928, baseEnd_233928] using wordTrace_append hprefix tailTrace_233928
  have hstable : (prefixWord ++ tailWord_233928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233928).length < 2 ^ (prefixWord ++ tailWord_233928).sum := by decide
  have hdescent : baseEnd_233928 < baseStart_233928 := by decide
  rcases family_descends (prefixWord ++ tailWord_233928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233938 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_233938 : Nat := 118140960795 + 233938 * 2 ^ 59
def prefixEnd_233938 : Nat := 4983230072969 + 3 ^ 40 * 233938 * 2
def baseEnd_233938 : Nat := 120122637351610950199145

theorem tailTrace_233938 : CollatzResearch.WordTrace tailWord_233938 prefixEnd_233938 120122637351610950199145 := by
  unfold tailWord_233938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133104956622513568663617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5688279884326702849769645 2133104956622513568663617)
  ·
    refine ⟨1599828717466885176497713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2133104956622513568663617 1599828717466885176497713)
    ·
      refine ⟨1199871538100163882373285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1599828717466885176497713 1199871538100163882373285)
      ·
        refine ⟨224975913393780727944991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1199871538100163882373285 224975913393780727944991)
        ·
          refine ⟨337463870090671091917487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224975913393780727944991 337463870090671091917487)
          ·
            refine ⟨506195805136006637876231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337463870090671091917487 506195805136006637876231)
            ·
              refine ⟨759293707704009956814347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506195805136006637876231 759293707704009956814347)
              ·
                refine ⟨1138940561556014935221521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759293707704009956814347 1138940561556014935221521)
                ·
                  refine ⟨854205421167011201416141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1138940561556014935221521 854205421167011201416141)
                  ·
                    refine ⟨320327032937629200531053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 854205421167011201416141 320327032937629200531053)
                    ·
                      refine ⟨120122637351610950199145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 320327032937629200531053 120122637351610950199145)
                      ·
                        rfl

theorem cell23_233938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_233938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233938 prefixEnd_233938 := by exact prefixLift 233938
  have htrace : WordTrace (prefixWord ++ tailWord_233938) baseStart_233938 baseEnd_233938 := by
    simpa [prefixWord, tailWord_233938, baseEnd_233938] using wordTrace_append hprefix tailTrace_233938
  have hstable : (prefixWord ++ tailWord_233938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233938).length < 2 ^ (prefixWord ++ tailWord_233938).sum := by decide
  have hdescent : baseEnd_233938 < baseStart_233938 := by decide
  rcases family_descends (prefixWord ++ tailWord_233938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233964 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 3]
def baseStart_233964 : Nat := 118140960795 + 233964 * 2 ^ 59
def prefixEnd_233964 : Nat := 4983230072969 + 3 ^ 40 * 233964 * 2
def baseEnd_233964 : Nat := 120135987848627848474025

theorem tailTrace_233964 : CollatzResearch.WordTrace tailWord_233964 prefixEnd_233964 120135987848627848474025 := by
  unfold tailWord_233964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4266684062197930357550473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5688912082930573810067297 4266684062197930357550473)
  ·
    refine ⟨3200013046648447768162855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4266684062197930357550473 3200013046648447768162855)
    ·
      refine ⟨4800019569972671652244283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200013046648447768162855 4800019569972671652244283)
      ·
        refine ⟨7200029354959007478366425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4800019569972671652244283 7200029354959007478366425)
        ·
          refine ⟨5400022016219255608774819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7200029354959007478366425 5400022016219255608774819)
          ·
            refine ⟨8100033024328883413162229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400022016219255608774819 8100033024328883413162229)
            ·
              refine ⟨759378096030832819983959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8100033024328883413162229 759378096030832819983959)
              ·
                refine ⟨1139067144046249229975939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759378096030832819983959 1139067144046249229975939)
                ·
                  refine ⟨1708600716069373844963909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139067144046249229975939 1708600716069373844963909)
                  ·
                    refine ⟨320362634263007595930733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1708600716069373844963909 320362634263007595930733)
                    ·
                      refine ⟨120135987848627848474025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 320362634263007595930733 120135987848627848474025)
                      ·
                        rfl

theorem cell23_233964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_233964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233964 prefixEnd_233964 := by exact prefixLift 233964
  have htrace : WordTrace (prefixWord ++ tailWord_233964) baseStart_233964 baseEnd_233964 := by
    simpa [prefixWord, tailWord_233964, baseEnd_233964] using wordTrace_append hprefix tailTrace_233964
  have hstable : (prefixWord ++ tailWord_233964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233964).length < 2 ^ (prefixWord ++ tailWord_233964).sum := by decide
  have hdescent : baseEnd_233964 < baseStart_233964 := by decide
  rcases family_descends (prefixWord ++ tailWord_233964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233967 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 8]
def baseStart_233967 : Nat := 118140960795 + 233967 * 2 ^ 59
def prefixEnd_233967 : Nat := 4983230072969 + 3 ^ 40 * 233967 * 2
def baseEnd_233967 : Nat := 13348614254510148526279

theorem tailTrace_233967 : CollatzResearch.WordTrace tailWord_233967 prefixEnd_233967 13348614254510148526279 := by
  unfold tailWord_233967
  simp only [CollatzResearch.WordTrace]
  refine ⟨8533477543384992227460155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5688985028923328151640103 8533477543384992227460155)
  ·
    refine ⟨12800216315077488341190233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8533477543384992227460155 12800216315077488341190233)
    ·
      refine ⟨9600162236308116255892675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12800216315077488341190233 9600162236308116255892675)
      ·
        refine ⟨14400243354462174383839013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9600162236308116255892675 14400243354462174383839013)
        ·
          refine ⟨2700045628961657696969815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14400243354462174383839013 2700045628961657696969815)
          ·
            refine ⟨4050068443442486545454723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700045628961657696969815 4050068443442486545454723)
            ·
              refine ⟨6075102665163729818182085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050068443442486545454723 6075102665163729818182085)
              ·
                refine ⟨1139081749718199340909141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6075102665163729818182085 1139081749718199340909141)
                ·
                  refine ⟨13348614254510148526279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1139081749718199340909141 13348614254510148526279)
                  ·
                    rfl

theorem cell23_233967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 8].length) (baseStart_233967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233967 prefixEnd_233967 := by exact prefixLift 233967
  have htrace : WordTrace (prefixWord ++ tailWord_233967) baseStart_233967 baseEnd_233967 := by
    simpa [prefixWord, tailWord_233967, baseEnd_233967] using wordTrace_append hprefix tailTrace_233967
  have hstable : (prefixWord ++ tailWord_233967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233967).length < 2 ^ (prefixWord ++ tailWord_233967).sum := by decide
  have hdescent : baseEnd_233967 < baseStart_233967 := by decide
  rcases family_descends (prefixWord ++ tailWord_233967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233974 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_233974 : Nat := 118140960795 + 233974 * 2 ^ 59
def prefixEnd_233974 : Nat := 4983230072969 + 3 ^ 40 * 233974 * 2
def baseEnd_233974 : Nat := 120141122655172809348979

theorem tailTrace_233974 : CollatzResearch.WordTrace tailWord_233974 prefixEnd_233974 120141122655172809348979 := by
  unfold tailWord_233974
  simp only [CollatzResearch.WordTrace]
  refine ⟨533358303397477026435311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5689155236239754948643317 533358303397477026435311)
  ·
    refine ⟨800037455096215539652967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 533358303397477026435311 800037455096215539652967)
    ·
      refine ⟨1200056182644323309479451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800037455096215539652967 1200056182644323309479451)
      ·
        refine ⟨1800084273966484964219177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200056182644323309479451 1800084273966484964219177)
        ·
          refine ⟨1350063205474863723164383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800084273966484964219177 1350063205474863723164383)
          ·
            refine ⟨2025094808212295584746575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350063205474863723164383 2025094808212295584746575)
            ·
              refine ⟨3037642212318443377119863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025094808212295584746575 3037642212318443377119863)
              ·
                refine ⟨4556463318477665065679795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037642212318443377119863 4556463318477665065679795)
                ·
                  refine ⟨6834694977716497598519693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556463318477665065679795 6834694977716497598519693)
                  ·
                    refine ⟨2563010616643686599444885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6834694977716497598519693 2563010616643686599444885)
                    ·
                      refine ⟨120141122655172809348979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2563010616643686599444885 120141122655172809348979)
                      ·
                        rfl

theorem cell23_233974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_233974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233974 prefixEnd_233974 := by exact prefixLift 233974
  have htrace : WordTrace (prefixWord ++ tailWord_233974) baseStart_233974 baseEnd_233974 := by
    simpa [prefixWord, tailWord_233974, baseEnd_233974] using wordTrace_append hprefix tailTrace_233974
  have hstable : (prefixWord ++ tailWord_233974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233974).length < 2 ^ (prefixWord ++ tailWord_233974).sum := by decide
  have hdescent : baseEnd_233974 < baseStart_233974 := by decide
  rcases family_descends (prefixWord ++ tailWord_233974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233987 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 8]
def baseStart_233987 : Nat := 118140960795 + 233987 * 2 ^ 59
def prefixEnd_233987 : Nat := 4983230072969 + 3 ^ 40 * 233987 * 2
def baseEnd_233987 : Nat := 120147797903681258486419

theorem tailTrace_233987 : CollatzResearch.WordTrace tailWord_233987 prefixEnd_233987 120147797903681258486419 := by
  unfold tailWord_233987
  simp only [CollatzResearch.WordTrace]
  refine ⟨8534207003312535643188215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5689471335541690428792143 8534207003312535643188215)
  ·
    refine ⟨12801310504968803464782323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8534207003312535643188215 12801310504968803464782323)
    ·
      refine ⟨19201965757453205197173485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12801310504968803464782323 19201965757453205197173485)
      ·
        refine ⟨7200737159044951948940057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19201965757453205197173485 7200737159044951948940057)
        ·
          refine ⟨5400552869283713961705043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7200737159044951948940057 5400552869283713961705043)
          ·
            refine ⟨8100829303925570942557565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400552869283713961705043 8100829303925570942557565)
            ·
              refine ⟨3037810988972089103459087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8100829303925570942557565 3037810988972089103459087)
              ·
                refine ⟨4556716483458133655188631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037810988972089103459087 4556716483458133655188631)
                ·
                  refine ⟨6835074725187200482782947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556716483458133655188631 6835074725187200482782947)
                  ·
                    refine ⟨10252612087780800724174421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6835074725187200482782947 10252612087780800724174421)
                    ·
                      refine ⟨120147797903681258486419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 10252612087780800724174421 120147797903681258486419)
                      ·
                        rfl

theorem cell23_233987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_233987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233987 prefixEnd_233987 := by exact prefixLift 233987
  have htrace : WordTrace (prefixWord ++ tailWord_233987) baseStart_233987 baseEnd_233987 := by
    simpa [prefixWord, tailWord_233987, baseEnd_233987] using wordTrace_append hprefix tailTrace_233987
  have hstable : (prefixWord ++ tailWord_233987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233987).length < 2 ^ (prefixWord ++ tailWord_233987).sum := by decide
  have hdescent : baseEnd_233987 < baseStart_233987 := by decide
  rcases family_descends (prefixWord ++ tailWord_233987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233988 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_233988 : Nat := 118140960795 + 233988 * 2 ^ 59
def prefixEnd_233988 : Nat := 4983230072969 + 3 ^ 40 * 233988 * 2
def baseEnd_233988 : Nat := 40049437128111918191305

theorem tailTrace_233988 : CollatzResearch.WordTrace tailWord_233988 prefixEnd_233988 40049437128111918191305 := by
  unfold tailWord_233988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4267121738154456406987309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5689495650872608542649745 4267121738154456406987309)
  ·
    refine ⟨1600170651807921152620241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4267121738154456406987309 1600170651807921152620241)
    ·
      refine ⟨1200127988855940864465181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1600170651807921152620241 1200127988855940864465181)
      ·
        refine ⟨450047995820977824174443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1200127988855940864465181 450047995820977824174443)
        ·
          refine ⟨675071993731466736261665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450047995820977824174443 675071993731466736261665)
          ·
            refine ⟨506303995298600052196249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675071993731466736261665 506303995298600052196249)
            ·
              refine ⟨379727996473950039147187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506303995298600052196249 379727996473950039147187)
              ·
                refine ⟨569591994710925058720781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379727996473950039147187 569591994710925058720781)
                ·
                  refine ⟨213596998016596897020293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569591994710925058720781 213596998016596897020293)
                  ·
                    refine ⟨40049437128111918191305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 213596998016596897020293 40049437128111918191305)
                    ·
                      rfl

theorem cell23_233988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_233988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_233988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_233988 prefixEnd_233988 := by exact prefixLift 233988
  have htrace : WordTrace (prefixWord ++ tailWord_233988) baseStart_233988 baseEnd_233988 := by
    simpa [prefixWord, tailWord_233988, baseEnd_233988] using wordTrace_append hprefix tailTrace_233988
  have hstable : (prefixWord ++ tailWord_233988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233988).length < 2 ^ (prefixWord ++ tailWord_233988).sum := by decide
  have hdescent : baseEnd_233988 < baseStart_233988 := by decide
  rcases family_descends (prefixWord ++ tailWord_233988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234021 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 1, 5, 2]
def baseStart_234021 : Nat := 118140960795 + 234021 * 2 ^ 59
def prefixEnd_234021 : Nat := 4983230072969 + 3 ^ 40 * 234021 * 2
def baseEnd_234021 : Nat := 120165256245934125461263

theorem tailTrace_234021 : CollatzResearch.WordTrace tailWord_234021 prefixEnd_234021 120165256245934125461263 := by
  unfold tailWord_234021
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535447085189359449925917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5690298056792906299950611 8535447085189359449925917)
  ·
    refine ⟨3200792656946009793722219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8535447085189359449925917 3200792656946009793722219)
    ·
      refine ⟨4801188985419014690583329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200792656946009793722219 4801188985419014690583329)
      ·
        refine ⟨3600891739064261017937497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4801188985419014690583329 3600891739064261017937497)
        ·
          refine ⟨2700668804298195763453123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3600891739064261017937497 2700668804298195763453123)
          ·
            refine ⟨4051003206447293645179685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700668804298195763453123 4051003206447293645179685)
            ·
              refine ⟨759563101208867558471191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4051003206447293645179685 759563101208867558471191)
              ·
                refine ⟨1139344651813301337706787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759563101208867558471191 1139344651813301337706787)
                ·
                  refine ⟨1709016977719952006560181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139344651813301337706787 1709016977719952006560181)
                  ·
                    refine ⟨160220341661245500615017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1709016977719952006560181 160220341661245500615017)
                    ·
                      refine ⟨120165256245934125461263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160220341661245500615017 120165256245934125461263)
                      ·
                        rfl

theorem cell23_234021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_234021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234021 prefixEnd_234021 := by exact prefixLift 234021
  have htrace : WordTrace (prefixWord ++ tailWord_234021) baseStart_234021 baseEnd_234021 := by
    simpa [prefixWord, tailWord_234021, baseEnd_234021] using wordTrace_append hprefix tailTrace_234021
  have hstable : (prefixWord ++ tailWord_234021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234021).length < 2 ^ (prefixWord ++ tailWord_234021).sum := by decide
  have hdescent : baseEnd_234021 < baseStart_234021 := by decide
  rcases family_descends (prefixWord ++ tailWord_234021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234045 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_234045 : Nat := 118140960795 + 234045 * 2 ^ 59
def prefixEnd_234045 : Nat := 4983230072969 + 3 ^ 40 * 234045 * 2
def baseEnd_234045 : Nat := 120177579781642031561153

theorem tailTrace_234045 : CollatzResearch.WordTrace tailWord_234045 prefixEnd_234045 120177579781642031561153 := by
  unfold tailWord_234045
  simp only [CollatzResearch.WordTrace]
  refine ⟨8536322437102411548799589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5690881624734941032533059 8536322437102411548799589)
  ·
    refine ⟨1600560456956702165399923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8536322437102411548799589 1600560456956702165399923)
    ·
      refine ⟨2400840685435053248099885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600560456956702165399923 2400840685435053248099885)
      ·
        refine ⟨900315257038144968037457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2400840685435053248099885 900315257038144968037457)
        ·
          refine ⟨675236442778608726028093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 900315257038144968037457 675236442778608726028093)
          ·
            refine ⟨253213666041978272260535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675236442778608726028093 253213666041978272260535)
            ·
              refine ⟨379820499062967408390803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253213666041978272260535 379820499062967408390803)
              ·
                refine ⟨569730748594451112586205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379820499062967408390803 569730748594451112586205)
                ·
                  refine ⟨213649030722919167219827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569730748594451112586205 213649030722919167219827)
                  ·
                    refine ⟨320473546084378750829741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213649030722919167219827 320473546084378750829741)
                    ·
                      refine ⟨120177579781642031561153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 320473546084378750829741 120177579781642031561153)
                      ·
                        rfl

theorem cell23_234045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_234045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234045 prefixEnd_234045 := by exact prefixLift 234045
  have htrace : WordTrace (prefixWord ++ tailWord_234045) baseStart_234045 baseEnd_234045 := by
    simpa [prefixWord, tailWord_234045, baseEnd_234045] using wordTrace_append hprefix tailTrace_234045
  have hstable : (prefixWord ++ tailWord_234045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234045).length < 2 ^ (prefixWord ++ tailWord_234045).sum := by decide
  have hdescent : baseEnd_234045 < baseStart_234045 := by decide
  rcases family_descends (prefixWord ++ tailWord_234045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234068 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_234068 : Nat := 118140960795 + 234068 * 2 ^ 59
def prefixEnd_234068 : Nat := 4983230072969 + 3 ^ 40 * 234068 * 2
def baseEnd_234068 : Nat := 120189389836695441573547

theorem tailTrace_234068 : CollatzResearch.WordTrace tailWord_234068 prefixEnd_234068 120189389836695441573547 := by
  unfold tailWord_234068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4268580658009543238443429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5691440877346057651257905 4268580658009543238443429)
  ·
    refine ⟨800358873376789357208143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4268580658009543238443429 800358873376789357208143)
    ·
      refine ⟨1200538310065184035812215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800358873376789357208143 1200538310065184035812215)
      ·
        refine ⟨1800807465097776053718323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200538310065184035812215 1800807465097776053718323)
        ·
          refine ⟨2701211197646664080577485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800807465097776053718323 2701211197646664080577485)
          ·
            refine ⟨1012954199117499030216557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2701211197646664080577485 1012954199117499030216557)
            ·
              refine ⟨379857824669062136331209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1012954199117499030216557 379857824669062136331209)
              ·
                refine ⟨284893368501796602248407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379857824669062136331209 284893368501796602248407)
                ·
                  refine ⟨427340052752694903372611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284893368501796602248407 427340052752694903372611)
                  ·
                    refine ⟨641010079129042355058917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 427340052752694903372611 641010079129042355058917)
                    ·
                      refine ⟨120189389836695441573547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 641010079129042355058917 120189389836695441573547)
                      ·
                        rfl

theorem cell23_234068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_234068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234068 prefixEnd_234068 := by exact prefixLift 234068
  have htrace : WordTrace (prefixWord ++ tailWord_234068) baseStart_234068 baseEnd_234068 := by
    simpa [prefixWord, tailWord_234068, baseEnd_234068] using wordTrace_append hprefix tailTrace_234068
  have hstable : (prefixWord ++ tailWord_234068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234068).length < 2 ^ (prefixWord ++ tailWord_234068).sum := by decide
  have hdescent : baseEnd_234068 < baseStart_234068 := by decide
  rcases family_descends (prefixWord ++ tailWord_234068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234071 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 3]
def baseStart_234071 : Nat := 118140960795 + 234071 * 2 ^ 59
def prefixEnd_234071 : Nat := 4983230072969 + 3 ^ 40 * 234071 * 2
def baseEnd_234071 : Nat := 120190930278658929836033

theorem tailTrace_234071 : CollatzResearch.WordTrace tailWord_234071 prefixEnd_234071 120190930278658929836033 := by
  unfold tailWord_234071
  simp only [CollatzResearch.WordTrace]
  refine ⟨8537270735008217989246067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5691513823338811992830711 8537270735008217989246067)
  ·
    refine ⟨12805906102512326983869101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8537270735008217989246067 12805906102512326983869101)
    ·
      refine ⟨4802214788442122618950913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12805906102512326983869101 4802214788442122618950913)
      ·
        refine ⟨3601661091331591964213185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4802214788442122618950913 3601661091331591964213185)
        ·
          refine ⟨2701245818498693973159889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3601661091331591964213185 2701245818498693973159889)
          ·
            refine ⟨2025934363874020479869917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701245818498693973159889 2025934363874020479869917)
            ·
              refine ⟨759725386452757679951219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2025934363874020479869917 759725386452757679951219)
              ·
                refine ⟨1139588079679136519926829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759725386452757679951219 1139588079679136519926829)
                ·
                  refine ⟨427345529879676194972561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139588079679136519926829 427345529879676194972561)
                  ·
                    refine ⟨320509147409757146229421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 427345529879676194972561 320509147409757146229421)
                    ·
                      refine ⟨120190930278658929836033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 320509147409757146229421 120190930278658929836033)
                      ·
                        rfl

theorem cell23_234071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_234071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234071 prefixEnd_234071 := by exact prefixLift 234071
  have htrace : WordTrace (prefixWord ++ tailWord_234071) baseStart_234071 baseEnd_234071 := by
    simpa [prefixWord, tailWord_234071, baseEnd_234071] using wordTrace_append hprefix tailTrace_234071
  have hstable : (prefixWord ++ tailWord_234071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234071).length < 2 ^ (prefixWord ++ tailWord_234071).sum := by decide
  have hdescent : baseEnd_234071 < baseStart_234071 := by decide
  rcases family_descends (prefixWord ++ tailWord_234071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234081 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_234081 : Nat := 118140960795 + 234081 * 2 ^ 59
def prefixEnd_234081 : Nat := 4983230072969 + 3 ^ 40 * 234081 * 2
def baseEnd_234081 : Nat := 120196065085203890710987

theorem tailTrace_234081 : CollatzResearch.WordTrace tailWord_234081 prefixEnd_234081 120196065085203890710987 := by
  unfold tailWord_234081
  simp only [CollatzResearch.WordTrace]
  refine ⟨8537635464971989697110097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5691756976647993131406731 8537635464971989697110097)
  ·
    refine ⟨6403226598728992272832573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8537635464971989697110097 6403226598728992272832573)
    ·
      refine ⟨2401209974523372102312215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6403226598728992272832573 2401209974523372102312215)
      ·
        refine ⟨3601814961785058153468323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401209974523372102312215 3601814961785058153468323)
        ·
          refine ⟨5402722442677587230202485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3601814961785058153468323 5402722442677587230202485)
          ·
            refine ⟨506505229001023802831483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5402722442677587230202485 506505229001023802831483)
            ·
              refine ⟨759757843501535704247225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506505229001023802831483 759757843501535704247225)
              ·
                refine ⟨569818382626151778185419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759757843501535704247225 569818382626151778185419)
                ·
                  refine ⟨854727573939227667278129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569818382626151778185419 854727573939227667278129)
                  ·
                    refine ⟨641045680454420750458597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 854727573939227667278129 641045680454420750458597)
                    ·
                      refine ⟨120196065085203890710987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 641045680454420750458597 120196065085203890710987)
                      ·
                        rfl

theorem cell23_234081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_234081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234081 prefixEnd_234081 := by exact prefixLift 234081
  have htrace : WordTrace (prefixWord ++ tailWord_234081) baseStart_234081 baseEnd_234081 := by
    simpa [prefixWord, tailWord_234081, baseEnd_234081] using wordTrace_append hprefix tailTrace_234081
  have hstable : (prefixWord ++ tailWord_234081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234081).length < 2 ^ (prefixWord ++ tailWord_234081).sum := by decide
  have hdescent : baseEnd_234081 < baseStart_234081 := by decide
  rcases family_descends (prefixWord ++ tailWord_234081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234082 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_234082 : Nat := 118140960795 + 234082 * 2 ^ 59
def prefixEnd_234082 : Nat := 4983230072969 + 3 ^ 40 * 234082 * 2
def baseEnd_234082 : Nat := 40065526188619462266161

theorem tailTrace_234082 : CollatzResearch.WordTrace tailWord_234082 prefixEnd_234082 40065526188619462266161 := by
  unfold tailWord_234082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134417984492091716974125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5691781291978911245264333 2134417984492091716974125)
  ·
    refine ⟨800406744184534393865297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2134417984492091716974125 800406744184534393865297)
    ·
      refine ⟨600305058138400795398973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 800406744184534393865297 600305058138400795398973)
      ·
        refine ⟨225114396801900298274615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600305058138400795398973 225114396801900298274615)
        ·
          refine ⟨337671595202850447411923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225114396801900298274615 337671595202850447411923)
          ·
            refine ⟨506507392804275671117885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337671595202850447411923 506507392804275671117885)
            ·
              refine ⟨189940272301603376669207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506507392804275671117885 189940272301603376669207)
              ·
                refine ⟨284910408452405065003811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189940272301603376669207 284910408452405065003811)
                ·
                  refine ⟨427365612678607597505717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284910408452405065003811 427365612678607597505717)
                  ·
                    refine ⟨40065526188619462266161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 427365612678607597505717 40065526188619462266161)
                    ·
                      rfl

theorem cell23_234082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_234082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234082 prefixEnd_234082 := by exact prefixLift 234082
  have htrace : WordTrace (prefixWord ++ tailWord_234082) baseStart_234082 baseEnd_234082 := by
    simpa [prefixWord, tailWord_234082, baseEnd_234082] using wordTrace_append hprefix tailTrace_234082
  have hstable : (prefixWord ++ tailWord_234082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234082).length < 2 ^ (prefixWord ++ tailWord_234082).sum := by decide
  have hdescent : baseEnd_234082 < baseStart_234082 := by decide
  rcases family_descends (prefixWord ++ tailWord_234082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234085 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 1, 1, 4]
def baseStart_234085 : Nat := 118140960795 + 234085 * 2 ^ 59
def prefixEnd_234085 : Nat := 4983230072969 + 3 ^ 40 * 234085 * 2
def baseEnd_234085 : Nat := 120198119007821875060969

theorem tailTrace_234085 : CollatzResearch.WordTrace tailWord_234085 prefixEnd_234085 120198119007821875060969 := by
  unfold tailWord_234085
  simp only [CollatzResearch.WordTrace]
  refine ⟨8537781356957498380255709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5691854237971665586837139 8537781356957498380255709)
  ·
    refine ⟨3201668008859061892595891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8537781356957498380255709 3201668008859061892595891)
    ·
      refine ⟨4802502013288592838893837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3201668008859061892595891 4802502013288592838893837)
      ·
        refine ⟨1800938254983222314585189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4802502013288592838893837 1800938254983222314585189)
        ·
          refine ⟨337675922809354183984723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1800938254983222314585189 337675922809354183984723)
          ·
            refine ⟨506513884214031275977085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337675922809354183984723 506513884214031275977085)
            ·
              refine ⟨189942706580261728491407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506513884214031275977085 189942706580261728491407)
              ·
                refine ⟨284914059870392592737111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189942706580261728491407 284914059870392592737111)
                ·
                  refine ⟨427371089805588889105667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284914059870392592737111 427371089805588889105667)
                  ·
                    refine ⟨641056634708383333658501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 427371089805588889105667 641056634708383333658501)
                    ·
                      refine ⟨120198119007821875060969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 641056634708383333658501 120198119007821875060969)
                      ·
                        rfl

theorem cell23_234085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_234085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234085 prefixEnd_234085 := by exact prefixLift 234085
  have htrace : WordTrace (prefixWord ++ tailWord_234085) baseStart_234085 baseEnd_234085 := by
    simpa [prefixWord, tailWord_234085, baseEnd_234085] using wordTrace_append hprefix tailTrace_234085
  have hstable : (prefixWord ++ tailWord_234085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234085).length < 2 ^ (prefixWord ++ tailWord_234085).sum := by decide
  have hdescent : baseEnd_234085 < baseStart_234085 := by decide
  rcases family_descends (prefixWord ++ tailWord_234085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234175 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 1, 4, 2]
def baseStart_234175 : Nat := 118140960795 + 234175 * 2 ^ 59
def prefixEnd_234175 : Nat := 4983230072969 + 3 ^ 40 * 234175 * 2
def baseEnd_234175 : Nat := 120244332266726522935555

theorem tailTrace_234175 : CollatzResearch.WordTrace tailWord_234175 prefixEnd_234175 120244332266726522935555 := by
  unfold tailWord_234175
  simp only [CollatzResearch.WordTrace]
  refine ⟨8541063926631443751031979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5694042617754295834021319 8541063926631443751031979)
  ·
    refine ⟨12811595889947165626547969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8541063926631443751031979 12811595889947165626547969)
    ·
      refine ⟨9608696917460374219910977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12811595889947165626547969 9608696917460374219910977)
      ·
        refine ⟨7206522688095280664933233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9608696917460374219910977 7206522688095280664933233)
        ·
          refine ⟨5404892016071460498699925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7206522688095280664933233 5404892016071460498699925)
          ·
            refine ⟨253354313253349710876559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5404892016071460498699925 253354313253349710876559)
            ·
              refine ⟨380031469880024566314839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253354313253349710876559 380031469880024566314839)
              ·
                refine ⟨570047204820036849472259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380031469880024566314839 570047204820036849472259)
                ·
                  refine ⟨855070807230055274208389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570047204820036849472259 855070807230055274208389)
                  ·
                    refine ⟨160325776355635363914073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 855070807230055274208389 160325776355635363914073)
                    ·
                      refine ⟨120244332266726522935555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160325776355635363914073 120244332266726522935555)
                      ·
                        rfl

theorem cell23_234175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_234175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234175 prefixEnd_234175 := by exact prefixLift 234175
  have htrace : WordTrace (prefixWord ++ tailWord_234175) baseStart_234175 baseEnd_234175 := by
    simpa [prefixWord, tailWord_234175, baseEnd_234175] using wordTrace_append hprefix tailTrace_234175
  have hstable : (prefixWord ++ tailWord_234175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234175).length < 2 ^ (prefixWord ++ tailWord_234175).sum := by decide
  have hdescent : baseEnd_234175 < baseStart_234175 := by decide
  rcases family_descends (prefixWord ++ tailWord_234175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234218 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_234218 : Nat := 118140960795 + 234218 * 2 ^ 59
def prefixEnd_234218 : Nat := 4983230072969 + 3 ^ 40 * 234218 * 2
def baseEnd_234218 : Nat := 120266411934869854697857

theorem tailTrace_234218 : CollatzResearch.WordTrace tailWord_234218 prefixEnd_234218 120266411934869854697857 := by
  unfold tailWord_234218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2135658066368915523711827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5695088176983774729898205 2135658066368915523711827)
  ·
    refine ⟨3203487099553373285567741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2135658066368915523711827 3203487099553373285567741)
    ·
      refine ⟨1201307662332514982087903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3203487099553373285567741 1201307662332514982087903)
      ·
        refine ⟨1801961493498772473131855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201307662332514982087903 1801961493498772473131855)
        ·
          refine ⟨2702942240248158709697783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801961493498772473131855 2702942240248158709697783)
          ·
            refine ⟨4054413360372238064546675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702942240248158709697783 4054413360372238064546675)
            ·
              refine ⟨6081620040558357096820013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054413360372238064546675 6081620040558357096820013)
              ·
                refine ⟨2280607515209383911307505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6081620040558357096820013 2280607515209383911307505)
                ·
                  refine ⟨1710455636407037933480629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2280607515209383911307505 1710455636407037933480629)
                  ·
                    refine ⟨160355215913159806263809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1710455636407037933480629 160355215913159806263809)
                    ·
                      refine ⟨120266411934869854697857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160355215913159806263809 120266411934869854697857)
                      ·
                        rfl

theorem cell23_234218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_234218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234218 prefixEnd_234218 := by exact prefixLift 234218
  have htrace : WordTrace (prefixWord ++ tailWord_234218) baseStart_234218 baseEnd_234218 := by
    simpa [prefixWord, tailWord_234218, baseEnd_234218] using wordTrace_append hprefix tailTrace_234218
  have hstable : (prefixWord ++ tailWord_234218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234218).length < 2 ^ (prefixWord ++ tailWord_234218).sum := by decide
  have hdescent : baseEnd_234218 < baseStart_234218 := by decide
  rcases family_descends (prefixWord ++ tailWord_234218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234231 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_234231 : Nat := 118140960795 + 234231 * 2 ^ 59
def prefixEnd_234231 : Nat := 4983230072969 + 3 ^ 40 * 234231 * 2
def baseEnd_234231 : Nat := 120273087183378303835297

theorem tailTrace_234231 : CollatzResearch.WordTrace tailWord_234231 prefixEnd_234231 120273087183378303835297 := by
  unfold tailWord_234231
  simp only [CollatzResearch.WordTrace]
  refine ⟨8543106414428565315070547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5695404276285710210047031 8543106414428565315070547)
  ·
    refine ⟨12814659621642847972605821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8543106414428565315070547 12814659621642847972605821)
    ·
      refine ⟨4805497358116067989727183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12814659621642847972605821 4805497358116067989727183)
      ·
        refine ⟨7208246037174101984590775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4805497358116067989727183 7208246037174101984590775)
        ·
          refine ⟨10812369055761152976886163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7208246037174101984590775 10812369055761152976886163)
          ·
            refine ⟨16218553583641729465329245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10812369055761152976886163 16218553583641729465329245)
            ·
              refine ⟨6081957593865648549498467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16218553583641729465329245 6081957593865648549498467)
              ·
                refine ⟨9122936390798472824247701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081957593865648549498467 9122936390798472824247701)
                ·
                  refine ⟨427637643318678413636611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9122936390798472824247701 427637643318678413636611)
                  ·
                    refine ⟨641456464978017620454917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 427637643318678413636611 641456464978017620454917)
                    ·
                      refine ⟨120273087183378303835297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 641456464978017620454917 120273087183378303835297)
                      ·
                        rfl

theorem cell23_234231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_234231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234231 prefixEnd_234231 := by exact prefixLift 234231
  have htrace : WordTrace (prefixWord ++ tailWord_234231) baseStart_234231 baseEnd_234231 := by
    simpa [prefixWord, tailWord_234231, baseEnd_234231] using wordTrace_append hprefix tailTrace_234231
  have hstable : (prefixWord ++ tailWord_234231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234231).length < 2 ^ (prefixWord ++ tailWord_234231).sum := by decide
  have hdescent : baseEnd_234231 < baseStart_234231 := by decide
  rcases family_descends (prefixWord ++ tailWord_234231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234248 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_234248 : Nat := 118140960795 + 234248 * 2 ^ 59
def prefixEnd_234248 : Nat := 4983230072969 + 3 ^ 40 * 234248 * 2
def baseEnd_234248 : Nat := 120281816354504737322719

theorem tailTrace_234248 : CollatzResearch.WordTrace tailWord_234248 prefixEnd_234248 120281816354504737322719 := by
  unfold tailWord_234248
  simp only [CollatzResearch.WordTrace]
  refine ⟨4271863227683488609219699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5695817636911318145626265 4271863227683488609219699)
  ·
    refine ⟨6407794841525232913829549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4271863227683488609219699 6407794841525232913829549)
    ·
      refine ⟨2402923065571962342686081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6407794841525232913829549 2402923065571962342686081)
      ·
        refine ⟨1802192299178971757014561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2402923065571962342686081 1802192299178971757014561)
        ·
          refine ⟨1351644224384228817760921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802192299178971757014561 1351644224384228817760921)
          ·
            refine ⟨1013733168288171613320691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351644224384228817760921 1013733168288171613320691)
            ·
              refine ⟨1520599752432257419981037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013733168288171613320691 1520599752432257419981037)
              ·
                refine ⟨570224907162096532492889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1520599752432257419981037 570224907162096532492889)
                ·
                  refine ⟨427668680371572399369667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570224907162096532492889 427668680371572399369667)
                  ·
                    refine ⟨641503020557358599054501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 427668680371572399369667 641503020557358599054501)
                    ·
                      refine ⟨120281816354504737322719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 641503020557358599054501 120281816354504737322719)
                      ·
                        rfl

theorem cell23_234248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_234248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234248 prefixEnd_234248 := by exact prefixLift 234248
  have htrace : WordTrace (prefixWord ++ tailWord_234248) baseStart_234248 baseEnd_234248 := by
    simpa [prefixWord, tailWord_234248, baseEnd_234248] using wordTrace_append hprefix tailTrace_234248
  have hstable : (prefixWord ++ tailWord_234248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234248).length < 2 ^ (prefixWord ++ tailWord_234248).sum := by decide
  have hdescent : baseEnd_234248 < baseStart_234248 := by decide
  rcases family_descends (prefixWord ++ tailWord_234248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234261 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_234261 : Nat := 118140960795 + 234261 * 2 ^ 59
def prefixEnd_234261 : Nat := 4983230072969 + 3 ^ 40 * 234261 * 2
def baseEnd_234261 : Nat := 120288491603013186460159

theorem tailTrace_234261 : CollatzResearch.WordTrace tailWord_234261 prefixEnd_234261 120288491603013186460159 := by
  unfold tailWord_234261
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544200604319880438662637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5696133736213253625775091 8544200604319880438662637)
  ·
    refine ⟨3204075226619955164498489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8544200604319880438662637 3204075226619955164498489)
    ·
      refine ⟨2403056419964966373373867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3204075226619955164498489 2403056419964966373373867)
      ·
        refine ⟨3604584629947449560060801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403056419964966373373867 3604584629947449560060801)
        ·
          refine ⟨2703438472460587170045601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3604584629947449560060801 2703438472460587170045601)
          ·
            refine ⟨2027578854345440377534201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2703438472460587170045601 2027578854345440377534201)
            ·
              refine ⟨1520684140759080283150651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027578854345440377534201 1520684140759080283150651)
              ·
                refine ⟨2281026211138620424725977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520684140759080283150651 2281026211138620424725977)
                ·
                  refine ⟨1710769658353965318544483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2281026211138620424725977 1710769658353965318544483)
                  ·
                    refine ⟨2566154487530947977816725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1710769658353965318544483 2566154487530947977816725)
                    ·
                      refine ⟨120288491603013186460159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2566154487530947977816725 120288491603013186460159)
                      ·
                        rfl

theorem cell23_234261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_234261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234261 prefixEnd_234261 := by exact prefixLift 234261
  have htrace : WordTrace (prefixWord ++ tailWord_234261) baseStart_234261 baseEnd_234261 := by
    simpa [prefixWord, tailWord_234261, baseEnd_234261] using wordTrace_append hprefix tailTrace_234261
  have hstable : (prefixWord ++ tailWord_234261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234261).length < 2 ^ (prefixWord ++ tailWord_234261).sum := by decide
  have hdescent : baseEnd_234261 < baseStart_234261 := by decide
  rcases family_descends (prefixWord ++ tailWord_234261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234292 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_234292 : Nat := 118140960795 + 234292 * 2 ^ 59
def prefixEnd_234292 : Nat := 4983230072969 + 3 ^ 40 * 234292 * 2
def baseEnd_234292 : Nat := 40101469834434188390839

theorem tailTrace_234292 : CollatzResearch.WordTrace tailWord_234292 prefixEnd_234292 40101469834434188390839 := by
  unfold tailWord_234292
  simp only [CollatzResearch.WordTrace]
  refine ⟨4272665633603786366520565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5696887511471715155360753 4272665633603786366520565)
  ·
    refine ⟨400562403150354971861303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4272665633603786366520565 400562403150354971861303)
    ·
      refine ⟨600843604725532457791955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400562403150354971861303 600843604725532457791955)
      ·
        refine ⟨901265407088298686687933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600843604725532457791955 901265407088298686687933)
        ·
          refine ⟨337974527658112007507975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 901265407088298686687933 337974527658112007507975)
          ·
            refine ⟨506961791487168011261963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337974527658112007507975 506961791487168011261963)
            ·
              refine ⟨760442687230752016892945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506961791487168011261963 760442687230752016892945)
              ·
                refine ⟨570332015423064012669709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 760442687230752016892945 570332015423064012669709)
                ·
                  refine ⟨213874505783649004751141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570332015423064012669709 213874505783649004751141)
                  ·
                    refine ⟨40101469834434188390839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 213874505783649004751141 40101469834434188390839)
                    ·
                      rfl

theorem cell23_234292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_234292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234292 prefixEnd_234292 := by exact prefixLift 234292
  have htrace : WordTrace (prefixWord ++ tailWord_234292) baseStart_234292 baseEnd_234292 := by
    simpa [prefixWord, tailWord_234292, baseEnd_234292] using wordTrace_append hprefix tailTrace_234292
  have hstable : (prefixWord ++ tailWord_234292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234292).length < 2 ^ (prefixWord ++ tailWord_234292).sum := by decide
  have hdescent : baseEnd_234292 < baseStart_234292 := by decide
  rcases family_descends (prefixWord ++ tailWord_234292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234311 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_234311 : Nat := 118140960795 + 234311 * 2 ^ 59
def prefixEnd_234311 : Nat := 4983230072969 + 3 ^ 40 * 234311 * 2
def baseEnd_234311 : Nat := 120314165635737990834929

theorem tailTrace_234311 : CollatzResearch.WordTrace tailWord_234311 prefixEnd_234311 120314165635737990834929 := by
  unfold tailWord_234311
  simp only [CollatzResearch.WordTrace]
  refine ⟨8546024254138738977982787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5697349502759159318655191 8546024254138738977982787)
  ·
    refine ⟨12819036381208108466974181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8546024254138738977982787 12819036381208108466974181)
    ·
      refine ⟨2403569321476520337557659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12819036381208108466974181 2403569321476520337557659)
      ·
        refine ⟨3605353982214780506336489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403569321476520337557659 3605353982214780506336489)
        ·
          refine ⟨2704015486661085379752367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3605353982214780506336489 2704015486661085379752367)
          ·
            refine ⟨4056023229991628069628551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704015486661085379752367 4056023229991628069628551)
            ·
              refine ⟨6084034844987442104442827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056023229991628069628551 6084034844987442104442827)
              ·
                refine ⟨9126052267481163156664241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084034844987442104442827 9126052267481163156664241)
                ·
                  refine ⟨6844539200610872367498181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9126052267481163156664241 6844539200610872367498181)
                  ·
                    refine ⟨1283351100114538568905909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6844539200610872367498181 1283351100114538568905909)
                    ·
                      refine ⟨120314165635737990834929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1283351100114538568905909 120314165635737990834929)
                      ·
                        rfl

theorem cell23_234311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_234311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234311 prefixEnd_234311 := by exact prefixLift 234311
  have htrace : WordTrace (prefixWord ++ tailWord_234311) baseStart_234311 baseEnd_234311 := by
    simpa [prefixWord, tailWord_234311, baseEnd_234311] using wordTrace_append hprefix tailTrace_234311
  have hstable : (prefixWord ++ tailWord_234311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234311).length < 2 ^ (prefixWord ++ tailWord_234311).sum := by decide
  have hdescent : baseEnd_234311 < baseStart_234311 := by decide
  rcases family_descends (prefixWord ++ tailWord_234311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234325 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 4, 3, 2]
def baseStart_234325 : Nat := 118140960795 + 234325 * 2 ^ 59
def prefixEnd_234325 : Nat := 4983230072969 + 3 ^ 40 * 234325 * 2
def baseEnd_234325 : Nat := 120321354364900936059865

theorem tailTrace_234325 : CollatzResearch.WordTrace tailWord_234325 prefixEnd_234325 120321354364900936059865 := by
  unfold tailWord_234325
  simp only [CollatzResearch.WordTrace]
  refine ⟨8546534876088019368992429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5697689917392012912661619 8546534876088019368992429)
  ·
    refine ⟨3204950578533007263372161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8546534876088019368992429 3204950578533007263372161)
    ·
      refine ⟨2403712933899755447529121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3204950578533007263372161 2403712933899755447529121)
      ·
        refine ⟨1802784700424816585646841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403712933899755447529121 1802784700424816585646841)
        ·
          refine ⟨1352088525318612439235131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802784700424816585646841 1352088525318612439235131)
          ·
            refine ⟨2028132787977918658852697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352088525318612439235131 2028132787977918658852697)
            ·
              refine ⟨1521099590983438994139523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2028132787977918658852697 1521099590983438994139523)
              ·
                refine ⟨2281649386475158491209285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521099590983438994139523 2281649386475158491209285)
                ·
                  refine ⟨427809259964092217101741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281649386475158491209285 427809259964092217101741)
                  ·
                    refine ⟨160428472486534581413153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 427809259964092217101741 160428472486534581413153)
                    ·
                      refine ⟨120321354364900936059865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160428472486534581413153 120321354364900936059865)
                      ·
                        rfl

theorem cell23_234325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_234325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234325 prefixEnd_234325 := by exact prefixLift 234325
  have htrace : WordTrace (prefixWord ++ tailWord_234325) baseStart_234325 baseEnd_234325 := by
    simpa [prefixWord, tailWord_234325, baseEnd_234325] using wordTrace_append hprefix tailTrace_234325
  have hstable : (prefixWord ++ tailWord_234325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234325).length < 2 ^ (prefixWord ++ tailWord_234325).sum := by decide
  have hdescent : baseEnd_234325 < baseStart_234325 := by decide
  rcases family_descends (prefixWord ++ tailWord_234325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234332 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_234332 : Nat := 118140960795 + 234332 * 2 ^ 59
def prefixEnd_234332 : Nat := 4983230072969 + 3 ^ 40 * 234332 * 2
def baseEnd_234332 : Nat := 120324948729482408672333

theorem tailTrace_234332 : CollatzResearch.WordTrace tailWord_234332 prefixEnd_234332 120324948729482408672333 := by
  unfold tailWord_234332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4273395093531329782248625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5697860124708439709664833 4273395093531329782248625)
  ·
    refine ⟨3205046320148497336686469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4273395093531329782248625 3205046320148497336686469)
    ·
      refine ⟨600946185027843250628713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3205046320148497336686469 600946185027843250628713)
      ·
        refine ⟨450709638770882437971535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600946185027843250628713 450709638770882437971535)
        ·
          refine ⟨676064458156323656957303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450709638770882437971535 676064458156323656957303)
          ·
            refine ⟨1014096687234485485435955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676064458156323656957303 1014096687234485485435955)
            ·
              refine ⟨1521145030851728228153933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014096687234485485435955 1521145030851728228153933)
              ·
                refine ⟨570429386569398085557725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1521145030851728228153933 570429386569398085557725)
                ·
                  refine ⟨213911019963524282084147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570429386569398085557725 213911019963524282084147)
                  ·
                    refine ⟨320866529945286423126221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213911019963524282084147 320866529945286423126221)
                    ·
                      refine ⟨120324948729482408672333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 320866529945286423126221 120324948729482408672333)
                      ·
                        rfl

theorem cell23_234332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_234332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234332 prefixEnd_234332 := by exact prefixLift 234332
  have htrace : WordTrace (prefixWord ++ tailWord_234332) baseStart_234332 baseEnd_234332 := by
    simpa [prefixWord, tailWord_234332, baseEnd_234332] using wordTrace_append hprefix tailTrace_234332
  have hstable : (prefixWord ++ tailWord_234332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234332).length < 2 ^ (prefixWord ++ tailWord_234332).sum := by decide
  have hdescent : baseEnd_234332 < baseStart_234332 := by decide
  rcases family_descends (prefixWord ++ tailWord_234332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234375 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_234375 : Nat := 118140960795 + 234375 * 2 ^ 59
def prefixEnd_234375 : Nat := 4983230072969 + 3 ^ 40 * 234375 * 2
def baseEnd_234375 : Nat := 120347028397625740434635

theorem tailTrace_234375 : CollatzResearch.WordTrace tailWord_234375 prefixEnd_234375 120347028397625740434635 := by
  unfold tailWord_234375
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548358525906877908312579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5698905683937918605541719 8548358525906877908312579)
  ·
    refine ⟨12822537788860316862468869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8548358525906877908312579 12822537788860316862468869)
    ·
      refine ⟨2404225835411309411712913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12822537788860316862468869 2404225835411309411712913)
      ·
        refine ⟨1803169376558482058784685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2404225835411309411712913 1803169376558482058784685)
        ·
          refine ⟨676188516209430772044257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1803169376558482058784685 676188516209430772044257)
          ·
            refine ⟨507141387157073079033193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676188516209430772044257 507141387157073079033193)
            ·
              refine ⟨380356040367804809274895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507141387157073079033193 380356040367804809274895)
              ·
                refine ⟨570534060551707213912343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380356040367804809274895 570534060551707213912343)
                ·
                  refine ⟨855801090827560820868515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570534060551707213912343 855801090827560820868515)
                  ·
                    refine ⟨1283701636241341231302773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 855801090827560820868515 1283701636241341231302773)
                    ·
                      refine ⟨120347028397625740434635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1283701636241341231302773 120347028397625740434635)
                      ·
                        rfl

theorem cell23_234375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_234375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234375 prefixEnd_234375 := by exact prefixLift 234375
  have htrace : WordTrace (prefixWord ++ tailWord_234375) baseStart_234375 baseEnd_234375 := by
    simpa [prefixWord, tailWord_234375, baseEnd_234375] using wordTrace_append hprefix tailTrace_234375
  have hstable : (prefixWord ++ tailWord_234375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234375).length < 2 ^ (prefixWord ++ tailWord_234375).sum := by decide
  have hdescent : baseEnd_234375 < baseStart_234375 := by decide
  rcases family_descends (prefixWord ++ tailWord_234375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234378 : List Nat := [3, 1, 2, 4, 1, 1, 11]
def baseStart_234378 : Nat := 118140960795 + 234378 * 2 ^ 59
def prefixEnd_234378 : Nat := 4983230072969 + 3 ^ 40 * 234378 * 2
def baseEnd_234378 : Nat := 1485784800488755909841

theorem tailTrace_234378 : CollatzResearch.WordTrace tailWord_234378 prefixEnd_234378 1485784800488755909841 := by
  unfold tailWord_234378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137116986224002355167947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5698978629930672947114525 2137116986224002355167947)
  ·
    refine ⟨3205675479336003532751921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2137116986224002355167947 3205675479336003532751921)
    ·
      refine ⟨2404256609502002649563941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3205675479336003532751921 2404256609502002649563941)
      ·
        refine ⟨450798114281625496793239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2404256609502002649563941 450798114281625496793239)
        ·
          refine ⟨676197171422438245189859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450798114281625496793239 676197171422438245189859)
          ·
            refine ⟨1014295757133657367784789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676197171422438245189859 1014295757133657367784789)
            ·
              refine ⟨1485784800488755909841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1014295757133657367784789 1485784800488755909841)
              ·
                rfl

theorem cell23_234378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 11].length) (baseStart_234378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234378 prefixEnd_234378 := by exact prefixLift 234378
  have htrace : WordTrace (prefixWord ++ tailWord_234378) baseStart_234378 baseEnd_234378 := by
    simpa [prefixWord, tailWord_234378, baseEnd_234378] using wordTrace_append hprefix tailTrace_234378
  have hstable : (prefixWord ++ tailWord_234378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234378).length < 2 ^ (prefixWord ++ tailWord_234378).sum := by decide
  have hdescent : baseEnd_234378 < baseStart_234378 := by decide
  rcases family_descends (prefixWord ++ tailWord_234378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234389 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 3, 2, 2]
def baseStart_234389 : Nat := 118140960795 + 234389 * 2 ^ 59
def prefixEnd_234389 : Nat := 4983230072969 + 3 ^ 40 * 234389 * 2
def baseEnd_234389 : Nat := 120354217126788685659571

theorem tailTrace_234389 : CollatzResearch.WordTrace tailWord_234389 prefixEnd_234389 120354217126788685659571 := by
  unfold tailWord_234389
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548869147856158299322221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5699246098570772199548147 8548869147856158299322221)
  ·
    refine ⟨3205825930446059362245833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8548869147856158299322221 3205825930446059362245833)
    ·
      refine ⟨2404369447834544521684375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3205825930446059362245833 2404369447834544521684375)
      ·
        refine ⟨3606554171751816782526563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404369447834544521684375 3606554171751816782526563)
        ·
          refine ⟨5409831257627725173789845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606554171751816782526563 5409831257627725173789845)
          ·
            refine ⟨253585840201299617521399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5409831257627725173789845 253585840201299617521399)
            ·
              refine ⟨380378760301949426282099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253585840201299617521399 380378760301949426282099)
              ·
                refine ⟨570568140452924139423149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380378760301949426282099 570568140452924139423149)
                ·
                  refine ⟨213963052669846552283681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570568140452924139423149 213963052669846552283681)
                  ·
                    refine ⟨160472289502384914212761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213963052669846552283681 160472289502384914212761)
                    ·
                      refine ⟨120354217126788685659571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160472289502384914212761 120354217126788685659571)
                      ·
                        rfl

theorem cell23_234389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_234389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234389 prefixEnd_234389 := by exact prefixLift 234389
  have htrace : WordTrace (prefixWord ++ tailWord_234389) baseStart_234389 baseEnd_234389 := by
    simpa [prefixWord, tailWord_234389, baseEnd_234389] using wordTrace_append hprefix tailTrace_234389
  have hstable : (prefixWord ++ tailWord_234389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234389).length < 2 ^ (prefixWord ++ tailWord_234389).sum := by decide
  have hdescent : baseEnd_234389 < baseStart_234389 := by decide
  rcases family_descends (prefixWord ++ tailWord_234389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234399 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 2, 4]
def baseStart_234399 : Nat := 118140960795 + 234399 * 2 ^ 59
def prefixEnd_234399 : Nat := 4983230072969 + 3 ^ 40 * 234399 * 2
def baseEnd_234399 : Nat := 40119783977777882178175

theorem tailTrace_234399 : CollatzResearch.WordTrace tailWord_234399 prefixEnd_234399 40119783977777882178175 := by
  unfold tailWord_234399
  simp only [CollatzResearch.WordTrace]
  refine ⟨8549233877819930007186251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5699489251879953338124167 8549233877819930007186251)
  ·
    refine ⟨12823850816729895010779377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8549233877819930007186251 12823850816729895010779377)
    ·
      refine ⟨9617888112547421258084533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12823850816729895010779377 9617888112547421258084533)
      ·
        refine ⟨901677010551320742945425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9617888112547421258084533 901677010551320742945425)
        ·
          refine ⟨676257757913490557209069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901677010551320742945425 676257757913490557209069)
          ·
            refine ⟨253596659217558958953401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 676257757913490557209069 253596659217558958953401)
            ·
              refine ⟨190197494413169219215051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253596659217558958953401 190197494413169219215051)
              ·
                refine ⟨285296241619753828822577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190197494413169219215051 285296241619753828822577)
                ·
                  refine ⟨213972181214815371616933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285296241619753828822577 213972181214815371616933)
                  ·
                    refine ⟨40119783977777882178175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 213972181214815371616933 40119783977777882178175)
                    ·
                      rfl

theorem cell23_234399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 4].length) (baseStart_234399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234399 prefixEnd_234399 := by exact prefixLift 234399
  have htrace : WordTrace (prefixWord ++ tailWord_234399) baseStart_234399 baseEnd_234399 := by
    simpa [prefixWord, tailWord_234399, baseEnd_234399] using wordTrace_append hprefix tailTrace_234399
  have hstable : (prefixWord ++ tailWord_234399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234399).length < 2 ^ (prefixWord ++ tailWord_234399).sum := by decide
  have hdescent : baseEnd_234399 < baseStart_234399 := by decide
  rcases family_descends (prefixWord ++ tailWord_234399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234440 : List Nat := [2, 1, 3, 1, 6, 1, 2, 2, 1, 2, 2]
def baseStart_234440 : Nat := 118140960795 + 234440 * 2 ^ 59
def prefixEnd_234440 : Nat := 4983230072969 + 3 ^ 40 * 234440 * 2
def baseEnd_234440 : Nat := 120380404640167986121837

theorem tailTrace_234440 : CollatzResearch.WordTrace tailWord_234440 prefixEnd_234440 120380404640167986121837 := by
  unfold tailWord_234440
  simp only [CollatzResearch.WordTrace]
  refine ⟨4275364635335697004714387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5700486180447596006285849 4275364635335697004714387)
  ·
    refine ⟨6413046953003545507071581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4275364635335697004714387 6413046953003545507071581)
    ·
      refine ⟨2404892607376329565151843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6413046953003545507071581 2404892607376329565151843)
      ·
        refine ⟨3607338911064494347727765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404892607376329565151843 3607338911064494347727765)
        ·
          refine ⟨169094011456148172549739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3607338911064494347727765 169094011456148172549739)
          ·
            refine ⟨253641017184222258824609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169094011456148172549739 253641017184222258824609)
            ·
              refine ⟨190230762888166694118457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253641017184222258824609 190230762888166694118457)
              ·
                refine ⟨142673072166125020588843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190230762888166694118457 142673072166125020588843)
                ·
                  refine ⟨214009608249187530883265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142673072166125020588843 214009608249187530883265)
                  ·
                    refine ⟨160507206186890648162449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214009608249187530883265 160507206186890648162449)
                    ·
                      refine ⟨120380404640167986121837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160507206186890648162449 120380404640167986121837)
                      ·
                        rfl

theorem cell23_234440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_234440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234440 prefixEnd_234440 := by exact prefixLift 234440
  have htrace : WordTrace (prefixWord ++ tailWord_234440) baseStart_234440 baseEnd_234440 := by
    simpa [prefixWord, tailWord_234440, baseEnd_234440] using wordTrace_append hprefix tailTrace_234440
  have hstable : (prefixWord ++ tailWord_234440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234440).length < 2 ^ (prefixWord ++ tailWord_234440).sum := by decide
  have hdescent : baseEnd_234440 < baseStart_234440 := by decide
  rcases family_descends (prefixWord ++ tailWord_234440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234505 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 1, 7, 2]
def baseStart_234505 : Nat := 118140960795 + 234505 * 2 ^ 59
def prefixEnd_234505 : Nat := 4983230072969 + 3 ^ 40 * 234505 * 2
def baseEnd_234505 : Nat := 120413780882710231809037

theorem tailTrace_234505 : CollatzResearch.WordTrace tailWord_234505 prefixEnd_234505 120413780882710231809037 := by
  unfold tailWord_234505
  simp only [CollatzResearch.WordTrace]
  refine ⟨8553100015435910110544969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5702066676957273407029979 8553100015435910110544969)
  ·
    refine ⟨6414825011576932582908727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8553100015435910110544969 6414825011576932582908727)
    ·
      refine ⟨9622237517365398874363091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6414825011576932582908727 9622237517365398874363091)
      ·
        refine ⟨14433356276048098311544637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9622237517365398874363091 14433356276048098311544637)
        ·
          refine ⟨5412508603518036866829239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14433356276048098311544637 5412508603518036866829239)
          ·
            refine ⟨8118762905277055300243859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412508603518036866829239 8118762905277055300243859)
            ·
              refine ⟨12178144357915582950365789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8118762905277055300243859 12178144357915582950365789)
              ·
                refine ⟨4566804134218343606387171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12178144357915582950365789 4566804134218343606387171)
                ·
                  refine ⟨6850206201327515409580757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566804134218343606387171 6850206201327515409580757)
                  ·
                    refine ⟨160551707843613642412049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6850206201327515409580757 160551707843613642412049)
                    ·
                      refine ⟨120413780882710231809037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160551707843613642412049 120413780882710231809037)
                      ·
                        rfl

theorem cell23_234505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 7, 2].length) (baseStart_234505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234505 prefixEnd_234505 := by exact prefixLift 234505
  have htrace : WordTrace (prefixWord ++ tailWord_234505) baseStart_234505 baseEnd_234505 := by
    simpa [prefixWord, tailWord_234505, baseEnd_234505] using wordTrace_append hprefix tailTrace_234505
  have hstable : (prefixWord ++ tailWord_234505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234505).length < 2 ^ (prefixWord ++ tailWord_234505).sum := by decide
  have hdescent : baseEnd_234505 < baseStart_234505 := by decide
  rcases family_descends (prefixWord ++ tailWord_234505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234552 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_234552 : Nat := 118140960795 + 234552 * 2 ^ 59
def prefixEnd_234552 : Nat := 4983230072969 + 3 ^ 40 * 234552 * 2
def baseEnd_234552 : Nat := 120437914473471547921321

theorem tailTrace_234552 : CollatzResearch.WordTrace tailWord_234552 prefixEnd_234552 120437914473471547921321 := by
  unfold tailWord_234552
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277407123132818568752955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5703209497510424758337273 4277407123132818568752955)
  ·
    refine ⟨6416110684699227853129433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4277407123132818568752955 6416110684699227853129433)
    ·
      refine ⟨4812083013524420889847075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6416110684699227853129433 4812083013524420889847075)
      ·
        refine ⟨7218124520286631334770613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4812083013524420889847075 7218124520286631334770613)
        ·
          refine ⟨676699173776871687634745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7218124520286631334770613 676699173776871687634745)
          ·
            refine ⟨507524380332653765726059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676699173776871687634745 507524380332653765726059)
            ·
              refine ⟨761286570498980648589089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507524380332653765726059 761286570498980648589089)
              ·
                refine ⟨570964927874235486441817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761286570498980648589089 570964927874235486441817)
                ·
                  refine ⟨428223695905676614831363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570964927874235486441817 428223695905676614831363)
                  ·
                    refine ⟨642335543858514922247045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 428223695905676614831363 642335543858514922247045)
                    ·
                      refine ⟨120437914473471547921321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 642335543858514922247045 120437914473471547921321)
                      ·
                        rfl

theorem cell23_234552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_234552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234552 prefixEnd_234552 := by exact prefixLift 234552
  have htrace : WordTrace (prefixWord ++ tailWord_234552) baseStart_234552 baseEnd_234552 := by
    simpa [prefixWord, tailWord_234552, baseEnd_234552] using wordTrace_append hprefix tailTrace_234552
  have hstable : (prefixWord ++ tailWord_234552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234552).length < 2 ^ (prefixWord ++ tailWord_234552).sum := by decide
  have hdescent : baseEnd_234552 < baseStart_234552 := by decide
  rcases family_descends (prefixWord ++ tailWord_234552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234613 : List Nat := [1, 3, 4, 3, 1, 1, 1, 4, 1, 4]
def baseStart_234613 : Nat := 118140960795 + 234613 * 2 ^ 59
def prefixEnd_234613 : Nat := 4983230072969 + 3 ^ 40 * 234613 * 2
def baseEnd_234613 : Nat := 40156412264465269752847

theorem tailTrace_234613 : CollatzResearch.WordTrace tailWord_234613 prefixEnd_234613 40156412264465269752847 := by
  unfold tailWord_234613
  simp only [CollatzResearch.WordTrace]
  refine ⟨8557039099044644555476493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5704692732696429703650995 8557039099044644555476493)
  ·
    refine ⟨3208889662141741708303685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8557039099044644555476493 3208889662141741708303685)
    ·
      refine ⟨601666811651576570306941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3208889662141741708303685 601666811651576570306941)
      ·
        refine ⟨225625054369341213865103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601666811651576570306941 225625054369341213865103)
        ·
          refine ⟨338437581554011820797655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225625054369341213865103 338437581554011820797655)
          ·
            refine ⟨507656372331017731196483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338437581554011820797655 507656372331017731196483)
            ·
              refine ⟨761484558496526596794725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507656372331017731196483 761484558496526596794725)
              ·
                refine ⟨142778354718098736899011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 761484558496526596794725 142778354718098736899011)
                ·
                  refine ⟨214167532077148105348517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142778354718098736899011 214167532077148105348517)
                  ·
                    refine ⟨40156412264465269752847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214167532077148105348517 40156412264465269752847)
                    ·
                      rfl

theorem cell23_234613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_234613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234613 prefixEnd_234613 := by exact prefixLift 234613
  have htrace : WordTrace (prefixWord ++ tailWord_234613) baseStart_234613 baseEnd_234613 := by
    simpa [prefixWord, tailWord_234613, baseEnd_234613] using wordTrace_append hprefix tailTrace_234613
  have hstable : (prefixWord ++ tailWord_234613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234613).length < 2 ^ (prefixWord ++ tailWord_234613).sum := by decide
  have hdescent : baseEnd_234613 < baseStart_234613 := by decide
  rcases family_descends (prefixWord ++ tailWord_234613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234645 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_234645 : Nat := 118140960795 + 234645 * 2 ^ 59
def prefixEnd_234645 : Nat := 4983230072969 + 3 ^ 40 * 234645 * 2
def baseEnd_234645 : Nat := 120485668174339684058393

theorem tailTrace_234645 : CollatzResearch.WordTrace tailWord_234645 prefixEnd_234645 120485668174339684058393 := by
  unfold tailWord_234645
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558206234928714020641389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5705470823285809347094259 8558206234928714020641389)
  ·
    refine ⟨3209327338098267757740521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8558206234928714020641389 3209327338098267757740521)
    ·
      refine ⟨2406995503573700818305391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3209327338098267757740521 2406995503573700818305391)
      ·
        refine ⟨3610493255360551227458087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406995503573700818305391 3610493255360551227458087)
        ·
          refine ⟨5415739883040826841187131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610493255360551227458087 5415739883040826841187131)
          ·
            refine ⟨8123609824561240261780697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415739883040826841187131 8123609824561240261780697)
            ·
              refine ⟨6092707368420930196335523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8123609824561240261780697 6092707368420930196335523)
              ·
                refine ⟨9139061052631395294503285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6092707368420930196335523 9139061052631395294503285)
                ·
                  refine ⟨856786973684193308859683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9139061052631395294503285 856786973684193308859683)
                  ·
                    refine ⟨1285180460526289963289525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 856786973684193308859683 1285180460526289963289525)
                    ·
                      refine ⟨120485668174339684058393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1285180460526289963289525 120485668174339684058393)
                      ·
                        rfl

theorem cell23_234645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_234645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234645 prefixEnd_234645 := by exact prefixLift 234645
  have htrace : WordTrace (prefixWord ++ tailWord_234645) baseStart_234645 baseEnd_234645 := by
    simpa [prefixWord, tailWord_234645, baseEnd_234645] using wordTrace_append hprefix tailTrace_234645
  have hstable : (prefixWord ++ tailWord_234645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234645).length < 2 ^ (prefixWord ++ tailWord_234645).sum := by decide
  have hdescent : baseEnd_234645 < baseStart_234645 := by decide
  rcases family_descends (prefixWord ++ tailWord_234645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234652 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_234652 : Nat := 118140960795 + 234652 * 2 ^ 59
def prefixEnd_234652 : Nat := 4983230072969 + 3 ^ 40 * 234652 * 2
def baseEnd_234652 : Nat := 40163087512973718890287

theorem tailTrace_234652 : CollatzResearch.WordTrace tailWord_234652 prefixEnd_234652 40163087512973718890287 := by
  unfold tailWord_234652
  simp only [CollatzResearch.WordTrace]
  refine ⟨4279230772951677108073105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5705641030602236144097473 4279230772951677108073105)
  ·
    refine ⟨3209423079713757831054829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4279230772951677108073105 3209423079713757831054829)
    ·
      refine ⟨1203533654892659186645561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3209423079713757831054829 1203533654892659186645561)
      ·
        refine ⟨902650241169494389984171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1203533654892659186645561 902650241169494389984171)
        ·
          refine ⟨1353975361754241584976257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902650241169494389984171 1353975361754241584976257)
          ·
            refine ⟨1015481521315681188732193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353975361754241584976257 1015481521315681188732193)
            ·
              refine ⟨761611140986760891549145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015481521315681188732193 761611140986760891549145)
              ·
                refine ⟨571208355740070668661859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761611140986760891549145 571208355740070668661859)
                ·
                  refine ⟨856812533610106002992789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571208355740070668661859 856812533610106002992789)
                  ·
                    refine ⟨40163087512973718890287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 856812533610106002992789 40163087512973718890287)
                    ·
                      rfl

theorem cell23_234652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_234652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234652 prefixEnd_234652 := by exact prefixLift 234652
  have htrace : WordTrace (prefixWord ++ tailWord_234652) baseStart_234652 baseEnd_234652 := by
    simpa [prefixWord, tailWord_234652, baseEnd_234652] using wordTrace_append hprefix tailTrace_234652
  have hstable : (prefixWord ++ tailWord_234652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234652).length < 2 ^ (prefixWord ++ tailWord_234652).sum := by decide
  have hdescent : baseEnd_234652 < baseStart_234652 := by decide
  rcases family_descends (prefixWord ++ tailWord_234652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234689 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_234689 : Nat := 118140960795 + 234689 * 2 ^ 59
def prefixEnd_234689 : Nat := 4983230072969 + 3 ^ 40 * 234689 * 2
def baseEnd_234689 : Nat := 120508261323137511908191

theorem tailTrace_234689 : CollatzResearch.WordTrace tailWord_234689 prefixEnd_234689 120508261323137511908191 := by
  unfold tailWord_234689
  simp only [CollatzResearch.WordTrace]
  refine ⟨8559811046769309535243121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5706540697846206356828747 8559811046769309535243121)
  ·
    refine ⟨6419858285076982151432341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8559811046769309535243121 6419858285076982151432341)
    ·
      refine ⟨300930857112983538348391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6419858285076982151432341 300930857112983538348391)
      ·
        refine ⟨451396285669475307522587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300930857112983538348391 451396285669475307522587)
        ·
          refine ⟨677094428504212961283881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451396285669475307522587 677094428504212961283881)
          ·
            refine ⟨507820821378159720962911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677094428504212961283881 507820821378159720962911)
            ·
              refine ⟨761731232067239581444367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507820821378159720962911 761731232067239581444367)
              ·
                refine ⟨1142596848100859372166551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761731232067239581444367 1142596848100859372166551)
                ·
                  refine ⟨1713895272151289058249827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142596848100859372166551 1713895272151289058249827)
                  ·
                    refine ⟨2570842908226933587374741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1713895272151289058249827 2570842908226933587374741)
                    ·
                      refine ⟨120508261323137511908191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2570842908226933587374741 120508261323137511908191)
                      ·
                        rfl

theorem cell23_234689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_234689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234689 prefixEnd_234689 := by exact prefixLift 234689
  have htrace : WordTrace (prefixWord ++ tailWord_234689) baseStart_234689 baseEnd_234689 := by
    simpa [prefixWord, tailWord_234689, baseEnd_234689] using wordTrace_append hprefix tailTrace_234689
  have hstable : (prefixWord ++ tailWord_234689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234689).length < 2 ^ (prefixWord ++ tailWord_234689).sum := by decide
  have hdescent : baseEnd_234689 < baseStart_234689 := by decide
  rcases family_descends (prefixWord ++ tailWord_234689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234695 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 2, 7]
def baseStart_234695 : Nat := 118140960795 + 234695 * 2 ^ 59
def prefixEnd_234695 : Nat := 4983230072969 + 3 ^ 40 * 234695 * 2
def baseEnd_234695 : Nat := 40170447402354829477721

theorem tailTrace_234695 : CollatzResearch.WordTrace tailWord_234695 prefixEnd_234695 40170447402354829477721 := by
  unfold tailWord_234695
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560029884747572559961539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5706686589831715039974359 8560029884747572559961539)
  ·
    refine ⟨12840044827121358839942309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8560029884747572559961539 12840044827121358839942309)
    ·
      refine ⟨2407508405085254782489183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12840044827121358839942309 2407508405085254782489183)
      ·
        refine ⟨3611262607627882173733775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407508405085254782489183 3611262607627882173733775)
        ·
          refine ⟨5416893911441823260600663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611262607627882173733775 5416893911441823260600663)
          ·
            refine ⟨8125340867162734890900995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416893911441823260600663 8125340867162734890900995)
            ·
              refine ⟨12188011300744102336351493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8125340867162734890900995 12188011300744102336351493)
              ·
                refine ⟨2285252118889519188065905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12188011300744102336351493 2285252118889519188065905)
                ·
                  refine ⟨1713939089167139391049429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2285252118889519188065905 1713939089167139391049429)
                  ·
                    refine ⟨40170447402354829477721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1713939089167139391049429 40170447402354829477721)
                    ·
                      rfl

theorem cell23_234695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_234695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234695 prefixEnd_234695 := by exact prefixLift 234695
  have htrace : WordTrace (prefixWord ++ tailWord_234695) baseStart_234695 baseEnd_234695 := by
    simpa [prefixWord, tailWord_234695, baseEnd_234695] using wordTrace_append hprefix tailTrace_234695
  have hstable : (prefixWord ++ tailWord_234695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234695).length < 2 ^ (prefixWord ++ tailWord_234695).sum := by decide
  have hdescent : baseEnd_234695 < baseStart_234695 := by decide
  rcases family_descends (prefixWord ++ tailWord_234695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234727 : List Nat := [1, 1, 5, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_234727 : Nat := 118140960795 + 234727 * 2 ^ 59
def prefixEnd_234727 : Nat := 4983230072969 + 3 ^ 40 * 234727 * 2
def baseEnd_234727 : Nat := 120527773588008363233017

theorem tailTrace_234727 : CollatzResearch.WordTrace tailWord_234727 prefixEnd_234727 120527773588008363233017 := by
  unfold tailWord_234727
  simp only [CollatzResearch.WordTrace]
  refine ⟨8561197020631642025126435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5707464680421094683417623 8561197020631642025126435)
  ·
    refine ⟨12841795530947463037689653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8561197020631642025126435 12841795530947463037689653)
    ·
      refine ⟨1203918331026324659783405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12841795530947463037689653 1203918331026324659783405)
      ·
        refine ⟨451469374134871747418777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1203918331026324659783405 451469374134871747418777)
        ·
          refine ⟨338602030601153810564083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451469374134871747418777 338602030601153810564083)
          ·
            refine ⟨507903045901730715846125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338602030601153810564083 507903045901730715846125)
            ·
              refine ⟨190463642213149018442297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507903045901730715846125 190463642213149018442297)
              ·
                refine ⟨142847731659861763831723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190463642213149018442297 142847731659861763831723)
                ·
                  refine ⟨214271597489792645747585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142847731659861763831723 214271597489792645747585)
                  ·
                    refine ⟨160703698117344484310689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214271597489792645747585 160703698117344484310689)
                    ·
                      refine ⟨120527773588008363233017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160703698117344484310689 120527773588008363233017)
                      ·
                        rfl

theorem cell23_234727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_234727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234727 prefixEnd_234727 := by exact prefixLift 234727
  have htrace : WordTrace (prefixWord ++ tailWord_234727) baseStart_234727 baseEnd_234727 := by
    simpa [prefixWord, tailWord_234727, baseEnd_234727] using wordTrace_append hprefix tailTrace_234727
  have hstable : (prefixWord ++ tailWord_234727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234727).length < 2 ^ (prefixWord ++ tailWord_234727).sum := by decide
  have hdescent : baseEnd_234727 < baseStart_234727 := by decide
  rcases family_descends (prefixWord ++ tailWord_234727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234742 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_234742 : Nat := 118140960795 + 234742 * 2 ^ 59
def prefixEnd_234742 : Nat := 4983230072969 + 3 ^ 40 * 234742 * 2
def baseEnd_234742 : Nat := 40178491932608601515149

theorem tailTrace_234742 : CollatzResearch.WordTrace tailWord_234742 prefixEnd_234742 40178491932608601515149 := by
  unfold tailWord_234742
  simp only [CollatzResearch.WordTrace]
  refine ⟨535109007223581224182655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5707829410384866391281653 535109007223581224182655)
  ·
    refine ⟨802663510835371836273983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 535109007223581224182655 802663510835371836273983)
    ·
      refine ⟨1203995266253057754410975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802663510835371836273983 1203995266253057754410975)
      ·
        refine ⟨1805992899379586631616463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203995266253057754410975 1805992899379586631616463)
        ·
          refine ⟨2708989349069379947424695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805992899379586631616463 2708989349069379947424695)
          ·
            refine ⟨4063484023604069921137043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708989349069379947424695 4063484023604069921137043)
            ·
              refine ⟨6095226035406104881705565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063484023604069921137043 6095226035406104881705565)
              ·
                refine ⟨2285709763277289330639587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6095226035406104881705565 2285709763277289330639587)
                ·
                  refine ⟨3428564644915933995959381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285709763277289330639587 3428564644915933995959381)
                  ·
                    refine ⟨40178491932608601515149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3428564644915933995959381 40178491932608601515149)
                    ·
                      rfl

theorem cell23_234742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_234742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234742 prefixEnd_234742 := by exact prefixLift 234742
  have htrace : WordTrace (prefixWord ++ tailWord_234742) baseStart_234742 baseEnd_234742 := by
    simpa [prefixWord, tailWord_234742, baseEnd_234742] using wordTrace_append hprefix tailTrace_234742
  have hstable : (prefixWord ++ tailWord_234742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234742).length < 2 ^ (prefixWord ++ tailWord_234742).sum := by decide
  have hdescent : baseEnd_234742 < baseStart_234742 := by decide
  rcases family_descends (prefixWord ++ tailWord_234742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234753 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_234753 : Nat := 118140960795 + 234753 * 2 ^ 59
def prefixEnd_234753 : Nat := 4983230072969 + 3 ^ 40 * 234753 * 2
def baseEnd_234753 : Nat := 120541124085025261507897

theorem tailTrace_234753 : CollatzResearch.WordTrace tailWord_234753 prefixEnd_234753 120541124085025261507897 := by
  unfold tailWord_234753
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562145318537448465572913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5708096879024965643715275 8562145318537448465572913)
  ·
    refine ⟨6421608988903086349179685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8562145318537448465572913 6421608988903086349179685)
    ·
      refine ⟨1204051685419328690471191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6421608988903086349179685 1204051685419328690471191)
      ·
        refine ⟨1806077528128993035706787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204051685419328690471191 1806077528128993035706787)
        ·
          refine ⟨2709116292193489553560181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806077528128993035706787 2709116292193489553560181)
          ·
            refine ⟨253979652393139645646267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2709116292193489553560181 253979652393139645646267)
            ·
              refine ⟨380969478589709468469401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253979652393139645646267 380969478589709468469401)
              ·
                refine ⟨285727108942282101352051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380969478589709468469401 285727108942282101352051)
                ·
                  refine ⟨428590663413423152028077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285727108942282101352051 428590663413423152028077)
                  ·
                    refine ⟨160721498780033682010529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 428590663413423152028077 160721498780033682010529)
                    ·
                      refine ⟨120541124085025261507897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160721498780033682010529 120541124085025261507897)
                      ·
                        rfl

theorem cell23_234753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_234753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234753 prefixEnd_234753 := by exact prefixLift 234753
  have htrace : WordTrace (prefixWord ++ tailWord_234753) baseStart_234753 baseEnd_234753 := by
    simpa [prefixWord, tailWord_234753, baseEnd_234753] using wordTrace_append hprefix tailTrace_234753
  have hstable : (prefixWord ++ tailWord_234753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234753).length < 2 ^ (prefixWord ++ tailWord_234753).sum := by decide
  have hdescent : baseEnd_234753 < baseStart_234753 := by decide
  rcases family_descends (prefixWord ++ tailWord_234753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234762 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_234762 : Nat := 118140960795 + 234762 * 2 ^ 59
def prefixEnd_234762 : Nat := 4983230072969 + 3 ^ 40 * 234762 * 2
def baseEnd_234762 : Nat := 120545745410915726295355

theorem tailTrace_234762 : CollatzResearch.WordTrace tailWord_234762 prefixEnd_234762 120545745410915726295355 := by
  unfold tailWord_234762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2140618393876210750662635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5708315717003228668433693 2140618393876210750662635)
  ·
    refine ⟨3210927590814316125993953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2140618393876210750662635 3210927590814316125993953)
    ·
      refine ⟨2408195693110737094495465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3210927590814316125993953 2408195693110737094495465)
      ·
        refine ⟨1806146769833052820871599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2408195693110737094495465 1806146769833052820871599)
        ·
          refine ⟨2709220154749579231307399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806146769833052820871599 2709220154749579231307399)
          ·
            refine ⟨4063830232124368846961099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709220154749579231307399 4063830232124368846961099)
            ·
              refine ⟨6095745348186553270441649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063830232124368846961099 6095745348186553270441649)
              ·
                refine ⟨4571809011139914952831237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6095745348186553270441649 4571809011139914952831237)
                ·
                  refine ⟨857214189588734053655857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4571809011139914952831237 857214189588734053655857)
                  ·
                    refine ⟨642910642191550540241893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 857214189588734053655857 642910642191550540241893)
                    ·
                      refine ⟨120545745410915726295355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 642910642191550540241893 120545745410915726295355)
                      ·
                        rfl

theorem cell23_234762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_234762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234762 prefixEnd_234762 := by exact prefixLift 234762
  have htrace : WordTrace (prefixWord ++ tailWord_234762) baseStart_234762 baseEnd_234762 := by
    simpa [prefixWord, tailWord_234762, baseEnd_234762] using wordTrace_append hprefix tailTrace_234762
  have hstable : (prefixWord ++ tailWord_234762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234762).length < 2 ^ (prefixWord ++ tailWord_234762).sum := by decide
  have hdescent : baseEnd_234762 < baseStart_234762 := by decide
  rcases family_descends (prefixWord ++ tailWord_234762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234766 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2]
def baseStart_234766 : Nat := 118140960795 + 234766 * 2 ^ 59
def prefixEnd_234766 : Nat := 4983230072969 + 3 ^ 40 * 234766 * 2
def baseEnd_234766 : Nat := 120547799333533710645337

theorem tailTrace_234766 : CollatzResearch.WordTrace tailWord_234766 prefixEnd_234766 120547799333533710645337 := by
  unfold tailWord_234766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1070327433436293960724519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5708412978326901123864101 1070327433436293960724519)
  ·
    refine ⟨1605491150154440941086779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1070327433436293960724519 1605491150154440941086779)
    ·
      refine ⟨2408236725231661411630169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1605491150154440941086779 2408236725231661411630169)
      ·
        refine ⟨1806177543923746058722627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2408236725231661411630169 1806177543923746058722627)
        ·
          refine ⟨2709266315885619088083941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806177543923746058722627 2709266315885619088083941)
          ·
            refine ⟨507987434228553579015739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2709266315885619088083941 507987434228553579015739)
            ·
              refine ⟨761981151342830368523609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507987434228553579015739 761981151342830368523609)
              ·
                refine ⟨571485863507122776392707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761981151342830368523609 571485863507122776392707)
                ·
                  refine ⟨857228795260684164589061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571485863507122776392707 857228795260684164589061)
                  ·
                    refine ⟨160730399111378280860449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 857228795260684164589061 160730399111378280860449)
                    ·
                      refine ⟨120547799333533710645337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160730399111378280860449 120547799333533710645337)
                      ·
                        rfl

theorem cell23_234766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_234766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234766 prefixEnd_234766 := by exact prefixLift 234766
  have htrace : WordTrace (prefixWord ++ tailWord_234766) baseStart_234766 baseEnd_234766 := by
    simpa [prefixWord, tailWord_234766, baseEnd_234766] using wordTrace_append hprefix tailTrace_234766
  have hstable : (prefixWord ++ tailWord_234766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234766).length < 2 ^ (prefixWord ++ tailWord_234766).sum := by decide
  have hdescent : baseEnd_234766 < baseStart_234766 := by decide
  rcases family_descends (prefixWord ++ tailWord_234766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234842 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_234842 : Nat := 118140960795 + 234842 * 2 ^ 59
def prefixEnd_234842 : Nat := 4983230072969 + 3 ^ 40 * 234842 * 2
def baseEnd_234842 : Nat := 120586823863275413294987

theorem tailTrace_234842 : CollatzResearch.WordTrace tailWord_234842 prefixEnd_234842 120586823863275413294987 := by
  unfold tailWord_234842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2141347853803754166390695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5710260943476677777041853 2141347853803754166390695)
  ·
    refine ⟨3212021780705631249586043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2141347853803754166390695 3212021780705631249586043)
    ·
      refine ⟨4818032671058446874379065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3212021780705631249586043 4818032671058446874379065)
      ·
        refine ⟨3613524503293835155784299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4818032671058446874379065 3613524503293835155784299)
        ·
          refine ⟨5420286754940752733676449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613524503293835155784299 5420286754940752733676449)
          ·
            refine ⟨4065215066205564550257337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5420286754940752733676449 4065215066205564550257337)
            ·
              refine ⟨3048911299654173412693003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4065215066205564550257337 3048911299654173412693003)
              ·
                refine ⟨4573366949481260119039505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048911299654173412693003 4573366949481260119039505)
                ·
                  refine ⟨3430025212110945089279629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4573366949481260119039505 3430025212110945089279629)
                  ·
                    refine ⟨1286259454541604408479861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3430025212110945089279629 1286259454541604408479861)
                    ·
                      refine ⟨120586823863275413294987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1286259454541604408479861 120586823863275413294987)
                      ·
                        rfl

theorem cell23_234842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_234842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234842 prefixEnd_234842 := by exact prefixLift 234842
  have htrace : WordTrace (prefixWord ++ tailWord_234842) baseStart_234842 baseEnd_234842 := by
    simpa [prefixWord, tailWord_234842, baseEnd_234842] using wordTrace_append hprefix tailTrace_234842
  have hstable : (prefixWord ++ tailWord_234842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234842).length < 2 ^ (prefixWord ++ tailWord_234842).sum := by decide
  have hdescent : baseEnd_234842 < baseStart_234842 := by decide
  rcases family_descends (prefixWord ++ tailWord_234842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234883 : List Nat := [1, 1, 1, 3, 5, 1, 3, 3, 1, 4]
def baseStart_234883 : Nat := 118140960795 + 234883 * 2 ^ 59
def prefixEnd_234883 : Nat := 4983230072969 + 3 ^ 40 * 234883 * 2
def baseEnd_234883 : Nat := 40202625523369917627433

theorem tailTrace_234883 : CollatzResearch.WordTrace tailWord_234883 prefixEnd_234883 40202625523369917627433 := by
  unfold tailWord_234883
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566886808066480667805303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5711257872044320445203535 8566886808066480667805303)
  ·
    refine ⟨12850330212099721001707955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8566886808066480667805303 12850330212099721001707955)
    ·
      refine ⟨19275495318149581502561933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12850330212099721001707955 19275495318149581502561933)
      ·
        refine ⟨7228310744306093063460725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19275495318149581502561933 7228310744306093063460725)
        ·
          refine ⟨677654132278696224699443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7228310744306093063460725 677654132278696224699443)
          ·
            refine ⟨1016481198418044337049165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677654132278696224699443 1016481198418044337049165)
            ·
              refine ⟨381180449406766626393437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1016481198418044337049165 381180449406766626393437)
              ·
                refine ⟨142942668527537484897539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381180449406766626393437 142942668527537484897539)
                ·
                  refine ⟨214414002791306227346309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142942668527537484897539 214414002791306227346309)
                  ·
                    refine ⟨40202625523369917627433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214414002791306227346309 40202625523369917627433)
                    ·
                      rfl

theorem cell23_234883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 1, 4].length) (baseStart_234883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234883 prefixEnd_234883 := by exact prefixLift 234883
  have htrace : WordTrace (prefixWord ++ tailWord_234883) baseStart_234883 baseEnd_234883 := by
    simpa [prefixWord, tailWord_234883, baseEnd_234883] using wordTrace_append hprefix tailTrace_234883
  have hstable : (prefixWord ++ tailWord_234883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234883).length < 2 ^ (prefixWord ++ tailWord_234883).sum := by decide
  have hdescent : baseEnd_234883 < baseStart_234883 := by decide
  rcases family_descends (prefixWord ++ tailWord_234883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234899 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 2, 9, 2]
def baseStart_234899 : Nat := 118140960795 + 234899 * 2 ^ 59
def prefixEnd_234899 : Nat := 4983230072969 + 3 ^ 40 * 234899 * 2
def baseEnd_234899 : Nat := 120616092260581690282225

theorem tailTrace_234899 : CollatzResearch.WordTrace tailWord_234899 prefixEnd_234899 120616092260581690282225 := by
  unfold tailWord_234899
  simp only [CollatzResearch.WordTrace]
  refine ⟨8567470376008515400387751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5711646917339010266925167 8567470376008515400387751)
  ·
    refine ⟨12851205564012773100581627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8567470376008515400387751 12851205564012773100581627)
    ·
      refine ⟨19276808346019159650872441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12851205564012773100581627 19276808346019159650872441)
      ·
        refine ⟨14457606259514369738154331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19276808346019159650872441 14457606259514369738154331)
        ·
          refine ⟨21686409389271554607231497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14457606259514369738154331 21686409389271554607231497)
          ·
            refine ⟨16264807041953665955423623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21686409389271554607231497 16264807041953665955423623)
            ·
              refine ⟨24397210562930498933135435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16264807041953665955423623 24397210562930498933135435)
              ·
                refine ⟨36595815844395748399703153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24397210562930498933135435 36595815844395748399703153)
                ·
                  refine ⟨27446861883296811299777365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36595815844395748399703153 27446861883296811299777365)
                  ·
                    refine ⟨160821456347442253709633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27446861883296811299777365 160821456347442253709633)
                    ·
                      refine ⟨120616092260581690282225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160821456347442253709633 120616092260581690282225)
                      ·
                        rfl

theorem cell23_234899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 9, 2].length) (baseStart_234899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234899 prefixEnd_234899 := by exact prefixLift 234899
  have htrace : WordTrace (prefixWord ++ tailWord_234899) baseStart_234899 baseEnd_234899 := by
    simpa [prefixWord, tailWord_234899, baseEnd_234899] using wordTrace_append hprefix tailTrace_234899
  have hstable : (prefixWord ++ tailWord_234899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234899).length < 2 ^ (prefixWord ++ tailWord_234899).sum := by decide
  have hdescent : baseEnd_234899 < baseStart_234899 := by decide
  rcases family_descends (prefixWord ++ tailWord_234899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234916 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 6, 3, 2]
def baseStart_234916 : Nat := 118140960795 + 234916 * 2 ^ 59
def prefixEnd_234916 : Nat := 4983230072969 + 3 ^ 40 * 234916 * 2
def baseEnd_234916 : Nat := 120624821431708123769647

theorem tailTrace_234916 : CollatzResearch.WordTrace tailWord_234916 prefixEnd_234916 120624821431708123769647 := by
  unfold tailWord_234916
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284045208473463651878301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5712060277964618202504401 4284045208473463651878301)
  ·
    refine ⟨1606516953177548869454363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4284045208473463651878301 1606516953177548869454363)
    ·
      refine ⟨2409775429766323304181545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606516953177548869454363 2409775429766323304181545)
      ·
        refine ⟨1807331572324742478136159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2409775429766323304181545 1807331572324742478136159)
        ·
          refine ⟨2710997358487113717204239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807331572324742478136159 2710997358487113717204239)
          ·
            refine ⟨4066496037730670575806359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710997358487113717204239 4066496037730670575806359)
            ·
              refine ⟨6099744056596005863709539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066496037730670575806359 6099744056596005863709539)
              ·
                refine ⟨9149616084894008795564309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099744056596005863709539 9149616084894008795564309)
                ·
                  refine ⟨428888253979406662292077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9149616084894008795564309 428888253979406662292077)
                  ·
                    refine ⟨160833095242277498359529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 428888253979406662292077 160833095242277498359529)
                    ·
                      refine ⟨120624821431708123769647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160833095242277498359529 120624821431708123769647)
                      ·
                        rfl

theorem cell23_234916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_234916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234916 prefixEnd_234916 := by exact prefixLift 234916
  have htrace : WordTrace (prefixWord ++ tailWord_234916) baseStart_234916 baseEnd_234916 := by
    simpa [prefixWord, tailWord_234916, baseEnd_234916] using wordTrace_append hprefix tailTrace_234916
  have hstable : (prefixWord ++ tailWord_234916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234916).length < 2 ^ (prefixWord ++ tailWord_234916).sum := by decide
  have hdescent : baseEnd_234916 < baseStart_234916 := by decide
  rcases family_descends (prefixWord ++ tailWord_234916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234933 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_234933 : Nat := 118140960795 + 234933 * 2 ^ 59
def prefixEnd_234933 : Nat := 4983230072969 + 3 ^ 40 * 234933 * 2
def baseEnd_234933 : Nat := 120633550602834557257069

theorem tailTrace_234933 : CollatzResearch.WordTrace tailWord_234933 prefixEnd_234933 120633550602834557257069 := by
  unfold tailWord_234933
  simp only [CollatzResearch.WordTrace]
  refine ⟨8568710457885339207125453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5712473638590226138083635 8568710457885339207125453)
  ·
    refine ⟨3213266421707002202672045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8568710457885339207125453 3213266421707002202672045)
    ·
      refine ⟨1204974908140125826002017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3213266421707002202672045 1204974908140125826002017)
      ·
        refine ⟨903731181105094369501513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1204974908140125826002017 903731181105094369501513)
        ·
          refine ⟨677798385828820777126135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903731181105094369501513 677798385828820777126135)
          ·
            refine ⟨1016697578743231165689203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677798385828820777126135 1016697578743231165689203)
            ·
              refine ⟨1525046368114846748533805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016697578743231165689203 1525046368114846748533805)
              ·
                refine ⟨571892388043067530700177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1525046368114846748533805 571892388043067530700177)
                ·
                  refine ⟨428919291032300648025133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571892388043067530700177 428919291032300648025133)
                  ·
                    refine ⟨160844734137112743009425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 428919291032300648025133 160844734137112743009425)
                    ·
                      refine ⟨120633550602834557257069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160844734137112743009425 120633550602834557257069)
                      ·
                        rfl

theorem cell23_234933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_234933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234933 prefixEnd_234933 := by exact prefixLift 234933
  have htrace : WordTrace (prefixWord ++ tailWord_234933) baseStart_234933 baseEnd_234933 := by
    simpa [prefixWord, tailWord_234933, baseEnd_234933] using wordTrace_append hprefix tailTrace_234933
  have hstable : (prefixWord ++ tailWord_234933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234933).length < 2 ^ (prefixWord ++ tailWord_234933).sum := by decide
  have hdescent : baseEnd_234933 < baseStart_234933 := by decide
  rcases family_descends (prefixWord ++ tailWord_234933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234969 : List Nat := [1, 2, 1, 2, 4, 2, 3, 8]
def baseStart_234969 : Nat := 118140960795 + 234969 * 2 ^ 59
def prefixEnd_234969 : Nat := 4983230072969 + 3 ^ 40 * 234969 * 2
def baseEnd_234969 : Nat := 4468593922459126533589

theorem tailTrace_234969 : CollatzResearch.WordTrace tailWord_234969 prefixEnd_234969 4468593922459126533589 := by
  unfold tailWord_234969
  simp only [CollatzResearch.WordTrace]
  refine ⟨8570023485754917355435961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5713348990503278236957307 8570023485754917355435961)
  ·
    refine ⟨6427517614316188016576971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8570023485754917355435961 6427517614316188016576971)
    ·
      refine ⟨9641276421474282024865457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6427517614316188016576971 9641276421474282024865457)
      ·
        refine ⟨7230957316105711518649093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9641276421474282024865457 7230957316105711518649093)
        ·
          refine ⟨1355804496769820909746705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7230957316105711518649093 1355804496769820909746705)
          ·
            refine ⟨1016853372577365682310029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355804496769820909746705 1016853372577365682310029)
            ·
              refine ⟨381320014716512130866261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1016853372577365682310029 381320014716512130866261)
              ·
                refine ⟨4468593922459126533589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 381320014716512130866261 4468593922459126533589)
                ·
                  rfl

theorem cell23_234969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 8].length) (baseStart_234969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234969 prefixEnd_234969 := by exact prefixLift 234969
  have htrace : WordTrace (prefixWord ++ tailWord_234969) baseStart_234969 baseEnd_234969 := by
    simpa [prefixWord, tailWord_234969, baseEnd_234969] using wordTrace_append hprefix tailTrace_234969
  have hstable : (prefixWord ++ tailWord_234969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234969).length < 2 ^ (prefixWord ++ tailWord_234969).sum := by decide
  have hdescent : baseEnd_234969 < baseStart_234969 := by decide
  rcases family_descends (prefixWord ++ tailWord_234969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234973 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_234973 : Nat := 118140960795 + 234973 * 2 ^ 59
def prefixEnd_234973 : Nat := 4983230072969 + 3 ^ 40 * 234973 * 2
def baseEnd_234973 : Nat := 40218029943004800252295

theorem tailTrace_234973 : CollatzResearch.WordTrace tailWord_234973 prefixEnd_234973 40218029943004800252295 := by
  unfold tailWord_234973
  simp only [CollatzResearch.WordTrace]
  refine ⟨8570169377740426038581573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5713446251826950692387715 8570169377740426038581573)
  ·
    refine ⟨1606906758326329882234045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8570169377740426038581573 1606906758326329882234045)
    ·
      refine ⟨602590034372373705837767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1606906758326329882234045 602590034372373705837767)
      ·
        refine ⟨903885051558560558756651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602590034372373705837767 903885051558560558756651)
        ·
          refine ⟨1355827577337840838134977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903885051558560558756651 1355827577337840838134977)
          ·
            refine ⟨1016870683003380628601233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355827577337840838134977 1016870683003380628601233)
            ·
              refine ⟨762653012252535471450925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016870683003380628601233 762653012252535471450925)
              ·
                refine ⟨285994879594700801794097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 762653012252535471450925 285994879594700801794097)
                ·
                  refine ⟨214496159696025601345573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285994879594700801794097 214496159696025601345573)
                  ·
                    refine ⟨40218029943004800252295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214496159696025601345573 40218029943004800252295)
                    ·
                      rfl

theorem cell23_234973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_234973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234973 prefixEnd_234973 := by exact prefixLift 234973
  have htrace : WordTrace (prefixWord ++ tailWord_234973) baseStart_234973 baseEnd_234973 := by
    simpa [prefixWord, tailWord_234973, baseEnd_234973] using wordTrace_append hprefix tailTrace_234973
  have hstable : (prefixWord ++ tailWord_234973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234973).length < 2 ^ (prefixWord ++ tailWord_234973).sum := by decide
  have hdescent : baseEnd_234973 < baseStart_234973 := by decide
  rcases family_descends (prefixWord ++ tailWord_234973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234997 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_234997 : Nat := 118140960795 + 234997 * 2 ^ 59
def prefixEnd_234997 : Nat := 4983230072969 + 3 ^ 40 * 234997 * 2
def baseEnd_234997 : Nat := 120666413364722306856775

theorem tailTrace_234997 : CollatzResearch.WordTrace tailWord_234997 prefixEnd_234997 120666413364722306856775 := by
  unfold tailWord_234997
  simp only [CollatzResearch.WordTrace]
  refine ⟨8571044729653478137455245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5714029819768985424970163 8571044729653478137455245)
  ·
    refine ⟨3214141773620054301545717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8571044729653478137455245 3214141773620054301545717)
    ·
      refine ⟨301325791276880090769911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3214141773620054301545717 301325791276880090769911)
      ·
        refine ⟨451988686915320136154867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301325791276880090769911 451988686915320136154867)
        ·
          refine ⟨677983030372980204232301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451988686915320136154867 677983030372980204232301)
          ·
            refine ⟨254243636389867576587113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 677983030372980204232301 254243636389867576587113)
            ·
              refine ⟨190682727292400682440335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254243636389867576587113 190682727292400682440335)
              ·
                refine ⟨286024090938601023660503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190682727292400682440335 286024090938601023660503)
                ·
                  refine ⟨429036136407901535490755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286024090938601023660503 429036136407901535490755)
                  ·
                    refine ⟨643554204611852303236133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 429036136407901535490755 643554204611852303236133)
                    ·
                      refine ⟨120666413364722306856775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 643554204611852303236133 120666413364722306856775)
                      ·
                        rfl

theorem cell23_234997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_234997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_234997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_234997 prefixEnd_234997 := by exact prefixLift 234997
  have htrace : WordTrace (prefixWord ++ tailWord_234997) baseStart_234997 baseEnd_234997 := by
    simpa [prefixWord, tailWord_234997, baseEnd_234997] using wordTrace_append hprefix tailTrace_234997
  have hstable : (prefixWord ++ tailWord_234997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234997).length < 2 ^ (prefixWord ++ tailWord_234997).sum := by decide
  have hdescent : baseEnd_234997 < baseStart_234997 := by decide
  rcases family_descends (prefixWord ++ tailWord_234997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235000 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 1, 2, 3]
def baseStart_235000 : Nat := 118140960795 + 235000 * 2 ^ 59
def prefixEnd_235000 : Nat := 4983230072969 + 3 ^ 40 * 235000 * 2
def baseEnd_235000 : Nat := 120667953806685795119261

theorem tailTrace_235000 : CollatzResearch.WordTrace tailWord_235000 prefixEnd_235000 120667953806685795119261 := by
  unfold tailWord_235000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285577074321304824907227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5714102765761739766542969 4285577074321304824907227)
  ·
    refine ⟨6428365611481957237360841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4285577074321304824907227 6428365611481957237360841)
    ·
      refine ⟨4821274208611467928020631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6428365611481957237360841 4821274208611467928020631)
      ·
        refine ⟨7231911312917201892030947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821274208611467928020631 7231911312917201892030947)
        ·
          refine ⟨10847866969375802838046421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7231911312917201892030947 10847866969375802838046421)
          ·
            refine ⟨254246882094745379016713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10847866969375802838046421 254246882094745379016713)
            ·
              refine ⟨190685161571059034262535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254246882094745379016713 190685161571059034262535)
              ·
                refine ⟨286027742356588551393803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190685161571059034262535 286027742356588551393803)
                ·
                  refine ⟨429041613534882827090705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286027742356588551393803 429041613534882827090705)
                  ·
                    refine ⟨321781210151162120318029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 429041613534882827090705 321781210151162120318029)
                    ·
                      refine ⟨120667953806685795119261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 321781210151162120318029 120667953806685795119261)
                      ·
                        rfl

theorem cell23_235000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_235000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235000 prefixEnd_235000 := by exact prefixLift 235000
  have htrace : WordTrace (prefixWord ++ tailWord_235000) baseStart_235000 baseEnd_235000 := by
    simpa [prefixWord, tailWord_235000, baseEnd_235000] using wordTrace_append hprefix tailTrace_235000
  have hstable : (prefixWord ++ tailWord_235000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235000).length < 2 ^ (prefixWord ++ tailWord_235000).sum := by decide
  have hdescent : baseEnd_235000 < baseStart_235000 := by decide
  rcases family_descends (prefixWord ++ tailWord_235000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235040 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 1, 3, 2]
def baseStart_235040 : Nat := 118140960795 + 235040 * 2 ^ 59
def prefixEnd_235040 : Nat := 4983230072969 + 3 ^ 40 * 235040 * 2
def baseEnd_235040 : Nat := 120688493032865638619077

theorem tailTrace_235040 : CollatzResearch.WordTrace tailWord_235040 prefixEnd_235040 120688493032865638619077 := by
  unfold tailWord_235040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4286306534248848240635287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5715075378998464320847049 4286306534248848240635287)
  ·
    refine ⟨6429459801373272360952931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4286306534248848240635287 6429459801373272360952931)
    ·
      refine ⟨9644189702059908541429397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429459801373272360952931 9644189702059908541429397)
      ·
        refine ⟨452071392284058212879503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9644189702059908541429397 452071392284058212879503)
        ·
          refine ⟨678107088426087319319255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452071392284058212879503 678107088426087319319255)
          ·
            refine ⟨1017160632639130978978883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678107088426087319319255 1017160632639130978978883)
            ·
              refine ⟨1525740948958696468468325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017160632639130978978883 1525740948958696468468325)
              ·
                refine ⟨286076427929755587837811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1525740948958696468468325 286076427929755587837811)
                ·
                  refine ⟨429114641894633381756717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286076427929755587837811 429114641894633381756717)
                  ·
                    refine ⟨160917990710487518158769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 429114641894633381756717 160917990710487518158769)
                    ·
                      refine ⟨120688493032865638619077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160917990710487518158769 120688493032865638619077)
                      ·
                        rfl

theorem cell23_235040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_235040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235040 prefixEnd_235040 := by exact prefixLift 235040
  have htrace : WordTrace (prefixWord ++ tailWord_235040) baseStart_235040 baseEnd_235040 := by
    simpa [prefixWord, tailWord_235040, baseEnd_235040] using wordTrace_append hprefix tailTrace_235040
  have hstable : (prefixWord ++ tailWord_235040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235040).length < 2 ^ (prefixWord ++ tailWord_235040).sum := by decide
  have hdescent : baseEnd_235040 < baseStart_235040 := by decide
  rcases family_descends (prefixWord ++ tailWord_235040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235086 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_235086 : Nat := 118140960795 + 235086 * 2 ^ 59
def prefixEnd_235086 : Nat := 4983230072969 + 3 ^ 40 * 235086 * 2
def baseEnd_235086 : Nat := 120712113142972458643865

theorem tailTrace_235086 : CollatzResearch.WordTrace tailWord_235086 prefixEnd_235086 120712113142972458643865 := by
  unfold tailWord_235086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071786353291380792180639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5716193884220697558296741 1071786353291380792180639)
  ·
    refine ⟨1607679529937071188270959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1071786353291380792180639 1607679529937071188270959)
    ·
      refine ⟨2411519294905606782406439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1607679529937071188270959 2411519294905606782406439)
      ·
        refine ⟨3617278942358410173609659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2411519294905606782406439 3617278942358410173609659)
        ·
          refine ⟨5425918413537615260414489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617278942358410173609659 5425918413537615260414489)
          ·
            refine ⟨4069438810153211445310867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5425918413537615260414489 4069438810153211445310867)
            ·
              refine ⟨6104158215229817167966301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4069438810153211445310867 6104158215229817167966301)
              ·
                refine ⟨2289059330711181437987363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6104158215229817167966301 2289059330711181437987363)
                ·
                  refine ⟨3433588996066772156981045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289059330711181437987363 3433588996066772156981045)
                  ·
                    refine ⟨321898968381259889716973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3433588996066772156981045 321898968381259889716973)
                    ·
                      refine ⟨120712113142972458643865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 321898968381259889716973 120712113142972458643865)
                      ·
                        rfl

theorem cell23_235086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_235086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235086 prefixEnd_235086 := by exact prefixLift 235086
  have htrace : WordTrace (prefixWord ++ tailWord_235086) baseStart_235086 baseEnd_235086 := by
    simpa [prefixWord, tailWord_235086, baseEnd_235086] using wordTrace_append hprefix tailTrace_235086
  have hstable : (prefixWord ++ tailWord_235086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235086).length < 2 ^ (prefixWord ++ tailWord_235086).sum := by decide
  have hdescent : baseEnd_235086 < baseStart_235086 := by decide
  rcases family_descends (prefixWord ++ tailWord_235086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235143 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 1, 6, 2]
def baseStart_235143 : Nat := 118140960795 + 235143 * 2 ^ 59
def prefixEnd_235143 : Nat := 4983230072969 + 3 ^ 40 * 235143 * 2
def baseEnd_235143 : Nat := 120741381540278735631103

theorem tailTrace_235143 : CollatzResearch.WordTrace tailWord_235143 prefixEnd_235143 120741381540278735631103 := by
  unfold tailWord_235143
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576369787124545072270083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5717579858083030048180055 8576369787124545072270083)
  ·
    refine ⟨12864554680686817608405125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8576369787124545072270083 12864554680686817608405125)
    ·
      refine ⟨2412104002628778301575961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12864554680686817608405125 2412104002628778301575961)
      ·
        refine ⟨1809078001971583726181971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2412104002628778301575961 1809078001971583726181971)
        ·
          refine ⟨2713617002957375589272957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809078001971583726181971 2713617002957375589272957)
          ·
            refine ⟨1017606376109015845977359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2713617002957375589272957 1017606376109015845977359)
            ·
              refine ⟨1526409564163523768966039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017606376109015845977359 1526409564163523768966039)
              ·
                refine ⟨2289614346245285653449059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526409564163523768966039 2289614346245285653449059)
                ·
                  refine ⟨3434421519367928480173589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289614346245285653449059 3434421519367928480173589)
                  ·
                    refine ⟨160988508720371647508137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3434421519367928480173589 160988508720371647508137)
                    ·
                      refine ⟨120741381540278735631103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 160988508720371647508137 120741381540278735631103)
                      ·
                        rfl

theorem cell23_235143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_235143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235143 prefixEnd_235143 := by exact prefixLift 235143
  have htrace : WordTrace (prefixWord ++ tailWord_235143) baseStart_235143 baseEnd_235143 := by
    simpa [prefixWord, tailWord_235143, baseEnd_235143] using wordTrace_append hprefix tailTrace_235143
  have hstable : (prefixWord ++ tailWord_235143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235143).length < 2 ^ (prefixWord ++ tailWord_235143).sum := by decide
  have hdescent : baseEnd_235143 < baseStart_235143 := by decide
  rcases family_descends (prefixWord ++ tailWord_235143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235160 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 2, 1, 4]
def baseStart_235160 : Nat := 118140960795 + 235160 * 2 ^ 59
def prefixEnd_235160 : Nat := 4983230072969 + 3 ^ 40 * 235160 * 2
def baseEnd_235160 : Nat := 120750110711405169118525

theorem tailTrace_235160 : CollatzResearch.WordTrace tailWord_235160 prefixEnd_235160 120750110711405169118525 := by
  unfold tailWord_235160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4288494914031478487819467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5717993218708637983759289 4288494914031478487819467)
  ·
    refine ⟨6432742371047217731729201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4288494914031478487819467 6432742371047217731729201)
    ·
      refine ⟨4824556778285413298796901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6432742371047217731729201 4824556778285413298796901)
      ·
        refine ⟨904604395928514993524419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4824556778285413298796901 904604395928514993524419)
        ·
          refine ⟨1356906593892772490286629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904604395928514993524419 1356906593892772490286629)
          ·
            refine ⟨254419986354894841928743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1356906593892772490286629 254419986354894841928743)
            ·
              refine ⟨381629979532342262893115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254419986354894841928743 381629979532342262893115)
              ·
                refine ⟨572444969298513394339673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381629979532342262893115 572444969298513394339673)
                ·
                  refine ⟨429333726973885045754755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572444969298513394339673 429333726973885045754755)
                  ·
                    refine ⟨644000590460827568632133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 429333726973885045754755 644000590460827568632133)
                    ·
                      refine ⟨120750110711405169118525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 644000590460827568632133 120750110711405169118525)
                      ·
                        rfl

theorem cell23_235160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_235160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235160 prefixEnd_235160 := by exact prefixLift 235160
  have htrace : WordTrace (prefixWord ++ tailWord_235160) baseStart_235160 baseEnd_235160 := by
    simpa [prefixWord, tailWord_235160, baseEnd_235160] using wordTrace_append hprefix tailTrace_235160
  have hstable : (prefixWord ++ tailWord_235160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235160).length < 2 ^ (prefixWord ++ tailWord_235160).sum := by decide
  have hdescent : baseEnd_235160 < baseStart_235160 := by decide
  rcases family_descends (prefixWord ++ tailWord_235160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235186 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_235186 : Nat := 118140960795 + 235186 * 2 ^ 59
def prefixEnd_235186 : Nat := 4983230072969 + 3 ^ 40 * 235186 * 2
def baseEnd_235186 : Nat := 120763461208422067393405

theorem tailTrace_235186 : CollatzResearch.WordTrace tailWord_235186 prefixEnd_235186 120763461208422067393405 := by
  unfold tailWord_235186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144484531492190854021353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5718625417312508944056941 2144484531492190854021353)
  ·
    refine ⟨1608363398619143140516015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2144484531492190854021353 1608363398619143140516015)
    ·
      refine ⟨2412545097928714710774023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1608363398619143140516015 2412545097928714710774023)
      ·
        refine ⟨3618817646893072066161035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2412545097928714710774023 3618817646893072066161035)
        ·
          refine ⟨5428226470339608099241553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3618817646893072066161035 5428226470339608099241553)
          ·
            refine ⟨4071169852754706074431165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5428226470339608099241553 4071169852754706074431165)
            ·
              refine ⟨1526688694783014777911687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4071169852754706074431165 1526688694783014777911687)
              ·
                refine ⟨2290033042174522166867531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526688694783014777911687 2290033042174522166867531)
                ·
                  refine ⟨3435049563261783250301297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290033042174522166867531 3435049563261783250301297)
                  ·
                    refine ⟨2576287172446337437725973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3435049563261783250301297 2576287172446337437725973)
                    ·
                      refine ⟨120763461208422067393405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2576287172446337437725973 120763461208422067393405)
                      ·
                        rfl

theorem cell23_235186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_235186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235186 prefixEnd_235186 := by exact prefixLift 235186
  have htrace : WordTrace (prefixWord ++ tailWord_235186) baseStart_235186 baseEnd_235186 := by
    simpa [prefixWord, tailWord_235186, baseEnd_235186] using wordTrace_append hprefix tailTrace_235186
  have hstable : (prefixWord ++ tailWord_235186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235186).length < 2 ^ (prefixWord ++ tailWord_235186).sum := by decide
  have hdescent : baseEnd_235186 < baseStart_235186 := by decide
  rcases family_descends (prefixWord ++ tailWord_235186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235243 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 4, 4]
def baseStart_235243 : Nat := 118140960795 + 235243 * 2 ^ 59
def prefixEnd_235243 : Nat := 4983230072969 + 3 ^ 40 * 235243 * 2
def baseEnd_235243 : Nat := 40264243201909448126881

theorem tailTrace_235243 : CollatzResearch.WordTrace tailWord_235243 prefixEnd_235243 40264243201909448126881 := by
  unfold tailWord_235243
  simp only [CollatzResearch.WordTrace]
  refine ⟨8580017086762262150910383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5720011391174841433940255 8580017086762262150910383)
  ·
    refine ⟨12870025630143393226365575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8580017086762262150910383 12870025630143393226365575)
    ·
      refine ⟨19305038445215089839548363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12870025630143393226365575 19305038445215089839548363)
      ·
        refine ⟨28957557667822634759322545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19305038445215089839548363 28957557667822634759322545)
        ·
          refine ⟨21718168250866976069491909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28957557667822634759322545 21718168250866976069491909)
          ·
            refine ⟨4072156547037558013029733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21718168250866976069491909 4072156547037558013029733)
            ·
              refine ⟨763529352569542127443075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4072156547037558013029733 763529352569542127443075)
              ·
                refine ⟨1145294028854313191164613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763529352569542127443075 1145294028854313191164613)
                ·
                  refine ⟨214742630410183723343365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145294028854313191164613 214742630410183723343365)
                  ·
                    refine ⟨40264243201909448126881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214742630410183723343365 40264243201909448126881)
                    ·
                      rfl

theorem cell23_235243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 4].length) (baseStart_235243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235243 prefixEnd_235243 := by exact prefixLift 235243
  have htrace : WordTrace (prefixWord ++ tailWord_235243) baseStart_235243 baseEnd_235243 := by
    simpa [prefixWord, tailWord_235243, baseEnd_235243] using wordTrace_append hprefix tailTrace_235243
  have hstable : (prefixWord ++ tailWord_235243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235243).length < 2 ^ (prefixWord ++ tailWord_235243).sum := by decide
  have hdescent : baseEnd_235243 < baseStart_235243 := by decide
  rcases family_descends (prefixWord ++ tailWord_235243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235260 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_235260 : Nat := 118140960795 + 235260 * 2 ^ 59
def prefixEnd_235260 : Nat := 4983230072969 + 3 ^ 40 * 235260 * 2
def baseEnd_235260 : Nat := 40267152925618259289355

theorem tailTrace_235260 : CollatzResearch.WordTrace tailWord_235260 prefixEnd_235260 40267152925618259289355 := by
  unfold tailWord_235260
  simp only [CollatzResearch.WordTrace]
  refine ⟨4290318563850337027139617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5720424751800449369519489 4290318563850337027139617)
  ·
    refine ⟨3217738922887752770354713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4290318563850337027139617 3217738922887752770354713)
    ·
      refine ⟨2413304192165814577766035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3217738922887752770354713 2413304192165814577766035)
      ·
        refine ⟨3619956288248721866649053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2413304192165814577766035 3619956288248721866649053)
        ·
          refine ⟨1357483608093270699993395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3619956288248721866649053 1357483608093270699993395)
          ·
            refine ⟨2036225412139906049990093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357483608093270699993395 2036225412139906049990093)
            ·
              refine ⟨763584529552464768746285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2036225412139906049990093 763584529552464768746285)
              ·
                refine ⟨286344198582174288279857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 763584529552464768746285 286344198582174288279857)
                ·
                  refine ⟨214758148936630716209893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286344198582174288279857 214758148936630716209893)
                  ·
                    refine ⟨40267152925618259289355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214758148936630716209893 40267152925618259289355)
                    ·
                      rfl

theorem cell23_235260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_235260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235260 prefixEnd_235260 := by exact prefixLift 235260
  have htrace : WordTrace (prefixWord ++ tailWord_235260) baseStart_235260 baseEnd_235260 := by
    simpa [prefixWord, tailWord_235260, baseEnd_235260] using wordTrace_append hprefix tailTrace_235260
  have hstable : (prefixWord ++ tailWord_235260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235260).length < 2 ^ (prefixWord ++ tailWord_235260).sum := by decide
  have hdescent : baseEnd_235260 < baseStart_235260 := by decide
  rcases family_descends (prefixWord ++ tailWord_235260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235301 : List Nat := [1, 3, 1, 2, 3, 2, 4, 2, 1, 2, 2]
def baseStart_235301 : Nat := 118140960795 + 235301 * 2 ^ 59
def prefixEnd_235301 : Nat := 4983230072969 + 3 ^ 40 * 235301 * 2
def baseEnd_235301 : Nat := 120822511483689117455377

theorem tailTrace_235301 : CollatzResearch.WordTrace tailWord_235301 prefixEnd_235301 120822511483689117455377 := by
  unfold tailWord_235301
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582132520552138056521757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5721421680368092037681171 8582132520552138056521757)
  ·
    refine ⟨3218299695207051771195659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8582132520552138056521757 3218299695207051771195659)
    ·
      refine ⟨4827449542810577656793489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3218299695207051771195659 4827449542810577656793489)
      ·
        refine ⟨3620587157107933242595117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4827449542810577656793489 3620587157107933242595117)
        ·
          refine ⟨1357720183915474965973169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3620587157107933242595117 1357720183915474965973169)
          ·
            refine ⟨1018290137936606224479877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1357720183915474965973169 1018290137936606224479877)
            ·
              refine ⟨190929400863113667089977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1018290137936606224479877 190929400863113667089977)
              ·
                refine ⟨143197050647335250317483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190929400863113667089977 143197050647335250317483)
                ·
                  refine ⟨214795575971002875476225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143197050647335250317483 214795575971002875476225)
                  ·
                    refine ⟨161096681978252156607169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214795575971002875476225 161096681978252156607169)
                    ·
                      refine ⟨120822511483689117455377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161096681978252156607169 120822511483689117455377)
                      ·
                        rfl

theorem cell23_235301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_235301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235301 prefixEnd_235301 := by exact prefixLift 235301
  have htrace : WordTrace (prefixWord ++ tailWord_235301) baseStart_235301 baseEnd_235301 := by
    simpa [prefixWord, tailWord_235301, baseEnd_235301] using wordTrace_append hprefix tailTrace_235301
  have hstable : (prefixWord ++ tailWord_235301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235301).length < 2 ^ (prefixWord ++ tailWord_235301).sum := by decide
  have hdescent : baseEnd_235301 < baseStart_235301 := by decide
  rcases family_descends (prefixWord ++ tailWord_235301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235317 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_235317 : Nat := 118140960795 + 235317 * 2 ^ 59
def prefixEnd_235317 : Nat := 4983230072969 + 3 ^ 40 * 235317 * 2
def baseEnd_235317 : Nat := 120830727174161054855303

theorem tailTrace_235317 : CollatzResearch.WordTrace tailWord_235317 prefixEnd_235317 120830727174161054855303 := by
  unfold tailWord_235317
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582716088494172789104205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5721810725662781859402803 8582716088494172789104205)
  ·
    refine ⟨3218518533185314795914077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8582716088494172789104205 3218518533185314795914077)
    ·
      refine ⟨1206944449944493048467779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3218518533185314795914077 1206944449944493048467779)
      ·
        refine ⟨1810416674916739572701669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206944449944493048467779 1810416674916739572701669)
        ·
          refine ⟨339453126546888669881563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1810416674916739572701669 339453126546888669881563)
          ·
            refine ⟨509179689820333004822345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339453126546888669881563 509179689820333004822345)
            ·
              refine ⟨381884767365249753616759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509179689820333004822345 381884767365249753616759)
              ·
                refine ⟨572827151047874630425139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381884767365249753616759 572827151047874630425139)
                ·
                  refine ⟨859240726571811945637709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572827151047874630425139 859240726571811945637709)
                  ·
                    refine ⟨322215272464429479614141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 859240726571811945637709 322215272464429479614141)
                    ·
                      refine ⟨120830727174161054855303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 322215272464429479614141 120830727174161054855303)
                      ·
                        rfl

theorem cell23_235317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_235317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235317 prefixEnd_235317 := by exact prefixLift 235317
  have htrace : WordTrace (prefixWord ++ tailWord_235317) baseStart_235317 baseEnd_235317 := by
    simpa [prefixWord, tailWord_235317, baseEnd_235317] using wordTrace_append hprefix tailTrace_235317
  have hstable : (prefixWord ++ tailWord_235317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235317).length < 2 ^ (prefixWord ++ tailWord_235317).sum := by decide
  have hdescent : baseEnd_235317 < baseStart_235317 := by decide
  rcases family_descends (prefixWord ++ tailWord_235317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235334 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_235334 : Nat := 118140960795 + 235334 * 2 ^ 59
def prefixEnd_235334 : Nat := 4983230072969 + 3 ^ 40 * 235334 * 2
def baseEnd_235334 : Nat := 120839456345287488342725

theorem tailTrace_235334 : CollatzResearch.WordTrace tailWord_235334 prefixEnd_235334 120839456345287488342725 := by
  unfold tailWord_235334
  simp only [CollatzResearch.WordTrace]
  refine ⟨268229254044768271639783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5722224086288389794982037 268229254044768271639783)
  ·
    refine ⟨402343881067152407459675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268229254044768271639783 402343881067152407459675)
    ·
      refine ⟨603515821600728611189513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402343881067152407459675 603515821600728611189513)
      ·
        refine ⟨452636866200546458392135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603515821600728611189513 452636866200546458392135)
        ·
          refine ⟨678955299300819687588203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452636866200546458392135 678955299300819687588203)
          ·
            refine ⟨1018432948951229531382305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678955299300819687588203 1018432948951229531382305)
            ·
              refine ⟨763824711713422148536729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018432948951229531382305 763824711713422148536729)
              ·
                refine ⟨572868533785066611402547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763824711713422148536729 572868533785066611402547)
                ·
                  refine ⟨859302800677599917103821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572868533785066611402547 859302800677599917103821)
                  ·
                    refine ⟨322238550254099968913933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 859302800677599917103821 322238550254099968913933)
                    ·
                      refine ⟨120839456345287488342725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 322238550254099968913933 120839456345287488342725)
                      ·
                        rfl

theorem cell23_235334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_235334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235334 prefixEnd_235334 := by exact prefixLift 235334
  have htrace : WordTrace (prefixWord ++ tailWord_235334) baseStart_235334 baseEnd_235334 := by
    simpa [prefixWord, tailWord_235334, baseEnd_235334] using wordTrace_append hprefix tailTrace_235334
  have hstable : (prefixWord ++ tailWord_235334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235334).length < 2 ^ (prefixWord ++ tailWord_235334).sum := by decide
  have hdescent : baseEnd_235334 < baseStart_235334 := by decide
  rcases family_descends (prefixWord ++ tailWord_235334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235351 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 2, 1, 3]
def baseStart_235351 : Nat := 118140960795 + 235351 * 2 ^ 59
def prefixEnd_235351 : Nat := 4983230072969 + 3 ^ 40 * 235351 * 2
def baseEnd_235351 : Nat := 120848185516413921830147

theorem tailTrace_235351 : CollatzResearch.WordTrace tailWord_235351 prefixEnd_235351 120848185516413921830147 := by
  unfold tailWord_235351
  simp only [CollatzResearch.WordTrace]
  refine ⟨8583956170370996595841907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5722637446913997730561271 8583956170370996595841907)
  ·
    refine ⟨12875934255556494893762861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8583956170370996595841907 12875934255556494893762861)
    ·
      refine ⟨4828475345833685585161073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12875934255556494893762861 4828475345833685585161073)
      ·
        refine ⟨3621356509375264188870805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4828475345833685585161073 3621356509375264188870805)
        ·
          refine ⟨169751086376965508853319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3621356509375264188870805 169751086376965508853319)
          ·
            refine ⟨254626629565448263279979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169751086376965508853319 254626629565448263279979)
            ·
              refine ⟨381939944348172394919969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254626629565448263279979 381939944348172394919969)
              ·
                refine ⟨286454958261129296189977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381939944348172394919969 286454958261129296189977)
                ·
                  refine ⟨214841218695846972142483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286454958261129296189977 214841218695846972142483)
                  ·
                    refine ⟨322261828043770458213725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 214841218695846972142483 322261828043770458213725)
                    ·
                      refine ⟨120848185516413921830147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 322261828043770458213725 120848185516413921830147)
                      ·
                        rfl

theorem cell23_235351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_235351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235351 prefixEnd_235351 := by exact prefixLift 235351
  have htrace : WordTrace (prefixWord ++ tailWord_235351) baseStart_235351 baseEnd_235351 := by
    simpa [prefixWord, tailWord_235351, baseEnd_235351] using wordTrace_append hprefix tailTrace_235351
  have hstable : (prefixWord ++ tailWord_235351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235351).length < 2 ^ (prefixWord ++ tailWord_235351).sum := by decide
  have hdescent : baseEnd_235351 < baseStart_235351 := by decide
  rcases family_descends (prefixWord ++ tailWord_235351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235353 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_235353 : Nat := 118140960795 + 235353 * 2 ^ 59
def prefixEnd_235353 : Nat := 4983230072969 + 3 ^ 40 * 235353 * 2
def baseEnd_235353 : Nat := 120849212477722914005137

theorem tailTrace_235353 : CollatzResearch.WordTrace tailWord_235353 prefixEnd_235353 120849212477722914005137 := by
  unfold tailWord_235353
  simp only [CollatzResearch.WordTrace]
  refine ⟨8584029116363750937414713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5722686077575833958276475 8584029116363750937414713)
  ·
    refine ⟨6438021837272813203061035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8584029116363750937414713 6438021837272813203061035)
    ·
      refine ⟨9657032755909219804591553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6438021837272813203061035 9657032755909219804591553)
      ·
        refine ⟨7242774566931914853443665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9657032755909219804591553 7242774566931914853443665)
        ·
          refine ⟨5432080925198936140082749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7242774566931914853443665 5432080925198936140082749)
          ·
            refine ⟨2037030346949601052531031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5432080925198936140082749 2037030346949601052531031)
            ·
              refine ⟨3055545520424401578796547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037030346949601052531031 3055545520424401578796547)
              ·
                refine ⟨4583318280636602368194821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055545520424401578796547 4583318280636602368194821)
                ·
                  refine ⟨859372177619362944036529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4583318280636602368194821 859372177619362944036529)
                  ·
                    refine ⟨644529133214522208027397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 859372177619362944036529 644529133214522208027397)
                    ·
                      refine ⟨120849212477722914005137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 644529133214522208027397 120849212477722914005137)
                      ·
                        rfl

theorem cell23_235353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_235353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235353 prefixEnd_235353 := by exact prefixLift 235353
  have htrace : WordTrace (prefixWord ++ tailWord_235353) baseStart_235353 baseEnd_235353 := by
    simpa [prefixWord, tailWord_235353, baseEnd_235353] using wordTrace_append hprefix tailTrace_235353
  have hstable : (prefixWord ++ tailWord_235353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235353).length < 2 ^ (prefixWord ++ tailWord_235353).sum := by decide
  have hdescent : baseEnd_235353 < baseStart_235353 := by decide
  rcases family_descends (prefixWord ++ tailWord_235353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235374 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_235374 : Nat := 118140960795 + 235374 * 2 ^ 59
def prefixEnd_235374 : Nat := 4983230072969 + 3 ^ 40 * 235374 * 2
def baseEnd_235374 : Nat := 120859995571467331842541

theorem tailTrace_235374 : CollatzResearch.WordTrace tailWord_235374 prefixEnd_235374 120859995571467331842541 := by
  unfold tailWord_235374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1073099381160958940491147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5723196699525114349286117 1073099381160958940491147)
  ·
    refine ⟨1609649071741438410736721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1073099381160958940491147 1609649071741438410736721)
    ·
      refine ⟨1207236803806078808052541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1609649071741438410736721 1207236803806078808052541)
      ·
        refine ⟨452713801427279553019703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1207236803806078808052541 452713801427279553019703)
        ·
          refine ⟨679070702140919329529555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452713801427279553019703 679070702140919329529555)
          ·
            refine ⟨1018606053211378994294333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679070702140919329529555 1018606053211378994294333)
            ·
              refine ⟨381977269954267122860375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1018606053211378994294333 381977269954267122860375)
              ·
                refine ⟨572965904931400684290563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381977269954267122860375 572965904931400684290563)
                ·
                  refine ⟨859448857397101026435845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572965904931400684290563 859448857397101026435845)
                  ·
                    refine ⟨161146660761956442456721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 859448857397101026435845 161146660761956442456721)
                    ·
                      refine ⟨120859995571467331842541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161146660761956442456721 120859995571467331842541)
                      ·
                        rfl

theorem cell23_235374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_235374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235374 prefixEnd_235374 := by exact prefixLift 235374
  have htrace : WordTrace (prefixWord ++ tailWord_235374) baseStart_235374 baseEnd_235374 := by
    simpa [prefixWord, tailWord_235374, baseEnd_235374] using wordTrace_append hprefix tailTrace_235374
  have hstable : (prefixWord ++ tailWord_235374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235374).length < 2 ^ (prefixWord ++ tailWord_235374).sum := by decide
  have hdescent : baseEnd_235374 < baseStart_235374 := by decide
  rcases family_descends (prefixWord ++ tailWord_235374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235403 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 5]
def baseStart_235403 : Nat := 118140960795 + 235403 * 2 ^ 59
def prefixEnd_235403 : Nat := 4983230072969 + 3 ^ 40 * 235403 * 2
def baseEnd_235403 : Nat := 120874886510447718379907

theorem tailTrace_235403 : CollatzResearch.WordTrace tailWord_235403 prefixEnd_235403 120874886510447718379907 := by
  unfold tailWord_235403
  simp only [CollatzResearch.WordTrace]
  refine ⟨8585852766182609476734863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5723901844121739651156575 8585852766182609476734863)
  ·
    refine ⟨12878779149273914215102295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8585852766182609476734863 12878779149273914215102295)
    ·
      refine ⟨19318168723910871322653443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12878779149273914215102295 19318168723910871322653443)
      ·
        refine ⟨28977253085866306983980165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19318168723910871322653443 28977253085866306983980165)
        ·
          refine ⟨5433234953599932559496281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28977253085866306983980165 5433234953599932559496281)
          ·
            refine ⟨4074926215199949419622211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5433234953599932559496281 4074926215199949419622211)
            ·
              refine ⟨6112389322799924129433317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4074926215199949419622211 6112389322799924129433317)
              ·
                refine ⟨1146072998024985774268747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6112389322799924129433317 1146072998024985774268747)
                ·
                  refine ⟨1719109497037478661403121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146072998024985774268747 1719109497037478661403121)
                  ·
                    refine ⟨1289332122778108996052341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1719109497037478661403121 1289332122778108996052341)
                    ·
                      refine ⟨120874886510447718379907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1289332122778108996052341 120874886510447718379907)
                      ·
                        rfl

theorem cell23_235403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 5].length) (baseStart_235403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235403 prefixEnd_235403 := by exact prefixLift 235403
  have htrace : WordTrace (prefixWord ++ tailWord_235403) baseStart_235403 baseEnd_235403 := by
    simpa [prefixWord, tailWord_235403, baseEnd_235403] using wordTrace_append hprefix tailTrace_235403
  have hstable : (prefixWord ++ tailWord_235403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235403).length < 2 ^ (prefixWord ++ tailWord_235403).sum := by decide
  have hdescent : baseEnd_235403 < baseStart_235403 := by decide
  rcases family_descends (prefixWord ++ tailWord_235403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235420 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_235420 : Nat := 118140960795 + 235420 * 2 ^ 59
def prefixEnd_235420 : Nat := 4983230072969 + 3 ^ 40 * 235420 * 2
def baseEnd_235420 : Nat := 120883615681574151867329

theorem tailTrace_235420 : CollatzResearch.WordTrace tailWord_235420 prefixEnd_235420 120883615681574151867329 := by
  unfold tailWord_235420
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293236403560510690051857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5724315204747347586735809 4293236403560510690051857)
  ·
    refine ⟨3219927302670383017538893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4293236403560510690051857 3219927302670383017538893)
    ·
      refine ⟨1207472738501393631577085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3219927302670383017538893 1207472738501393631577085)
      ·
        refine ⟨452802276938022611841407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1207472738501393631577085 452802276938022611841407)
        ·
          refine ⟨679203415407033917762111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452802276938022611841407 679203415407033917762111)
          ·
            refine ⟨1018805123110550876643167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679203415407033917762111 1018805123110550876643167)
            ·
              refine ⟨1528207684665826314964751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018805123110550876643167 1528207684665826314964751)
              ·
                refine ⟨2292311526998739472447127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528207684665826314964751 2292311526998739472447127)
                ·
                  refine ⟨3438467290498109208670691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292311526998739472447127 3438467290498109208670691)
                  ·
                    refine ⟨5157700935747163813006037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3438467290498109208670691 5157700935747163813006037)
                    ·
                      refine ⟨120883615681574151867329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5157700935747163813006037 120883615681574151867329)
                      ·
                        rfl

theorem cell23_235420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_235420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235420 prefixEnd_235420 := by exact prefixLift 235420
  have htrace : WordTrace (prefixWord ++ tailWord_235420) baseStart_235420 baseEnd_235420 := by
    simpa [prefixWord, tailWord_235420, baseEnd_235420] using wordTrace_append hprefix tailTrace_235420
  have hstable : (prefixWord ++ tailWord_235420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235420).length < 2 ^ (prefixWord ++ tailWord_235420).sum := by decide
  have hdescent : baseEnd_235420 < baseStart_235420 := by decide
  rcases family_descends (prefixWord ++ tailWord_235420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235425 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 2, 2, 2]
def baseStart_235425 : Nat := 118140960795 + 235425 * 2 ^ 59
def prefixEnd_235425 : Nat := 4983230072969 + 3 ^ 40 * 235425 * 2
def baseEnd_235425 : Nat := 120886183084846632304807

theorem tailTrace_235425 : CollatzResearch.WordTrace tailWord_235425 prefixEnd_235425 120886183084846632304807 := by
  unfold tailWord_235425
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586655172102907234035729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5724436781401938156023819 8586655172102907234035729)
  ·
    refine ⟨6439991379077180425526797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8586655172102907234035729 6439991379077180425526797)
    ·
      refine ⟨2414996767153942659572549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6439991379077180425526797 2414996767153942659572549)
      ·
        refine ⟨452811893841364248669853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2414996767153942659572549 452811893841364248669853)
        ·
          refine ⟨169804460190511593251195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452811893841364248669853 169804460190511593251195)
          ·
            refine ⟨254706690285767389876793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169804460190511593251195 254706690285767389876793)
            ·
              refine ⟨191030017714325542407595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254706690285767389876793 191030017714325542407595)
              ·
                refine ⟨286545026571488313611393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191030017714325542407595 286545026571488313611393)
                ·
                  refine ⟨214908769928616235208545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286545026571488313611393 214908769928616235208545)
                  ·
                    refine ⟨161181577446462176406409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214908769928616235208545 161181577446462176406409)
                    ·
                      refine ⟨120886183084846632304807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161181577446462176406409 120886183084846632304807)
                      ·
                        rfl

theorem cell23_235425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_235425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235425 prefixEnd_235425 := by exact prefixLift 235425
  have htrace : WordTrace (prefixWord ++ tailWord_235425) baseStart_235425 baseEnd_235425 := by
    simpa [prefixWord, tailWord_235425, baseEnd_235425] using wordTrace_append hprefix tailTrace_235425
  have hstable : (prefixWord ++ tailWord_235425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235425).length < 2 ^ (prefixWord ++ tailWord_235425).sum := by decide
  have hdescent : baseEnd_235425 < baseStart_235425 := by decide
  rcases family_descends (prefixWord ++ tailWord_235425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235520 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 4]
def baseStart_235520 : Nat := 118140960795 + 235520 * 2 ^ 59
def prefixEnd_235520 : Nat := 4983230072969 + 3 ^ 40 * 235520 * 2
def baseEnd_235520 : Nat := 120934963747023760616869

theorem tailTrace_235520 : CollatzResearch.WordTrace tailWord_235520 prefixEnd_235520 120934963747023760616869 := by
  unfold tailWord_235520
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295060053379369229372007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5726746737839158972496009 4295060053379369229372007)
  ·
    refine ⟨6442590080069053844058011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4295060053379369229372007 6442590080069053844058011)
    ·
      refine ⟨9663885120103580766087017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6442590080069053844058011 9663885120103580766087017)
      ·
        refine ⟨7247913840077685574565263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9663885120103580766087017 7247913840077685574565263)
        ·
          refine ⟨10871870760116528361847895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7247913840077685574565263 10871870760116528361847895)
          ·
            refine ⟨16307806140174792542771843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10871870760116528361847895 16307806140174792542771843)
            ·
              refine ⟨24461709210262188814157765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16307806140174792542771843 24461709210262188814157765)
              ·
                refine ⟨4586570476924160402654581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24461709210262188814157765 4586570476924160402654581)
                ·
                  refine ⟨429990982211640037748867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4586570476924160402654581 429990982211640037748867)
                  ·
                    refine ⟨644986473317460056623301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 429990982211640037748867 644986473317460056623301)
                    ·
                      refine ⟨120934963747023760616869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 644986473317460056623301 120934963747023760616869)
                      ·
                        rfl

theorem cell23_235520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_235520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235520 prefixEnd_235520 := by exact prefixLift 235520
  have htrace : WordTrace (prefixWord ++ tailWord_235520) baseStart_235520 baseEnd_235520 := by
    simpa [prefixWord, tailWord_235520, baseEnd_235520] using wordTrace_append hprefix tailTrace_235520
  have hstable : (prefixWord ++ tailWord_235520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235520).length < 2 ^ (prefixWord ++ tailWord_235520).sum := by decide
  have hdescent : baseEnd_235520 < baseStart_235520 := by decide
  rcases family_descends (prefixWord ++ tailWord_235520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235554 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_235554 : Nat := 118140960795 + 235554 * 2 ^ 59
def prefixEnd_235554 : Nat := 4983230072969 + 3 ^ 40 * 235554 * 2
def baseEnd_235554 : Nat := 120952422089276627591713

theorem tailTrace_235554 : CollatzResearch.WordTrace tailWord_235554 prefixEnd_235554 120952422089276627591713 := by
  unfold tailWord_235554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2147840047158890566370429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5727573459090374843654477 2147840047158890566370429)
  ·
    refine ⟨805440017684583962388911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2147840047158890566370429 805440017684583962388911)
    ·
      refine ⟨1208160026526875943583367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 805440017684583962388911 1208160026526875943583367)
      ·
        refine ⟨1812240039790313915375051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208160026526875943583367 1812240039790313915375051)
        ·
          refine ⟨2718360059685470873062577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1812240039790313915375051 2718360059685470873062577)
          ·
            refine ⟨2038770044764103154796933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2718360059685470873062577 2038770044764103154796933)
            ·
              refine ⟨382269383393269341524425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2038770044764103154796933 382269383393269341524425)
              ·
                refine ⟨286702037544952006143319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382269383393269341524425 286702037544952006143319)
                ·
                  refine ⟨430053056317428009214979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286702037544952006143319 430053056317428009214979)
                  ·
                    refine ⟨645079584476142013822469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 430053056317428009214979 645079584476142013822469)
                    ·
                      refine ⟨120952422089276627591713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 645079584476142013822469 120952422089276627591713)
                      ·
                        rfl

theorem cell23_235554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_235554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235554 prefixEnd_235554 := by exact prefixLift 235554
  have htrace : WordTrace (prefixWord ++ tailWord_235554) baseStart_235554 baseEnd_235554 := by
    simpa [prefixWord, tailWord_235554, baseEnd_235554] using wordTrace_append hprefix tailTrace_235554
  have hstable : (prefixWord ++ tailWord_235554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235554).length < 2 ^ (prefixWord ++ tailWord_235554).sum := by decide
  have hdescent : baseEnd_235554 < baseStart_235554 := by decide
  rcases family_descends (prefixWord ++ tailWord_235554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235574 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_235574 : Nat := 118140960795 + 235574 * 2 ^ 59
def prefixEnd_235574 : Nat := 4983230072969 + 3 ^ 40 * 235574 * 2
def baseEnd_235574 : Nat := 120962691702366549341621

theorem tailTrace_235574 : CollatzResearch.WordTrace tailWord_235574 prefixEnd_235574 120962691702366549341621 := by
  unfold tailWord_235574
  simp only [CollatzResearch.WordTrace]
  refine ⟨537005603035194105075611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5728059765708737120806517 537005603035194105075611)
  ·
    refine ⟨805508404552791157613417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 537005603035194105075611 805508404552791157613417)
    ·
      refine ⟨604131303414593368210063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 805508404552791157613417 604131303414593368210063)
      ·
        refine ⟨906196955121890052315095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604131303414593368210063 906196955121890052315095)
        ·
          refine ⟨1359295432682835078472643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906196955121890052315095 1359295432682835078472643)
          ·
            refine ⟨2038943149024252617708965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359295432682835078472643 2038943149024252617708965)
            ·
              refine ⟨382301840442047365820431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2038943149024252617708965 382301840442047365820431)
              ·
                refine ⟨573452760663071048730647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382301840442047365820431 573452760663071048730647)
                ·
                  refine ⟨860179140994606573095971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573452760663071048730647 860179140994606573095971)
                  ·
                    refine ⟨1290268711491909859643957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 860179140994606573095971 1290268711491909859643957)
                    ·
                      refine ⟨120962691702366549341621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1290268711491909859643957 120962691702366549341621)
                      ·
                        rfl

theorem cell23_235574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_235574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235574 prefixEnd_235574 := by exact prefixLift 235574
  have htrace : WordTrace (prefixWord ++ tailWord_235574) baseStart_235574 baseEnd_235574 := by
    simpa [prefixWord, tailWord_235574, baseEnd_235574] using wordTrace_append hprefix tailTrace_235574
  have hstable : (prefixWord ++ tailWord_235574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235574).length < 2 ^ (prefixWord ++ tailWord_235574).sum := by decide
  have hdescent : baseEnd_235574 < baseStart_235574 := by decide
  rcases family_descends (prefixWord ++ tailWord_235574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235577 : List Nat := [1, 2, 1, 5, 3, 2, 9]
def baseStart_235577 : Nat := 118140960795 + 235577 * 2 ^ 59
def prefixEnd_235577 : Nat := 4983230072969 + 3 ^ 40 * 235577 * 2
def baseEnd_235577 : Nat := 1493385582028765896347

theorem tailTrace_235577 : CollatzResearch.WordTrace tailWord_235577 prefixEnd_235577 1493385582028765896347 := by
  unfold tailWord_235577
  simp only [CollatzResearch.WordTrace]
  refine ⟨8592199067552237193568985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5728132711701491462379323 8592199067552237193568985)
  ·
    refine ⟨6444149300664177895176739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8592199067552237193568985 6444149300664177895176739)
    ·
      refine ⟨9666223950996266842765109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6444149300664177895176739 9666223950996266842765109)
      ·
        refine ⟨906208495405900016509229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9666223950996266842765109 906208495405900016509229)
        ·
          refine ⟨339828185777212506190961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 906208495405900016509229 339828185777212506190961)
          ·
            refine ⟨254871139332909379643221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339828185777212506190961 254871139332909379643221)
            ·
              refine ⟨1493385582028765896347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 254871139332909379643221 1493385582028765896347)
              ·
                rfl

theorem cell23_235577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 9].length) (baseStart_235577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235577 prefixEnd_235577 := by exact prefixLift 235577
  have htrace : WordTrace (prefixWord ++ tailWord_235577) baseStart_235577 baseEnd_235577 := by
    simpa [prefixWord, tailWord_235577, baseEnd_235577] using wordTrace_append hprefix tailTrace_235577
  have hstable : (prefixWord ++ tailWord_235577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235577).length < 2 ^ (prefixWord ++ tailWord_235577).sum := by decide
  have hdescent : baseEnd_235577 < baseStart_235577 := by decide
  rcases family_descends (prefixWord ++ tailWord_235577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235597 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_235597 : Nat := 118140960795 + 235597 * 2 ^ 59
def prefixEnd_235597 : Nat := 4983230072969 + 3 ^ 40 * 235597 * 2
def baseEnd_235597 : Nat := 120974501757419959354015

theorem tailTrace_235597 : CollatzResearch.WordTrace tailWord_235597 prefixEnd_235597 120974501757419959354015 := by
  unfold tailWord_235597
  simp only [CollatzResearch.WordTrace]
  refine ⟨8592928527479780609297045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5728619018319853739531363 8592928527479780609297045)
  ·
    refine ⟨402793524725614716060799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8592928527479780609297045 402793524725614716060799)
    ·
      refine ⟨604190287088422074091199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402793524725614716060799 604190287088422074091199)
      ·
        refine ⟨906285430632633111136799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604190287088422074091199 906285430632633111136799)
        ·
          refine ⟨1359428145948949666705199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906285430632633111136799 1359428145948949666705199)
          ·
            refine ⟨2039142218923424500057799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359428145948949666705199 2039142218923424500057799)
            ·
              refine ⟨3058713328385136750086699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039142218923424500057799 3058713328385136750086699)
              ·
                refine ⟨4588069992577705125130049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058713328385136750086699 4588069992577705125130049)
                ·
                  refine ⟨3441052494433278843847537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4588069992577705125130049 3441052494433278843847537)
                  ·
                    refine ⟨2580789370824959132885653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3441052494433278843847537 2580789370824959132885653)
                    ·
                      refine ⟨120974501757419959354015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2580789370824959132885653 120974501757419959354015)
                      ·
                        rfl

theorem cell23_235597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_235597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235597 prefixEnd_235597 := by exact prefixLift 235597
  have htrace : WordTrace (prefixWord ++ tailWord_235597) baseStart_235597 baseEnd_235597 := by
    simpa [prefixWord, tailWord_235597, baseEnd_235597] using wordTrace_append hprefix tailTrace_235597
  have hstable : (prefixWord ++ tailWord_235597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235597).length < 2 ^ (prefixWord ++ tailWord_235597).sum := by decide
  have hdescent : baseEnd_235597 < baseStart_235597 := by decide
  rcases family_descends (prefixWord ++ tailWord_235597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235638 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_235638 : Nat := 118140960795 + 235638 * 2 ^ 59
def prefixEnd_235638 : Nat := 4983230072969 + 3 ^ 40 * 235638 * 2
def baseEnd_235638 : Nat := 120995554464254298941327

theorem tailTrace_235638 : CollatzResearch.WordTrace tailWord_235638 prefixEnd_235638 120995554464254298941327 := by
  unfold tailWord_235638
  simp only [CollatzResearch.WordTrace]
  refine ⟨537151495020702788221223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5729615946887496407693045 537151495020702788221223)
  ·
    refine ⟨805727242531054182331835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 537151495020702788221223 805727242531054182331835)
    ·
      refine ⟨1208590863796581273497753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 805727242531054182331835 1208590863796581273497753)
      ·
        refine ⟨906443147847435955123315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1208590863796581273497753 906443147847435955123315)
        ·
          refine ⟨1359664721771153932684973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906443147847435955123315 1359664721771153932684973)
          ·
            refine ⟨509874270664182724756865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1359664721771153932684973 509874270664182724756865)
            ·
              refine ⟨382405702998137043567649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509874270664182724756865 382405702998137043567649)
              ·
                refine ⟨286804277248602782675737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382405702998137043567649 286804277248602782675737)
                ·
                  refine ⟨215103207936452087006803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286804277248602782675737 215103207936452087006803)
                  ·
                    refine ⟨322654811904678130510205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 215103207936452087006803 322654811904678130510205)
                    ·
                      refine ⟨120995554464254298941327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 322654811904678130510205 120995554464254298941327)
                      ·
                        rfl

theorem cell23_235638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_235638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235638 prefixEnd_235638 := by exact prefixLift 235638
  have htrace : WordTrace (prefixWord ++ tailWord_235638) baseStart_235638 baseEnd_235638 := by
    simpa [prefixWord, tailWord_235638, baseEnd_235638] using wordTrace_append hprefix tailTrace_235638
  have hstable : (prefixWord ++ tailWord_235638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235638).length < 2 ^ (prefixWord ++ tailWord_235638).sum := by decide
  have hdescent : baseEnd_235638 < baseStart_235638 := by decide
  rcases family_descends (prefixWord ++ tailWord_235638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235640 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_235640 : Nat := 118140960795 + 235640 * 2 ^ 59
def prefixEnd_235640 : Nat := 4983230072969 + 3 ^ 40 * 235640 * 2
def baseEnd_235640 : Nat := 120996581425563291116317

theorem tailTrace_235640 : CollatzResearch.WordTrace tailWord_235640 prefixEnd_235640 120996581425563291116317 := by
  unfold tailWord_235640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4297248433161999476556187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5729664577549332635408249 4297248433161999476556187)
  ·
    refine ⟨6445872649742999214834281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4297248433161999476556187 6445872649742999214834281)
    ·
      refine ⟨4834404487307249411125711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6445872649742999214834281 4834404487307249411125711)
      ·
        refine ⟨7251606730960874116688567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834404487307249411125711 7251606730960874116688567)
        ·
          refine ⟨10877410096441311175032851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7251606730960874116688567 10877410096441311175032851)
          ·
            refine ⟨16316115144661966762549277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10877410096441311175032851 16316115144661966762549277)
            ·
              refine ⟨6118543179248237535955979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16316115144661966762549277 6118543179248237535955979)
              ·
                refine ⟨9177814768872356303933969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118543179248237535955979 9177814768872356303933969)
                ·
                  refine ⟨6883361076654267227950477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9177814768872356303933969 6883361076654267227950477)
                  ·
                    refine ⟨2581260403745350210481429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6883361076654267227950477 2581260403745350210481429)
                    ·
                      refine ⟨120996581425563291116317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2581260403745350210481429 120996581425563291116317)
                      ·
                        rfl

theorem cell23_235640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_235640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235640 prefixEnd_235640 := by exact prefixLift 235640
  have htrace : WordTrace (prefixWord ++ tailWord_235640) baseStart_235640 baseEnd_235640 := by
    simpa [prefixWord, tailWord_235640, baseEnd_235640] using wordTrace_append hprefix tailTrace_235640
  have hstable : (prefixWord ++ tailWord_235640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235640).length < 2 ^ (prefixWord ++ tailWord_235640).sum := by decide
  have hdescent : baseEnd_235640 < baseStart_235640 := by decide
  rcases family_descends (prefixWord ++ tailWord_235640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235657 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_235657 : Nat := 118140960795 + 235657 * 2 ^ 59
def prefixEnd_235657 : Nat := 4983230072969 + 3 ^ 40 * 235657 * 2
def baseEnd_235657 : Nat := 121005310596689724603739

theorem tailTrace_235657 : CollatzResearch.WordTrace tailWord_235657 prefixEnd_235657 121005310596689724603739 := by
  unfold tailWord_235657
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595116907262410856481225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5730077938174940570987483 8595116907262410856481225)
  ·
    refine ⟨6446337680446808142360919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8595116907262410856481225 6446337680446808142360919)
    ·
      refine ⟨9669506520670212213541379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6446337680446808142360919 9669506520670212213541379)
      ·
        refine ⟨14504259781005318320312069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9669506520670212213541379 14504259781005318320312069)
        ·
          refine ⟨2719548708938497185058513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14504259781005318320312069 2719548708938497185058513)
          ·
            refine ⟨2039661531703872888793885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2719548708938497185058513 2039661531703872888793885)
            ·
              refine ⟨764873074388952333297707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2039661531703872888793885 764873074388952333297707)
              ·
                refine ⟨1147309611583428499946561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764873074388952333297707 1147309611583428499946561)
                ·
                  refine ⟨860482208687571374959921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147309611583428499946561 860482208687571374959921)
                  ·
                    refine ⟨645361656515678531219941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 860482208687571374959921 645361656515678531219941)
                    ·
                      refine ⟨121005310596689724603739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 645361656515678531219941 121005310596689724603739)
                      ·
                        rfl

theorem cell23_235657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_235657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235657 prefixEnd_235657 := by exact prefixLift 235657
  have htrace : WordTrace (prefixWord ++ tailWord_235657) baseStart_235657 baseEnd_235657 := by
    simpa [prefixWord, tailWord_235657, baseEnd_235657] using wordTrace_append hprefix tailTrace_235657
  have hstable : (prefixWord ++ tailWord_235657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235657).length < 2 ^ (prefixWord ++ tailWord_235657).sum := by decide
  have hdescent : baseEnd_235657 < baseStart_235657 := by decide
  rcases family_descends (prefixWord ++ tailWord_235657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235701 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 7]
def baseStart_235701 : Nat := 118140960795 + 235701 * 2 ^ 59
def prefixEnd_235701 : Nat := 4983230072969 + 3 ^ 40 * 235701 * 2
def baseEnd_235701 : Nat := 13447544860609728050393

theorem tailTrace_235701 : CollatzResearch.WordTrace tailWord_235701 prefixEnd_235701 13447544860609728050393 := by
  unfold tailWord_235701
  simp only [CollatzResearch.WordTrace]
  refine ⟨8596721719103006371082957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5731147812735337580721971 8596721719103006371082957)
  ·
    refine ⟨3223770644663627389156109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8596721719103006371082957 3223770644663627389156109)
    ·
      refine ⟨1208913991748860270933541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3223770644663627389156109 1208913991748860270933541)
      ·
        refine ⟨226671373452911300800039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1208913991748860270933541 226671373452911300800039)
        ·
          refine ⟨340007060179366951200059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226671373452911300800039 340007060179366951200059)
          ·
            refine ⟨510010590269050426800089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340007060179366951200059 510010590269050426800089)
            ·
              refine ⟨382507942701787820100067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510010590269050426800089 382507942701787820100067)
              ·
                refine ⟨573761914052681730150101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382507942701787820100067 573761914052681730150101)
                ·
                  refine ⟨13447544860609728050393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 573761914052681730150101 13447544860609728050393)
                  ·
                    rfl

theorem cell23_235701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_235701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235701 prefixEnd_235701 := by exact prefixLift 235701
  have htrace : WordTrace (prefixWord ++ tailWord_235701) baseStart_235701 baseEnd_235701 := by
    simpa [prefixWord, tailWord_235701, baseEnd_235701] using wordTrace_append hprefix tailTrace_235701
  have hstable : (prefixWord ++ tailWord_235701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235701).length < 2 ^ (prefixWord ++ tailWord_235701).sum := by decide
  have hdescent : baseEnd_235701 < baseStart_235701 := by decide
  rcases family_descends (prefixWord ++ tailWord_235701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235717 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_235717 : Nat := 118140960795 + 235717 * 2 ^ 59
def prefixEnd_235717 : Nat := 4983230072969 + 3 ^ 40 * 235717 * 2
def baseEnd_235717 : Nat := 121036119435959489853463

theorem tailTrace_235717 : CollatzResearch.WordTrace tailWord_235717 prefixEnd_235717 121036119435959489853463 := by
  unfold tailWord_235717
  simp only [CollatzResearch.WordTrace]
  refine ⟨8597305287045041103665405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5731536858030027402443603 8597305287045041103665405)
  ·
    refine ⟨3223989482641890413874527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8597305287045041103665405 3223989482641890413874527)
    ·
      refine ⟨4835984223962835620811791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3223989482641890413874527 4835984223962835620811791)
      ·
        refine ⟨7253976335944253431217687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4835984223962835620811791 7253976335944253431217687)
        ·
          refine ⟨10880964503916380146826531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7253976335944253431217687 10880964503916380146826531)
          ·
            refine ⟨16321446755874570220239797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10880964503916380146826531 16321446755874570220239797)
            ·
              refine ⟨1530135633363240958147481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16321446755874570220239797 1530135633363240958147481)
              ·
                refine ⟨1147601725022430718610611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530135633363240958147481 1147601725022430718610611)
                ·
                  refine ⟨1721402587533646077915917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147601725022430718610611 1721402587533646077915917)
                  ·
                    refine ⟨645525970325117279218469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721402587533646077915917 645525970325117279218469)
                    ·
                      refine ⟨121036119435959489853463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 645525970325117279218469 121036119435959489853463)
                      ·
                        rfl

theorem cell23_235717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_235717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235717 prefixEnd_235717 := by exact prefixLift 235717
  have htrace : WordTrace (prefixWord ++ tailWord_235717) baseStart_235717 baseEnd_235717 := by
    simpa [prefixWord, tailWord_235717, baseEnd_235717] using wordTrace_append hprefix tailTrace_235717
  have hstable : (prefixWord ++ tailWord_235717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235717).length < 2 ^ (prefixWord ++ tailWord_235717).sum := by decide
  have hdescent : baseEnd_235717 < baseStart_235717 := by decide
  rcases family_descends (prefixWord ++ tailWord_235717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235751 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_235751 : Nat := 118140960795 + 235751 * 2 ^ 59
def prefixEnd_235751 : Nat := 4983230072969 + 3 ^ 40 * 235751 * 2
def baseEnd_235751 : Nat := 121053577778212356828307

theorem tailTrace_235751 : CollatzResearch.WordTrace tailWord_235751 prefixEnd_235751 121053577778212356828307 := by
  unfold tailWord_235751
  simp only [CollatzResearch.WordTrace]
  refine ⟨8598545368921864910403107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5732363579281243273602071 8598545368921864910403107)
  ·
    refine ⟨12897818053382797365604661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8598545368921864910403107 12897818053382797365604661)
    ·
      refine ⟨1209170442504637253025437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12897818053382797365604661 1209170442504637253025437)
      ·
        refine ⟨453438915939238969884539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1209170442504637253025437 453438915939238969884539)
        ·
          refine ⟨680158373908858454826809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453438915939238969884539 680158373908858454826809)
          ·
            refine ⟨510118780431643841120107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680158373908858454826809 510118780431643841120107)
            ·
              refine ⟨765178170647465761680161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510118780431643841120107 765178170647465761680161)
              ·
                refine ⟨573883627985599321260121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765178170647465761680161 573883627985599321260121)
                ·
                  refine ⟨430412720989199490945091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573883627985599321260121 430412720989199490945091)
                  ·
                    refine ⟨645619081483799236417637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 430412720989199490945091 645619081483799236417637)
                    ·
                      refine ⟨121053577778212356828307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 645619081483799236417637 121053577778212356828307)
                      ·
                        rfl

theorem cell23_235751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_235751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235751 prefixEnd_235751 := by exact prefixLift 235751
  have htrace : WordTrace (prefixWord ++ tailWord_235751) baseStart_235751 baseEnd_235751 := by
    simpa [prefixWord, tailWord_235751, baseEnd_235751] using wordTrace_append hprefix tailTrace_235751
  have hstable : (prefixWord ++ tailWord_235751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235751).length < 2 ^ (prefixWord ++ tailWord_235751).sum := by decide
  have hdescent : baseEnd_235751 < baseStart_235751 := by decide
  rcases family_descends (prefixWord ++ tailWord_235751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235761 : List Nat := [1, 2, 2, 2, 2, 1, 2, 6, 1, 4]
def baseStart_235761 : Nat := 118140960795 + 235761 * 2 ^ 59
def prefixEnd_235761 : Nat := 4983230072969 + 3 ^ 40 * 235761 * 2
def baseEnd_235761 : Nat := 40352904194919105901087

theorem tailTrace_235761 : CollatzResearch.WordTrace tailWord_235761 prefixEnd_235761 40352904194919105901087 := by
  unfold tailWord_235761
  simp only [CollatzResearch.WordTrace]
  refine ⟨8598910098885636618267137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5732606732590424412178091 8598910098885636618267137)
  ·
    refine ⟨6449182574164227463700353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8598910098885636618267137 6449182574164227463700353)
    ·
      refine ⟨4836886930623170597775265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6449182574164227463700353 4836886930623170597775265)
      ·
        refine ⟨3627665197967377948331449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4836886930623170597775265 3627665197967377948331449)
        ·
          refine ⟨2720748898475533461248587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3627665197967377948331449 2720748898475533461248587)
          ·
            refine ⟨4081123347713300191872881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720748898475533461248587 4081123347713300191872881)
            ·
              refine ⟨3060842510784975143904661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081123347713300191872881 3060842510784975143904661)
              ·
                refine ⟨143476992693045709870531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3060842510784975143904661 143476992693045709870531)
                ·
                  refine ⟨215215489039568564805797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143476992693045709870531 215215489039568564805797)
                  ·
                    refine ⟨40352904194919105901087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215215489039568564805797 40352904194919105901087)
                    ·
                      rfl

theorem cell23_235761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_235761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235761 prefixEnd_235761 := by exact prefixLift 235761
  have htrace : WordTrace (prefixWord ++ tailWord_235761) baseStart_235761 baseEnd_235761 := by
    simpa [prefixWord, tailWord_235761, baseEnd_235761] using wordTrace_append hprefix tailTrace_235761
  have hstable : (prefixWord ++ tailWord_235761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235761).length < 2 ^ (prefixWord ++ tailWord_235761).sum := by decide
  have hdescent : baseEnd_235761 < baseStart_235761 := by decide
  rcases family_descends (prefixWord ++ tailWord_235761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235811 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 2, 3, 2]
def baseStart_235811 : Nat := 118140960795 + 235811 * 2 ^ 59
def prefixEnd_235811 : Nat := 4983230072969 + 3 ^ 40 * 235811 * 2
def baseEnd_235811 : Nat := 121084386617482122078031

theorem tailTrace_235811 : CollatzResearch.WordTrace tailWord_235811 prefixEnd_235811 121084386617482122078031 := by
  unfold tailWord_235811
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600733748704495157587287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5733822499136330105058191 8600733748704495157587287)
  ·
    refine ⟨12901100623056742736380931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8600733748704495157587287 12901100623056742736380931)
    ·
      refine ⟨19351650934585114104571397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12901100623056742736380931 19351650934585114104571397)
      ·
        refine ⟨3628434550234708894607137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19351650934585114104571397 3628434550234708894607137)
        ·
          refine ⟨2721325912676031670955353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3628434550234708894607137 2721325912676031670955353)
          ·
            refine ⟨2040994434507023753216515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2721325912676031670955353 2040994434507023753216515)
            ·
              refine ⟨3061491651760535629824773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040994434507023753216515 3061491651760535629824773)
              ·
                refine ⟨574029684705100430592145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3061491651760535629824773 574029684705100430592145)
                ·
                  refine ⟨430522263528825322944109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574029684705100430592145 430522263528825322944109)
                  ·
                    refine ⟨161445848823309496104041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 430522263528825322944109 161445848823309496104041)
                    ·
                      refine ⟨121084386617482122078031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161445848823309496104041 121084386617482122078031)
                      ·
                        rfl

theorem cell23_235811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_235811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235811 prefixEnd_235811 := by exact prefixLift 235811
  have htrace : WordTrace (prefixWord ++ tailWord_235811) baseStart_235811 baseEnd_235811 := by
    simpa [prefixWord, tailWord_235811, baseEnd_235811] using wordTrace_append hprefix tailTrace_235811
  have hstable : (prefixWord ++ tailWord_235811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235811).length < 2 ^ (prefixWord ++ tailWord_235811).sum := by decide
  have hdescent : baseEnd_235811 < baseStart_235811 := by decide
  rcases family_descends (prefixWord ++ tailWord_235811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235834 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_235834 : Nat := 118140960795 + 235834 * 2 ^ 59
def prefixEnd_235834 : Nat := 4983230072969 + 3 ^ 40 * 235834 * 2
def baseEnd_235834 : Nat := 40365398890845177363475

theorem tailTrace_235834 : CollatzResearch.WordTrace tailWord_235834 prefixEnd_235834 40365398890845177363475 := by
  unfold tailWord_235834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150393156905292521418639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5734381751747446723783037 2150393156905292521418639)
  ·
    refine ⟨3225589735357938782127959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2150393156905292521418639 3225589735357938782127959)
    ·
      refine ⟨4838384603036908173191939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3225589735357938782127959 4838384603036908173191939)
      ·
        refine ⟨7257576904555362259787909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4838384603036908173191939 7257576904555362259787909)
        ·
          refine ⟨1360795669604130423710233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7257576904555362259787909 1360795669604130423710233)
          ·
            refine ⟨1020596752203097817782675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1360795669604130423710233 1020596752203097817782675)
            ·
              refine ⟨1530895128304646726674013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020596752203097817782675 1530895128304646726674013)
              ·
                refine ⟨574085673114242522502755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1530895128304646726674013 574085673114242522502755)
                ·
                  refine ⟨861128509671363783754133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574085673114242522502755 861128509671363783754133)
                  ·
                    refine ⟨40365398890845177363475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 861128509671363783754133 40365398890845177363475)
                    ·
                      rfl

theorem cell23_235834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_235834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235834 prefixEnd_235834 := by exact prefixLift 235834
  have htrace : WordTrace (prefixWord ++ tailWord_235834) baseStart_235834 baseEnd_235834 := by
    simpa [prefixWord, tailWord_235834, baseEnd_235834] using wordTrace_append hprefix tailTrace_235834
  have hstable : (prefixWord ++ tailWord_235834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235834).length < 2 ^ (prefixWord ++ tailWord_235834).sum := by decide
  have hdescent : baseEnd_235834 < baseStart_235834 := by decide
  rcases family_descends (prefixWord ++ tailWord_235834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235854 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_235854 : Nat := 118140960795 + 235854 * 2 ^ 59
def prefixEnd_235854 : Nat := 4983230072969 + 3 ^ 40 * 235854 * 2
def baseEnd_235854 : Nat := 121106466285625453840333

theorem tailTrace_235854 : CollatzResearch.WordTrace tailWord_235854 prefixEnd_235854 121106466285625453840333 := by
  unfold tailWord_235854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1075287760943589187675327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5734868058365809000935077 1075287760943589187675327)
  ·
    refine ⟨1612931641415383781512991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1075287760943589187675327 1612931641415383781512991)
    ·
      refine ⟨2419397462123075672269487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612931641415383781512991 2419397462123075672269487)
      ·
        refine ⟨3629096193184613508404231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419397462123075672269487 3629096193184613508404231)
        ·
          refine ⟨5443644289776920262606347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3629096193184613508404231 5443644289776920262606347)
          ·
            refine ⟨8165466434665380393909521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5443644289776920262606347 8165466434665380393909521)
            ·
              refine ⟨6124099825999035295432141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8165466434665380393909521 6124099825999035295432141)
              ·
                refine ⟨2296537434749638235787053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6124099825999035295432141 2296537434749638235787053)
                ·
                  refine ⟨861201538031114338420145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2296537434749638235787053 861201538031114338420145)
                  ·
                    refine ⟨645901153523335753815109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 861201538031114338420145 645901153523335753815109)
                    ·
                      refine ⟨121106466285625453840333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 645901153523335753815109 121106466285625453840333)
                      ·
                        rfl

theorem cell23_235854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_235854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235854 prefixEnd_235854 := by exact prefixLift 235854
  have htrace : WordTrace (prefixWord ++ tailWord_235854) baseStart_235854 baseEnd_235854 := by
    simpa [prefixWord, tailWord_235854, baseEnd_235854] using wordTrace_append hprefix tailTrace_235854
  have hstable : (prefixWord ++ tailWord_235854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235854).length < 2 ^ (prefixWord ++ tailWord_235854).sum := by decide
  have hdescent : baseEnd_235854 < baseStart_235854 := by decide
  rcases family_descends (prefixWord ++ tailWord_235854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235858 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_235858 : Nat := 118140960795 + 235858 * 2 ^ 59
def prefixEnd_235858 : Nat := 4983230072969 + 3 ^ 40 * 235858 * 2
def baseEnd_235858 : Nat := 121108520208243438190315

theorem tailTrace_235858 : CollatzResearch.WordTrace tailWord_235858 prefixEnd_235858 121108520208243438190315 := by
  unfold tailWord_235858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150611994883555546137057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5734965319689481456365485 2150611994883555546137057)
  ·
    refine ⟨1612958996162666659602793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2150611994883555546137057 1612958996162666659602793)
    ·
      refine ⟨1209719247121999994702095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1612958996162666659602793 1209719247121999994702095)
      ·
        refine ⟨1814578870682999992053143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209719247121999994702095 1814578870682999992053143)
        ·
          refine ⟨2721868306024499988079715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814578870682999992053143 2721868306024499988079715)
          ·
            refine ⟨4082802459036749982119573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721868306024499988079715 4082802459036749982119573)
            ·
              refine ⟨191381365267347655411855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4082802459036749982119573 191381365267347655411855)
              ·
                refine ⟨287072047901021483117783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191381365267347655411855 287072047901021483117783)
                ·
                  refine ⟨430608071851532224676675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287072047901021483117783 430608071851532224676675)
                  ·
                    refine ⟨645912107777298337015013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 430608071851532224676675 645912107777298337015013)
                    ·
                      refine ⟨121108520208243438190315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 645912107777298337015013 121108520208243438190315)
                      ·
                        rfl

theorem cell23_235858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_235858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235858 prefixEnd_235858 := by exact prefixLift 235858
  have htrace : WordTrace (prefixWord ++ tailWord_235858) baseStart_235858 baseEnd_235858 := by
    simpa [prefixWord, tailWord_235858, baseEnd_235858] using wordTrace_append hprefix tailTrace_235858
  have hstable : (prefixWord ++ tailWord_235858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235858).length < 2 ^ (prefixWord ++ tailWord_235858).sum := by decide
  have hdescent : baseEnd_235858 < baseStart_235858 := by decide
  rcases family_descends (prefixWord ++ tailWord_235858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235875 : List Nat := [1, 1, 1, 5, 2, 1, 1, 6, 1, 2, 2]
def baseStart_235875 : Nat := 118140960795 + 235875 * 2 ^ 59
def prefixEnd_235875 : Nat := 4983230072969 + 3 ^ 40 * 235875 * 2
def baseEnd_235875 : Nat := 121117249379369871677737

theorem tailTrace_235875 : CollatzResearch.WordTrace tailWord_235875 prefixEnd_235875 121117249379369871677737 := by
  unfold tailWord_235875
  simp only [CollatzResearch.WordTrace]
  refine ⟨8603068020472634087917079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5735378680315089391944719 8603068020472634087917079)
  ·
    refine ⟨12904602030708951131875619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8603068020472634087917079 12904602030708951131875619)
    ·
      refine ⟨19356903046063426697813429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12904602030708951131875619 19356903046063426697813429)
      ·
        refine ⟨1814709660568446252920009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19356903046063426697813429 1814709660568446252920009)
        ·
          refine ⟨1361032245426334689690007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1814709660568446252920009 1361032245426334689690007)
          ·
            refine ⟨2041548368139502034535011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361032245426334689690007 2041548368139502034535011)
            ·
              refine ⟨3062322552209253051802517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041548368139502034535011 3062322552209253051802517)
              ·
                refine ⟨143546369634808736803243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3062322552209253051802517 143546369634808736803243)
                ·
                  refine ⟨215319554452213105204865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143546369634808736803243 215319554452213105204865)
                  ·
                    refine ⟨161489665839159828903649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215319554452213105204865 161489665839159828903649)
                    ·
                      refine ⟨121117249379369871677737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161489665839159828903649 121117249379369871677737)
                      ·
                        rfl

theorem cell23_235875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_235875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235875 prefixEnd_235875 := by exact prefixLift 235875
  have htrace : WordTrace (prefixWord ++ tailWord_235875) baseStart_235875 baseEnd_235875 := by
    simpa [prefixWord, tailWord_235875, baseEnd_235875] using wordTrace_append hprefix tailTrace_235875
  have hstable : (prefixWord ++ tailWord_235875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235875).length < 2 ^ (prefixWord ++ tailWord_235875).sum := by decide
  have hdescent : baseEnd_235875 < baseStart_235875 := by decide
  rcases family_descends (prefixWord ++ tailWord_235875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235946 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_235946 : Nat := 118140960795 + 235946 * 2 ^ 59
def prefixEnd_235946 : Nat := 4983230072969 + 3 ^ 40 * 235946 * 2
def baseEnd_235946 : Nat := 121153706505839093889911

theorem tailTrace_235946 : CollatzResearch.WordTrace tailWord_235946 prefixEnd_235946 121153706505839093889911 := by
  unfold tailWord_235946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2151414400803853303437923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5737105068810275475834461 2151414400803853303437923)
  ·
    refine ⟨3227121601205779955156885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2151414400803853303437923 3227121601205779955156885)
    ·
      refine ⟨151271325056520935397979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3227121601205779955156885 151271325056520935397979)
      ·
        refine ⟨226906987584781403096969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151271325056520935397979 226906987584781403096969)
        ·
          refine ⟨170180240688586052322727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226906987584781403096969 170180240688586052322727)
          ·
            refine ⟨255270361032879078484091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170180240688586052322727 255270361032879078484091)
            ·
              refine ⟨382905541549318617726137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255270361032879078484091 382905541549318617726137)
              ·
                refine ⟨287179156161988963294603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382905541549318617726137 287179156161988963294603)
                ·
                  refine ⟨430768734242983444941905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287179156161988963294603 430768734242983444941905)
                  ·
                    refine ⟨323076550682237583706429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 430768734242983444941905 323076550682237583706429)
                    ·
                      refine ⟨121153706505839093889911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 323076550682237583706429 121153706505839093889911)
                      ·
                        rfl

theorem cell23_235946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_235946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235946 prefixEnd_235946 := by exact prefixLift 235946
  have htrace : WordTrace (prefixWord ++ tailWord_235946) baseStart_235946 baseEnd_235946 := by
    simpa [prefixWord, tailWord_235946, baseEnd_235946] using wordTrace_append hprefix tailTrace_235946
  have hstable : (prefixWord ++ tailWord_235946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235946).length < 2 ^ (prefixWord ++ tailWord_235946).sum := by decide
  have hdescent : baseEnd_235946 < baseStart_235946 := by decide
  rcases family_descends (prefixWord ++ tailWord_235946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235954 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 9]
def baseStart_235954 : Nat := 118140960795 + 235954 * 2 ^ 59
def prefixEnd_235954 : Nat := 4983230072969 + 3 ^ 40 * 235954 * 2
def baseEnd_235954 : Nat := 13461979372341673621097

theorem tailTrace_235954 : CollatzResearch.WordTrace tailWord_235954 prefixEnd_235954 13461979372341673621097 := by
  unfold tailWord_235954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2151487346796607645010729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5737299591457620386695277 2151487346796607645010729)
  ·
    refine ⟨1613615510097455733758047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2151487346796607645010729 1613615510097455733758047)
    ·
      refine ⟨2420423265146183600637071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1613615510097455733758047 2420423265146183600637071)
      ·
        refine ⟨3630634897719275400955607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420423265146183600637071 3630634897719275400955607)
        ·
          refine ⟨5445952346578913101433411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3630634897719275400955607 5445952346578913101433411)
          ·
            refine ⟨8168928519868369652150117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5445952346578913101433411 8168928519868369652150117)
            ·
              refine ⟨1531674097475319309778147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8168928519868369652150117 1531674097475319309778147)
              ·
                refine ⟨2297511146212978964667221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531674097475319309778147 2297511146212978964667221)
                ·
                  refine ⟨13461979372341673621097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2297511146212978964667221 13461979372341673621097)
                  ·
                    rfl

theorem cell23_235954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_235954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235954 prefixEnd_235954 := by exact prefixLift 235954
  have htrace : WordTrace (prefixWord ++ tailWord_235954) baseStart_235954 baseEnd_235954 := by
    simpa [prefixWord, tailWord_235954, baseEnd_235954] using wordTrace_append hprefix tailTrace_235954
  have hstable : (prefixWord ++ tailWord_235954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235954).length < 2 ^ (prefixWord ++ tailWord_235954).sum := by decide
  have hdescent : baseEnd_235954 < baseStart_235954 := by decide
  rcases family_descends (prefixWord ++ tailWord_235954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235971 : List Nat := [1, 1, 1, 3, 1, 1, 3, 7, 5]
def baseStart_235971 : Nat := 118140960795 + 235971 * 2 ^ 59
def prefixEnd_235971 : Nat := 4983230072969 + 3 ^ 40 * 235971 * 2
def baseEnd_235971 : Nat := 13462949280244610675255

theorem tailTrace_235971 : CollatzResearch.WordTrace tailWord_235971 prefixEnd_235971 13462949280244610675255 := by
  unfold tailWord_235971
  simp only [CollatzResearch.WordTrace]
  refine ⟨8606569428124842483411767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5737712952083228322274511 8606569428124842483411767)
  ·
    refine ⟨12909854142187263725117651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8606569428124842483411767 12909854142187263725117651)
    ·
      refine ⟨19364781213280895587676477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12909854142187263725117651 19364781213280895587676477)
      ·
        refine ⟨7261792954980335845378679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19364781213280895587676477 7261792954980335845378679)
        ·
          refine ⟨10892689432470503768068019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7261792954980335845378679 10892689432470503768068019)
          ·
            refine ⟨16339034148705755652102029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10892689432470503768068019 16339034148705755652102029)
            ·
              refine ⟨6127137805764658369538261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16339034148705755652102029 6127137805764658369538261)
              ·
                refine ⟨143604792322609180536053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6127137805764658369538261 143604792322609180536053)
                ·
                  refine ⟨13462949280244610675255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143604792322609180536053 13462949280244610675255)
                  ·
                    rfl

theorem cell23_235971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 5].length) (baseStart_235971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_235971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_235971 prefixEnd_235971 := by exact prefixLift 235971
  have htrace : WordTrace (prefixWord ++ tailWord_235971) baseStart_235971 baseEnd_235971 := by
    simpa [prefixWord, tailWord_235971, baseEnd_235971] using wordTrace_append hprefix tailTrace_235971
  have hstable : (prefixWord ++ tailWord_235971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235971).length < 2 ^ (prefixWord ++ tailWord_235971).sum := by decide
  have hdescent : baseEnd_235971 < baseStart_235971 := by decide
  rcases family_descends (prefixWord ++ tailWord_235971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236018 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_236018 : Nat := 118140960795 + 236018 * 2 ^ 59
def prefixEnd_236018 : Nat := 4983230072969 + 3 ^ 40 * 236018 * 2
def baseEnd_236018 : Nat := 40396892370987604063193

theorem tailTrace_236018 : CollatzResearch.WordTrace tailWord_236018 prefixEnd_236018 40396892370987604063193 := by
  unfold tailWord_236018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152070914738642377593177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5738855772636379673581805 2152070914738642377593177)
  ·
    refine ⟨1614053186053981783194883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2152070914738642377593177 1614053186053981783194883)
    ·
      refine ⟨2421079779080972674792325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614053186053981783194883 2421079779080972674792325)
      ·
        refine ⟨453952458577682376523561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2421079779080972674792325 453952458577682376523561)
        ·
          refine ⟨340464343933261782392671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453952458577682376523561 340464343933261782392671)
          ·
            refine ⟨510696515899892673589007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340464343933261782392671 510696515899892673589007)
            ·
              refine ⟨766044773849839010383511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510696515899892673589007 766044773849839010383511)
              ·
                refine ⟨1149067160774758515575267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766044773849839010383511 1149067160774758515575267)
                ·
                  refine ⟨1723600741162137773362901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149067160774758515575267 1723600741162137773362901)
                  ·
                    refine ⟨40396892370987604063193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1723600741162137773362901 40396892370987604063193)
                    ·
                      rfl

theorem cell23_236018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_236018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236018 prefixEnd_236018 := by exact prefixLift 236018
  have htrace : WordTrace (prefixWord ++ tailWord_236018) baseStart_236018 baseEnd_236018 := by
    simpa [prefixWord, tailWord_236018, baseEnd_236018] using wordTrace_append hprefix tailTrace_236018
  have hstable : (prefixWord ++ tailWord_236018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236018).length < 2 ^ (prefixWord ++ tailWord_236018).sum := by decide
  have hdescent : baseEnd_236018 < baseStart_236018 := by decide
  rcases family_descends (prefixWord ++ tailWord_236018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236031 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 5, 4]
def baseStart_236031 : Nat := 118140960795 + 236031 * 2 ^ 59
def prefixEnd_236031 : Nat := 4983230072969 + 3 ^ 40 * 236031 * 2
def baseEnd_236031 : Nat := 40399117453823753775673

theorem tailTrace_236031 : CollatzResearch.WordTrace tailWord_236031 prefixEnd_236031 40399117453823753775673 := by
  unfold tailWord_236031
  simp only [CollatzResearch.WordTrace]
  refine ⟨8608757807907472730595947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5739171871938315153730631 8608757807907472730595947)
  ·
    refine ⟨12913136711861209095893921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8608757807907472730595947 12913136711861209095893921)
    ·
      refine ⟨9684852533895906821920441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12913136711861209095893921 9684852533895906821920441)
      ·
        refine ⟨7263639400421930116440331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9684852533895906821920441 7263639400421930116440331)
        ·
          refine ⟨10895459100632895174660497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7263639400421930116440331 10895459100632895174660497)
          ·
            refine ⟨8171594325474671380995373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10895459100632895174660497 8171594325474671380995373)
            ·
              refine ⟨3064347872053001767873265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8171594325474671380995373 3064347872053001767873265)
              ·
                refine ⟨2298260904039751325904949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064347872053001767873265 2298260904039751325904949)
                ·
                  refine ⟨215461959753726686803589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2298260904039751325904949 215461959753726686803589)
                  ·
                    refine ⟨40399117453823753775673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215461959753726686803589 40399117453823753775673)
                    ·
                      rfl

theorem cell23_236031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 4].length) (baseStart_236031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236031 prefixEnd_236031 := by exact prefixLift 236031
  have htrace : WordTrace (prefixWord ++ tailWord_236031) baseStart_236031 baseEnd_236031 := by
    simpa [prefixWord, tailWord_236031, baseEnd_236031] using wordTrace_append hprefix tailTrace_236031
  have hstable : (prefixWord ++ tailWord_236031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236031).length < 2 ^ (prefixWord ++ tailWord_236031).sum := by decide
  have hdescent : baseEnd_236031 < baseStart_236031 := by decide
  rcases family_descends (prefixWord ++ tailWord_236031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236126 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_236126 : Nat := 118140960795 + 236126 * 2 ^ 59
def prefixEnd_236126 : Nat := 4983230072969 + 3 ^ 40 * 236126 * 2
def baseEnd_236126 : Nat := 121246133023648389639083

theorem tailTrace_236126 : CollatzResearch.WordTrace tailWord_236126 prefixEnd_236126 121246133023648389639083 := by
  unfold tailWord_236126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076527842820412994413029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5741481828375535970202821 1076527842820412994413029)
  ·
    refine ⟨201848970528827436452443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1076527842820412994413029 201848970528827436452443)
    ·
      refine ⟨302773455793241154678665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201848970528827436452443 302773455793241154678665)
      ·
        refine ⟨227080091844930866008999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302773455793241154678665 227080091844930866008999)
        ·
          refine ⟨340620137767396299013499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227080091844930866008999 340620137767396299013499)
          ·
            refine ⟨510930206651094448520249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340620137767396299013499 510930206651094448520249)
            ·
              refine ⟨383197654988320836390187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510930206651094448520249 383197654988320836390187)
              ·
                refine ⟨574796482482481254585281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383197654988320836390187 574796482482481254585281)
                ·
                  refine ⟨431097361861860940938961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574796482482481254585281 431097361861860940938961)
                  ·
                    refine ⟨323323021396395705704221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 431097361861860940938961 323323021396395705704221)
                    ·
                      refine ⟨121246133023648389639083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 323323021396395705704221 121246133023648389639083)
                      ·
                        rfl

theorem cell23_236126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_236126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236126 prefixEnd_236126 := by exact prefixLift 236126
  have htrace : WordTrace (prefixWord ++ tailWord_236126) baseStart_236126 baseEnd_236126 := by
    simpa [prefixWord, tailWord_236126, baseEnd_236126] using wordTrace_append hprefix tailTrace_236126
  have hstable : (prefixWord ++ tailWord_236126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236126).length < 2 ^ (prefixWord ++ tailWord_236126).sum := by decide
  have hdescent : baseEnd_236126 < baseStart_236126 := by decide
  rcases family_descends (prefixWord ++ tailWord_236126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236128 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 2, 6, 2]
def baseStart_236128 : Nat := 118140960795 + 236128 * 2 ^ 59
def prefixEnd_236128 : Nat := 4983230072969 + 3 ^ 40 * 236128 * 2
def baseEnd_236128 : Nat := 121247159984957381814073

theorem tailTrace_236128 : CollatzResearch.WordTrace tailWord_236128 prefixEnd_236128 121247159984957381814073 := by
  unfold tailWord_236128
  simp only [CollatzResearch.WordTrace]
  refine ⟨4306147844278029148438519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5741530459037372197918025 4306147844278029148438519)
  ·
    refine ⟨6459221766417043722657779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4306147844278029148438519 6459221766417043722657779)
    ·
      refine ⟨9688832649625565583986669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6459221766417043722657779 9688832649625565583986669)
      ·
        refine ⟨3633312243609587093995001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9688832649625565583986669 3633312243609587093995001)
        ·
          refine ⟨2724984182707190320496251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3633312243609587093995001 2724984182707190320496251)
          ·
            refine ⟨4087476274060785480744377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724984182707190320496251 4087476274060785480744377)
            ·
              refine ⟨3065607205545589110558283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4087476274060785480744377 3065607205545589110558283)
              ·
                refine ⟨4598410808318383665837425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065607205545589110558283 4598410808318383665837425)
                ·
                  refine ⟨3448808106238787749378069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4598410808318383665837425 3448808106238787749378069)
                  ·
                    refine ⟨161662879979943175752097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3448808106238787749378069 161662879979943175752097)
                    ·
                      refine ⟨121247159984957381814073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161662879979943175752097 121247159984957381814073)
                      ·
                        rfl

theorem cell23_236128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_236128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236128 prefixEnd_236128 := by exact prefixLift 236128
  have htrace : WordTrace (prefixWord ++ tailWord_236128) baseStart_236128 baseEnd_236128 := by
    simpa [prefixWord, tailWord_236128, baseEnd_236128] using wordTrace_append hprefix tailTrace_236128
  have hstable : (prefixWord ++ tailWord_236128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236128).length < 2 ^ (prefixWord ++ tailWord_236128).sum := by decide
  have hdescent : baseEnd_236128 < baseStart_236128 := by decide
  rcases family_descends (prefixWord ++ tailWord_236128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236138 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_236138 : Nat := 118140960795 + 236138 * 2 ^ 59
def prefixEnd_236138 : Nat := 4983230072969 + 3 ^ 40 * 236138 * 2
def baseEnd_236138 : Nat := 40417431597167447563009

theorem tailTrace_236138 : CollatzResearch.WordTrace tailWord_236138 prefixEnd_236138 40417431597167447563009 := by
  unfold tailWord_236138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2153165104629957501185267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5741773612346553336494045 2153165104629957501185267)
  ·
    refine ⟨3229747656944936251777901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2153165104629957501185267 3229747656944936251777901)
    ·
      refine ⟨1211155371354351094416713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3229747656944936251777901 1211155371354351094416713)
      ·
        refine ⟨908366528515763320812535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1211155371354351094416713 908366528515763320812535)
        ·
          refine ⟨1362549792773644981218803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908366528515763320812535 1362549792773644981218803)
          ·
            refine ⟨2043824689160467471828205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362549792773644981218803 2043824689160467471828205)
            ·
              refine ⟨766434258435175301935577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2043824689160467471828205 766434258435175301935577)
              ·
                refine ⟨574825693826381476451683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766434258435175301935577 574825693826381476451683)
                ·
                  refine ⟨862238540739572214677525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574825693826381476451683 862238540739572214677525)
                  ·
                    refine ⟨40417431597167447563009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 862238540739572214677525 40417431597167447563009)
                    ·
                      rfl

theorem cell23_236138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_236138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236138 prefixEnd_236138 := by exact prefixLift 236138
  have htrace : WordTrace (prefixWord ++ tailWord_236138) baseStart_236138 baseEnd_236138 := by
    simpa [prefixWord, tailWord_236138, baseEnd_236138] using wordTrace_append hprefix tailTrace_236138
  have hstable : (prefixWord ++ tailWord_236138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236138).length < 2 ^ (prefixWord ++ tailWord_236138).sum := by decide
  have hdescent : baseEnd_236138 < baseStart_236138 := by decide
  rcases family_descends (prefixWord ++ tailWord_236138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236142 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_236142 : Nat := 118140960795 + 236142 * 2 ^ 59
def prefixEnd_236142 : Nat := 4983230072969 + 3 ^ 40 * 236142 * 2
def baseEnd_236142 : Nat := 40418116238040109013003

theorem tailTrace_236142 : CollatzResearch.WordTrace tailWord_236142 prefixEnd_236142 40418116238040109013003 := by
  unfold tailWord_236142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076600788813167335985835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5741870873670225791924453 1076600788813167335985835)
  ·
    refine ⟨1614901183219751003978753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1076600788813167335985835 1614901183219751003978753)
    ·
      refine ⟨1211175887414813252984065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1614901183219751003978753 1211175887414813252984065)
      ·
        refine ⟨908381915561109939738049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1211175887414813252984065 908381915561109939738049)
        ·
          refine ⟨681286436670832454803537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908381915561109939738049 681286436670832454803537)
          ·
            refine ⟨510964827503124341102653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681286436670832454803537 510964827503124341102653)
            ·
              refine ⟨191611810313671627913495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510964827503124341102653 191611810313671627913495)
              ·
                refine ⟨287417715470507441870243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191611810313671627913495 287417715470507441870243)
                ·
                  refine ⟨431126573205761162805365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287417715470507441870243 431126573205761162805365)
                  ·
                    refine ⟨40418116238040109013003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 431126573205761162805365 40418116238040109013003)
                    ·
                      rfl

theorem cell23_236142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_236142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236142 prefixEnd_236142 := by exact prefixLift 236142
  have htrace : WordTrace (prefixWord ++ tailWord_236142) baseStart_236142 baseEnd_236142 := by
    simpa [prefixWord, tailWord_236142, baseEnd_236142] using wordTrace_append hprefix tailTrace_236142
  have hstable : (prefixWord ++ tailWord_236142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236142).length < 2 ^ (prefixWord ++ tailWord_236142).sum := by decide
  have hdescent : baseEnd_236142 < baseStart_236142 := by decide
  rcases family_descends (prefixWord ++ tailWord_236142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236199 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_236199 : Nat := 118140960795 + 236199 * 2 ^ 59
def prefixEnd_236199 : Nat := 4983230072969 + 3 ^ 40 * 236199 * 2
def baseEnd_236199 : Nat := 121283617111426604026247

theorem tailTrace_236199 : CollatzResearch.WordTrace tailWord_236199 prefixEnd_236199 121283617111426604026247 := by
  unfold tailWord_236199
  simp only [CollatzResearch.WordTrace]
  refine ⟨8614885271298837422711651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5743256847532558281807767 8614885271298837422711651)
  ·
    refine ⟨12922327906948256134067477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8614885271298837422711651 12922327906948256134067477)
    ·
      refine ⟨605734120638199506284413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12922327906948256134067477 605734120638199506284413)
      ·
        refine ⟨227150295239324814856655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605734120638199506284413 227150295239324814856655)
        ·
          refine ⟨340725442858987222284983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227150295239324814856655 340725442858987222284983)
          ·
            refine ⟨511088164288480833427475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340725442858987222284983 511088164288480833427475)
            ·
              refine ⟨766632246432721250141213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511088164288480833427475 766632246432721250141213)
              ·
                refine ⟨287487092412270468802955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 766632246432721250141213 287487092412270468802955)
                ·
                  refine ⟨431230638618405703204433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287487092412270468802955 431230638618405703204433)
                  ·
                    refine ⟨323422978963804277403325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 431230638618405703204433 323422978963804277403325)
                    ·
                      refine ⟨121283617111426604026247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 323422978963804277403325 121283617111426604026247)
                      ·
                        rfl

theorem cell23_236199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_236199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236199 prefixEnd_236199 := by exact prefixLift 236199
  have htrace : WordTrace (prefixWord ++ tailWord_236199) baseStart_236199 baseEnd_236199 := by
    simpa [prefixWord, tailWord_236199, baseEnd_236199] using wordTrace_append hprefix tailTrace_236199
  have hstable : (prefixWord ++ tailWord_236199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236199).length < 2 ^ (prefixWord ++ tailWord_236199).sum := by decide
  have hdescent : baseEnd_236199 < baseStart_236199 := by decide
  rcases family_descends (prefixWord ++ tailWord_236199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236269 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_236269 : Nat := 118140960795 + 236269 * 2 ^ 59
def prefixEnd_236269 : Nat := 4983230072969 + 3 ^ 40 * 236269 * 2
def baseEnd_236269 : Nat := 121319560757241330150925

theorem tailTrace_236269 : CollatzResearch.WordTrace tailWord_236269 prefixEnd_236269 121319560757241330150925 := by
  unfold tailWord_236269
  simp only [CollatzResearch.WordTrace]
  refine ⟨8617438381045239377759861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5744958920696826251839907 8617438381045239377759861)
  ·
    refine ⟨807884848222991191664987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8617438381045239377759861 807884848222991191664987)
    ·
      refine ⟨1211827272334486787497481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807884848222991191664987 1211827272334486787497481)
      ·
        refine ⟨908870454250865090623111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1211827272334486787497481 908870454250865090623111)
        ·
          refine ⟨1363305681376297635934667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908870454250865090623111 1363305681376297635934667)
          ·
            refine ⟨2044958522064446453902001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363305681376297635934667 2044958522064446453902001)
            ·
              refine ⟨1533718891548334840426501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044958522064446453902001 1533718891548334840426501)
              ·
                refine ⟨287572292165312782579969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1533718891548334840426501 287572292165312782579969)
                ·
                  refine ⟨215679219123984586934977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287572292165312782579969 215679219123984586934977)
                  ·
                    refine ⟨161759414342988440201233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215679219123984586934977 161759414342988440201233)
                    ·
                      refine ⟨121319560757241330150925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161759414342988440201233 121319560757241330150925)
                      ·
                        rfl

theorem cell23_236269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_236269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236269 prefixEnd_236269 := by exact prefixLift 236269
  have htrace : WordTrace (prefixWord ++ tailWord_236269) baseStart_236269 baseEnd_236269 := by
    simpa [prefixWord, tailWord_236269, baseEnd_236269] using wordTrace_append hprefix tailTrace_236269
  have hstable : (prefixWord ++ tailWord_236269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236269).length < 2 ^ (prefixWord ++ tailWord_236269).sum := by decide
  have hdescent : baseEnd_236269 < baseStart_236269 := by decide
  rcases family_descends (prefixWord ++ tailWord_236269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236286 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_236286 : Nat := 118140960795 + 236286 * 2 ^ 59
def prefixEnd_236286 : Nat := 4983230072969 + 3 ^ 40 * 236286 * 2
def baseEnd_236286 : Nat := 121328289928367763638347

theorem tailTrace_236286 : CollatzResearch.WordTrace tailWord_236286 prefixEnd_236286 121328289928367763638347 := by
  unfold tailWord_236286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1077257302747956410141089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5745372281322434187419141 1077257302747956410141089)
  ·
    refine ⟨807942977060967307605817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1077257302747956410141089 807942977060967307605817)
    ·
      refine ⟨605957232795725480704363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 807942977060967307605817 605957232795725480704363)
      ·
        refine ⟨908935849193588221056545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605957232795725480704363 908935849193588221056545)
        ·
          refine ⟨681701886895191165792409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908935849193588221056545 681701886895191165792409)
          ·
            refine ⟨511276415171393374344307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681701886895191165792409 511276415171393374344307)
            ·
              refine ⟨766914622757090061516461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511276415171393374344307 766914622757090061516461)
              ·
                refine ⟨287592983533908773068673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 766914622757090061516461 287592983533908773068673)
                ·
                  refine ⟨215694737650431579801505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287592983533908773068673 215694737650431579801505)
                  ·
                    refine ⟨161771053237823684851129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215694737650431579801505 161771053237823684851129)
                    ·
                      refine ⟨121328289928367763638347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161771053237823684851129 121328289928367763638347)
                      ·
                        rfl

theorem cell23_236286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_236286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236286 prefixEnd_236286 := by exact prefixLift 236286
  have htrace : WordTrace (prefixWord ++ tailWord_236286) baseStart_236286 baseEnd_236286 := by
    simpa [prefixWord, tailWord_236286, baseEnd_236286] using wordTrace_append hprefix tailTrace_236286
  have hstable : (prefixWord ++ tailWord_236286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236286).length < 2 ^ (prefixWord ++ tailWord_236286).sum := by decide
  have hdescent : baseEnd_236286 < baseStart_236286 := by decide
  rcases family_descends (prefixWord ++ tailWord_236286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236298 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_236298 : Nat := 118140960795 + 236298 * 2 ^ 59
def prefixEnd_236298 : Nat := 4983230072969 + 3 ^ 40 * 236298 * 2
def baseEnd_236298 : Nat := 121334451696221716688291

theorem tailTrace_236298 : CollatzResearch.WordTrace tailWord_236298 prefixEnd_236298 121334451696221716688291 := by
  unfold tailWord_236298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154624024485044332641387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5745664065293451553710365 2154624024485044332641387)
  ·
    refine ⟨3231936036727566498962081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2154624024485044332641387 3231936036727566498962081)
    ·
      refine ⟨2423952027545674874221561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3231936036727566498962081 2423952027545674874221561)
      ·
        refine ⟨1817964020659256155666171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2423952027545674874221561 1817964020659256155666171)
        ·
          refine ⟨2726946030988884233499257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1817964020659256155666171 2726946030988884233499257)
          ·
            refine ⟨2045209523241663175124443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2726946030988884233499257 2045209523241663175124443)
            ·
              refine ⟨3067814284862494762686665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045209523241663175124443 3067814284862494762686665)
              ·
                refine ⟨2300860713646871072014999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3067814284862494762686665 2300860713646871072014999)
                ·
                  refine ⟨3451291070470306608022499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300860713646871072014999 3451291070470306608022499)
                  ·
                    refine ⟨5176936605705459912033749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3451291070470306608022499 5176936605705459912033749)
                    ·
                      refine ⟨121334451696221716688291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5176936605705459912033749 121334451696221716688291)
                      ·
                        rfl

theorem cell23_236298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_236298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236298 prefixEnd_236298 := by exact prefixLift 236298
  have htrace : WordTrace (prefixWord ++ tailWord_236298) baseStart_236298 baseEnd_236298 := by
    simpa [prefixWord, tailWord_236298, baseEnd_236298] using wordTrace_append hprefix tailTrace_236298
  have hstable : (prefixWord ++ tailWord_236298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236298).length < 2 ^ (prefixWord ++ tailWord_236298).sum := by decide
  have hdescent : baseEnd_236298 < baseStart_236298 := by decide
  rcases family_descends (prefixWord ++ tailWord_236298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236325 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_236325 : Nat := 118140960795 + 236325 * 2 ^ 59
def prefixEnd_236325 : Nat := 4983230072969 + 3 ^ 40 * 236325 * 2
def baseEnd_236325 : Nat := 121348315673893111050667

theorem tailTrace_236325 : CollatzResearch.WordTrace tailWord_236325 prefixEnd_236325 121348315673893111050667 := by
  unfold tailWord_236325
  simp only [CollatzResearch.WordTrace]
  refine ⟨8619480868842360941798429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5746320579228240627865619 8619480868842360941798429)
  ·
    refine ⟨3232305325815885353174411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8619480868842360941798429 3232305325815885353174411)
    ·
      refine ⟨4848457988723828029761617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3232305325815885353174411 4848457988723828029761617)
      ·
        refine ⟨3636343491542871022321213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4848457988723828029761617 3636343491542871022321213)
        ·
          refine ⟨1363628809328576633370455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3636343491542871022321213 1363628809328576633370455)
          ·
            refine ⟨2045443213992864950055683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363628809328576633370455 2045443213992864950055683)
            ·
              refine ⟨3068164820989297425083525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045443213992864950055683 3068164820989297425083525)
              ·
                refine ⟨575280903935493267203161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3068164820989297425083525 575280903935493267203161)
                ·
                  refine ⟨431460677951619950402371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575280903935493267203161 431460677951619950402371)
                  ·
                    refine ⟨647191016927429925603557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431460677951619950402371 647191016927429925603557)
                    ·
                      refine ⟨121348315673893111050667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 647191016927429925603557 121348315673893111050667)
                      ·
                        rfl

theorem cell23_236325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_236325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236325 prefixEnd_236325 := by exact prefixLift 236325
  have htrace : WordTrace (prefixWord ++ tailWord_236325) baseStart_236325 baseEnd_236325 := by
    simpa [prefixWord, tailWord_236325, baseEnd_236325] using wordTrace_append hprefix tailTrace_236325
  have hstable : (prefixWord ++ tailWord_236325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236325).length < 2 ^ (prefixWord ++ tailWord_236325).sum := by decide
  have hdescent : baseEnd_236325 < baseStart_236325 := by decide
  rcases family_descends (prefixWord ++ tailWord_236325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236348 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 10]
def baseStart_236348 : Nat := 118140960795 + 236348 * 2 ^ 59
def prefixEnd_236348 : Nat := 4983230072969 + 3 ^ 40 * 236348 * 2
def baseEnd_236348 : Nat := 13484458414327391229229

theorem tailTrace_236348 : CollatzResearch.WordTrace tailWord_236348 prefixEnd_236348 13484458414327391229229 := by
  unfold tailWord_236348
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310159873879517934942849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5746879831839357246590465 4310159873879517934942849)
  ·
    refine ⟨3232619905409638451207137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4310159873879517934942849 3232619905409638451207137)
    ·
      refine ⟨2424464929057228838405353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3232619905409638451207137 2424464929057228838405353)
      ·
        refine ⟨1818348696792921628804015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2424464929057228838405353 1818348696792921628804015)
        ·
          refine ⟨2727523045189382443206023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818348696792921628804015 2727523045189382443206023)
          ·
            refine ⟨4091284567784073664809035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727523045189382443206023 4091284567784073664809035)
            ·
              refine ⟨6136926851676110497213553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4091284567784073664809035 6136926851676110497213553)
              ·
                refine ⟨4602695138757082872910165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6136926851676110497213553 4602695138757082872910165)
                ·
                  refine ⟨13484458414327391229229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 4602695138757082872910165 13484458414327391229229)
                  ·
                    rfl

theorem cell23_236348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_236348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236348 prefixEnd_236348 := by exact prefixLift 236348
  have htrace : WordTrace (prefixWord ++ tailWord_236348) baseStart_236348 baseEnd_236348 := by
    simpa [prefixWord, tailWord_236348, baseEnd_236348] using wordTrace_append hprefix tailTrace_236348
  have hstable : (prefixWord ++ tailWord_236348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236348).length < 2 ^ (prefixWord ++ tailWord_236348).sum := by decide
  have hdescent : baseEnd_236348 < baseStart_236348 := by decide
  rcases family_descends (prefixWord ++ tailWord_236348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236356 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_236356 : Nat := 118140960795 + 236356 * 2 ^ 59
def prefixEnd_236356 : Nat := 4983230072969 + 3 ^ 40 * 236356 * 2
def baseEnd_236356 : Nat := 40454744524727496587675

theorem tailTrace_236356 : CollatzResearch.WordTrace tailWord_236356 prefixEnd_236356 40454744524727496587675 := by
  unfold tailWord_236356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310305765865026618088461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5747074354486702157451281 4310305765865026618088461)
  ·
    refine ⟨1616364662199384981783173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4310305765865026618088461 1616364662199384981783173)
    ·
      refine ⟨303068374162384684084345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1616364662199384981783173 303068374162384684084345)
      ·
        refine ⟨227301280621788513063259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303068374162384684084345 227301280621788513063259)
        ·
          refine ⟨340951920932682769594889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227301280621788513063259 340951920932682769594889)
          ·
            refine ⟨255713940699512077196167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340951920932682769594889 255713940699512077196167)
            ·
              refine ⟨383570911049268115794251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255713940699512077196167 383570911049268115794251)
              ·
                refine ⟨575356366573902173691377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383570911049268115794251 575356366573902173691377)
                ·
                  refine ⟨431517274930426630268533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575356366573902173691377 431517274930426630268533)
                  ·
                    refine ⟨40454744524727496587675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 431517274930426630268533 40454744524727496587675)
                    ·
                      rfl

theorem cell23_236356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_236356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236356 prefixEnd_236356 := by exact prefixLift 236356
  have htrace : WordTrace (prefixWord ++ tailWord_236356) baseStart_236356 baseEnd_236356 := by
    simpa [prefixWord, tailWord_236356, baseEnd_236356] using wordTrace_append hprefix tailTrace_236356
  have hstable : (prefixWord ++ tailWord_236356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236356).length < 2 ^ (prefixWord ++ tailWord_236356).sum := by decide
  have hdescent : baseEnd_236356 < baseStart_236356 := by decide
  rcases family_descends (prefixWord ++ tailWord_236356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236402 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 1, 5, 2]
def baseStart_236402 : Nat := 118140960795 + 236402 * 2 ^ 59
def prefixEnd_236402 : Nat := 4983230072969 + 3 ^ 40 * 236402 * 2
def baseEnd_236402 : Nat := 121387853684289309787813

theorem tailTrace_236402 : CollatzResearch.WordTrace tailWord_236402 prefixEnd_236402 121387853684289309787813 := by
  unfold tailWord_236402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155572322390850773087865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5748192859708935394900973 2155572322390850773087865)
  ·
    refine ⟨1616679241793138079815899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2155572322390850773087865 1616679241793138079815899)
    ·
      refine ⟨2425018862689707119723849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1616679241793138079815899 2425018862689707119723849)
      ·
        refine ⟨1818764147017280339792887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2425018862689707119723849 1818764147017280339792887)
        ·
          refine ⟨2728146220525920509689331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818764147017280339792887 2728146220525920509689331)
          ·
            refine ⟨4092219330788880764533997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728146220525920509689331 4092219330788880764533997)
            ·
              refine ⟨1534582249045830286700249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4092219330788880764533997 1534582249045830286700249)
              ·
                refine ⟨1150936686784372715025187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534582249045830286700249 1150936686784372715025187)
                ·
                  refine ⟨1726405030176559072537781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150936686784372715025187 1726405030176559072537781)
                  ·
                    refine ⟨161850471579052413050417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1726405030176559072537781 161850471579052413050417)
                    ·
                      refine ⟨121387853684289309787813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161850471579052413050417 121387853684289309787813)
                      ·
                        rfl

theorem cell23_236402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_236402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236402 prefixEnd_236402 := by exact prefixLift 236402
  have htrace : WordTrace (prefixWord ++ tailWord_236402) baseStart_236402 baseEnd_236402 := by
    simpa [prefixWord, tailWord_236402, baseEnd_236402] using wordTrace_append hprefix tailTrace_236402
  have hstable : (prefixWord ++ tailWord_236402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236402).length < 2 ^ (prefixWord ++ tailWord_236402).sum := by decide
  have hdescent : baseEnd_236402 < baseStart_236402 := by decide
  rcases family_descends (prefixWord ++ tailWord_236402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236415 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 4]
def baseStart_236415 : Nat := 118140960795 + 236415 * 2 ^ 59
def prefixEnd_236415 : Nat := 4983230072969 + 3 ^ 40 * 236415 * 2
def baseEnd_236415 : Nat := 121394528932797758925253

theorem tailTrace_236415 : CollatzResearch.WordTrace tailWord_236415 prefixEnd_236415 121394528932797758925253 := by
  unfold tailWord_236415
  simp only [CollatzResearch.WordTrace]
  refine ⟨8622763438516306312574699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5748508959010870875049799 8622763438516306312574699)
  ·
    refine ⟨12934145157774459468862049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8622763438516306312574699 12934145157774459468862049)
    ·
      refine ⟨9700608868330844601646537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12934145157774459468862049 9700608868330844601646537)
      ·
        refine ⟨7275456651248133451234903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9700608868330844601646537 7275456651248133451234903)
        ·
          refine ⟨10913184976872200176852355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7275456651248133451234903 10913184976872200176852355)
          ·
            refine ⟨16369777465308300265278533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10913184976872200176852355 16369777465308300265278533)
            ·
              refine ⟨3069333274745306299739725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16369777465308300265278533 3069333274745306299739725)
              ·
                refine ⟨1150999978029489862402397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3069333274745306299739725 1150999978029489862402397)
                ·
                  refine ⟨431624991761058698400899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150999978029489862402397 431624991761058698400899)
                  ·
                    refine ⟨647437487641588047601349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431624991761058698400899 647437487641588047601349)
                    ·
                      refine ⟨121394528932797758925253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 647437487641588047601349 121394528932797758925253)
                      ·
                        rfl

theorem cell23_236415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_236415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236415 prefixEnd_236415 := by exact prefixLift 236415
  have htrace : WordTrace (prefixWord ++ tailWord_236415) baseStart_236415 baseEnd_236415 := by
    simpa [prefixWord, tailWord_236415, baseEnd_236415] using wordTrace_append hprefix tailTrace_236415
  have hstable : (prefixWord ++ tailWord_236415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236415).length < 2 ^ (prefixWord ++ tailWord_236415).sum := by decide
  have hdescent : baseEnd_236415 < baseStart_236415 := by decide
  rcases family_descends (prefixWord ++ tailWord_236415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236445 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_236445 : Nat := 118140960795 + 236445 * 2 ^ 59
def prefixEnd_236445 : Nat := 4983230072969 + 3 ^ 40 * 236445 * 2
def baseEnd_236445 : Nat := 121409933352432641550115

theorem tailTrace_236445 : CollatzResearch.WordTrace tailWord_236445 prefixEnd_236445 121409933352432641550115 := by
  unfold tailWord_236445
  simp only [CollatzResearch.WordTrace]
  refine ⟨8623857628407621436166789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5749238418938414290777859 8623857628407621436166789)
  ·
    refine ⟨1616973305326429019281273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8623857628407621436166789 1616973305326429019281273)
    ·
      refine ⟨1212729978994821764460955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1616973305326429019281273 1212729978994821764460955)
      ·
        refine ⟨1819094968492232646691433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212729978994821764460955 1819094968492232646691433)
        ·
          refine ⟨1364321226369174485018575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1819094968492232646691433 1364321226369174485018575)
          ·
            refine ⟨2046481839553761727527863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364321226369174485018575 2046481839553761727527863)
            ·
              refine ⟨3069722759330642591291795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046481839553761727527863 3069722759330642591291795)
              ·
                refine ⟨4604584138995963886937693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069722759330642591291795 4604584138995963886937693)
                ·
                  refine ⟨1726719052123486457601635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4604584138995963886937693 1726719052123486457601635)
                  ·
                    refine ⟨2590078578185229686402453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1726719052123486457601635 2590078578185229686402453)
                    ·
                      refine ⟨121409933352432641550115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2590078578185229686402453 121409933352432641550115)
                      ·
                        rfl

theorem cell23_236445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_236445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236445 prefixEnd_236445 := by exact prefixLift 236445
  have htrace : WordTrace (prefixWord ++ tailWord_236445) baseStart_236445 baseEnd_236445 := by
    simpa [prefixWord, tailWord_236445, baseEnd_236445] using wordTrace_append hprefix tailTrace_236445
  have hstable : (prefixWord ++ tailWord_236445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236445).length < 2 ^ (prefixWord ++ tailWord_236445).sum := by decide
  have hdescent : baseEnd_236445 < baseStart_236445 := by decide
  rcases family_descends (prefixWord ++ tailWord_236445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236452 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_236452 : Nat := 118140960795 + 236452 * 2 ^ 59
def prefixEnd_236452 : Nat := 4983230072969 + 3 ^ 40 * 236452 * 2
def baseEnd_236452 : Nat := 121413527717014114162583

theorem tailTrace_236452 : CollatzResearch.WordTrace tailWord_236452 prefixEnd_236452 121413527717014114162583 := by
  unfold tailWord_236452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4312056469691130815835805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5749408626254841087781073 4312056469691130815835805)
  ·
    refine ⟨1617021176134174055938427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4312056469691130815835805 1617021176134174055938427)
    ·
      refine ⟨2425531764201261083907641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1617021176134174055938427 2425531764201261083907641)
      ·
        refine ⟨1819148823150945812930731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2425531764201261083907641 1819148823150945812930731)
        ·
          refine ⟨2728723234726418719396097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819148823150945812930731 2728723234726418719396097)
          ·
            refine ⟨2046542426044814039547073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728723234726418719396097 2046542426044814039547073)
            ·
              refine ⟨1534906819533610529660305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046542426044814039547073 1534906819533610529660305)
              ·
                refine ⟨1151180114650207897245229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534906819533610529660305 1151180114650207897245229)
                ·
                  refine ⟨431692542993827961466961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151180114650207897245229 431692542993827961466961)
                  ·
                    refine ⟨323769407245370971100221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 431692542993827961466961 323769407245370971100221)
                    ·
                      refine ⟨121413527717014114162583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 323769407245370971100221 121413527717014114162583)
                      ·
                        rfl

theorem cell23_236452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_236452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236452 prefixEnd_236452 := by exact prefixLift 236452
  have htrace : WordTrace (prefixWord ++ tailWord_236452) baseStart_236452 baseEnd_236452 := by
    simpa [prefixWord, tailWord_236452, baseEnd_236452] using wordTrace_append hprefix tailTrace_236452
  have hstable : (prefixWord ++ tailWord_236452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236452).length < 2 ^ (prefixWord ++ tailWord_236452).sum := by decide
  have hdescent : baseEnd_236452 < baseStart_236452 := by decide
  rcases family_descends (prefixWord ++ tailWord_236452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236500 : List Nat := [2, 4, 1, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_236500 : Nat := 118140960795 + 236500 * 2 ^ 59
def prefixEnd_236500 : Nat := 4983230072969 + 3 ^ 40 * 236500 * 2
def baseEnd_236500 : Nat := 121438174788429926362363

theorem tailTrace_236500 : CollatzResearch.WordTrace tailWord_236500 prefixEnd_236500 121438174788429926362363 := by
  unfold tailWord_236500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4312931821604182914709477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5750575762138910552945969 4312931821604182914709477)
  ·
    refine ⟨808674716550784296508027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4312931821604182914709477 808674716550784296508027)
    ·
      refine ⟨1213012074826176444762041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 808674716550784296508027 1213012074826176444762041)
      ·
        refine ⟨909759056119632333571531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1213012074826176444762041 909759056119632333571531)
        ·
          refine ⟨1364638584179448500357297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909759056119632333571531 1364638584179448500357297)
          ·
            refine ⟨1023478938134586375267973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364638584179448500357297 1023478938134586375267973)
            ·
              refine ⟨191902300900234945362745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1023478938134586375267973 191902300900234945362745)
              ·
                refine ⟨143926725675176209022059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191902300900234945362745 143926725675176209022059)
                ·
                  refine ⟨215890088512764313533089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143926725675176209022059 215890088512764313533089)
                  ·
                    refine ⟨161917566384573235149817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215890088512764313533089 161917566384573235149817)
                    ·
                      refine ⟨121438174788429926362363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161917566384573235149817 121438174788429926362363)
                      ·
                        rfl

theorem cell23_236500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_236500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236500 prefixEnd_236500 := by exact prefixLift 236500
  have htrace : WordTrace (prefixWord ++ tailWord_236500) baseStart_236500 baseEnd_236500 := by
    simpa [prefixWord, tailWord_236500, baseEnd_236500] using wordTrace_append hprefix tailTrace_236500
  have hstable : (prefixWord ++ tailWord_236500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236500).length < 2 ^ (prefixWord ++ tailWord_236500).sum := by decide
  have hdescent : baseEnd_236500 < baseStart_236500 := by decide
  rcases family_descends (prefixWord ++ tailWord_236500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236539 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 4, 2, 2]
def baseStart_236539 : Nat := 118140960795 + 236539 * 2 ^ 59
def prefixEnd_236539 : Nat := 4983230072969 + 3 ^ 40 * 236539 * 2
def baseEnd_236539 : Nat := 121458200533955273774683

theorem tailTrace_236539 : CollatzResearch.WordTrace tailWord_236539 prefixEnd_236539 121458200533955273774683 := by
  unfold tailWord_236539
  simp only [CollatzResearch.WordTrace]
  refine ⟨8627286090067075490088671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5751524060044716993392447 8627286090067075490088671)
  ·
    refine ⟨12940929135100613235133007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8627286090067075490088671 12940929135100613235133007)
    ·
      refine ⟨19411393702650919852699511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12940929135100613235133007 19411393702650919852699511)
      ·
        refine ⟨29117090553976379779049267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19411393702650919852699511 29117090553976379779049267)
        ·
          refine ⟨43675635830964569668573901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29117090553976379779049267 43675635830964569668573901)
          ·
            refine ⟨16378363436611713625715213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43675635830964569668573901 16378363436611713625715213)
            ·
              refine ⟨6141886288729392609643205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16378363436611713625715213 6141886288729392609643205)
              ·
                refine ⟨1151603679136761114308101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6141886288729392609643205 1151603679136761114308101)
                ·
                  refine ⟨215925689838142708932769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151603679136761114308101 215925689838142708932769)
                  ·
                    refine ⟨161944267378607031699577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215925689838142708932769 161944267378607031699577)
                    ·
                      refine ⟨121458200533955273774683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161944267378607031699577 121458200533955273774683)
                      ·
                        rfl

theorem cell23_236539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 2, 2].length) (baseStart_236539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236539 prefixEnd_236539 := by exact prefixLift 236539
  have htrace : WordTrace (prefixWord ++ tailWord_236539) baseStart_236539 baseEnd_236539 := by
    simpa [prefixWord, tailWord_236539, baseEnd_236539] using wordTrace_append hprefix tailTrace_236539
  have hstable : (prefixWord ++ tailWord_236539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236539).length < 2 ^ (prefixWord ++ tailWord_236539).sum := by decide
  have hdescent : baseEnd_236539 < baseStart_236539 := by decide
  rcases family_descends (prefixWord ++ tailWord_236539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236552 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_236552 : Nat := 118140960795 + 236552 * 2 ^ 59
def prefixEnd_236552 : Nat := 4983230072969 + 3 ^ 40 * 236552 * 2
def baseEnd_236552 : Nat := 121464875782463722912123

theorem tailTrace_236552 : CollatzResearch.WordTrace tailWord_236552 prefixEnd_236552 121464875782463722912123 := by
  unfold tailWord_236552
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313880119509989355155955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5751840159346652473541273 4313880119509989355155955)
  ·
    refine ⟨6470820179264984032733933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4313880119509989355155955 6470820179264984032733933)
    ·
      refine ⟨2426557567224369012275225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6470820179264984032733933 2426557567224369012275225)
      ·
        refine ⟨1819918175418276759206419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2426557567224369012275225 1819918175418276759206419)
        ·
          refine ⟨2729877263127415138809629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819918175418276759206419 2729877263127415138809629)
          ·
            refine ⟨1023703973672780677053611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2729877263127415138809629 1023703973672780677053611)
            ·
              refine ⟨1535555960509171015580417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023703973672780677053611 1535555960509171015580417)
              ·
                refine ⟨1151666970381878261685313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535555960509171015580417 1151666970381878261685313)
                ·
                  refine ⟨863750227786408696263985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1151666970381878261685313 863750227786408696263985)
                  ·
                    refine ⟨647812670839806522197989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 863750227786408696263985 647812670839806522197989)
                    ·
                      refine ⟨121464875782463722912123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 647812670839806522197989 121464875782463722912123)
                      ·
                        rfl

theorem cell23_236552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_236552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236552 prefixEnd_236552 := by exact prefixLift 236552
  have htrace : WordTrace (prefixWord ++ tailWord_236552) baseStart_236552 baseEnd_236552 := by
    simpa [prefixWord, tailWord_236552, baseEnd_236552] using wordTrace_append hprefix tailTrace_236552
  have hstable : (prefixWord ++ tailWord_236552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236552).length < 2 ^ (prefixWord ++ tailWord_236552).sum := by decide
  have hdescent : baseEnd_236552 < baseStart_236552 := by decide
  rcases family_descends (prefixWord ++ tailWord_236552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236556 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 4, 2, 2]
def baseStart_236556 : Nat := 118140960795 + 236556 * 2 ^ 59
def prefixEnd_236556 : Nat := 4983230072969 + 3 ^ 40 * 236556 * 2
def baseEnd_236556 : Nat := 121466929705081707262105

theorem tailTrace_236556 : CollatzResearch.WordTrace tailWord_236556 prefixEnd_236556 121466929705081707262105 := by
  unfold tailWord_236556
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313953065502743696728761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5751937420670324928971681 4313953065502743696728761)
  ·
    refine ⟨3235464799127057772546571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4313953065502743696728761 3235464799127057772546571)
    ·
      refine ⟨4853197198690586658819857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3235464799127057772546571 4853197198690586658819857)
      ·
        refine ⟨3639897899017939994114893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4853197198690586658819857 3639897899017939994114893)
        ·
          refine ⟨1364961712131727497793085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3639897899017939994114893 1364961712131727497793085)
          ·
            refine ⟨511860642049397811672407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1364961712131727497793085 511860642049397811672407)
            ·
              refine ⟨767790963074096717508611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511860642049397811672407 767790963074096717508611)
              ·
                refine ⟨1151686444611145076262917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767790963074096717508611 1151686444611145076262917)
                ·
                  refine ⟨215941208364589701799297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151686444611145076262917 215941208364589701799297)
                  ·
                    refine ⟨161955906273442276349473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215941208364589701799297 161955906273442276349473)
                    ·
                      refine ⟨121466929705081707262105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161955906273442276349473 121466929705081707262105)
                      ·
                        rfl

theorem cell23_236556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_236556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236556 prefixEnd_236556 := by exact prefixLift 236556
  have htrace : WordTrace (prefixWord ++ tailWord_236556) baseStart_236556 baseEnd_236556 := by
    simpa [prefixWord, tailWord_236556, baseEnd_236556] using wordTrace_append hprefix tailTrace_236556
  have hstable : (prefixWord ++ tailWord_236556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236556).length < 2 ^ (prefixWord ++ tailWord_236556).sum := by decide
  have hdescent : baseEnd_236556 < baseStart_236556 := by decide
  rcases family_descends (prefixWord ++ tailWord_236556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236573 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_236573 : Nat := 118140960795 + 236573 * 2 ^ 59
def prefixEnd_236573 : Nat := 4983230072969 + 3 ^ 40 * 236573 * 2
def baseEnd_236573 : Nat := 121475658876208140749527

theorem tailTrace_236573 : CollatzResearch.WordTrace tailWord_236573 prefixEnd_236573 121475658876208140749527 := by
  unfold tailWord_236573
  simp only [CollatzResearch.WordTrace]
  refine ⟨8628526171943899296826373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5752350781295932864550915 8628526171943899296826373)
  ·
    refine ⟨1617848657239481118154945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8628526171943899296826373 1617848657239481118154945)
    ·
      refine ⟨1213386492929610838616209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1617848657239481118154945 1213386492929610838616209)
      ·
        refine ⟨910039869697208128962157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1213386492929610838616209 910039869697208128962157)
        ·
          refine ⟨341264951136453048360809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 910039869697208128962157 341264951136453048360809)
          ·
            refine ⟨255948713352339786270607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341264951136453048360809 255948713352339786270607)
            ·
              refine ⟨383923070028509679405911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255948713352339786270607 383923070028509679405911)
              ·
                refine ⟨575884605042764519108867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383923070028509679405911 575884605042764519108867)
                ·
                  refine ⟨863826907564146778663301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575884605042764519108867 863826907564146778663301)
                  ·
                    refine ⟨161967545168277520999369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863826907564146778663301 161967545168277520999369)
                    ·
                      refine ⟨121475658876208140749527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 161967545168277520999369 121475658876208140749527)
                      ·
                        rfl

theorem cell23_236573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_236573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236573 prefixEnd_236573 := by exact prefixLift 236573
  have htrace : WordTrace (prefixWord ++ tailWord_236573) baseStart_236573 baseEnd_236573 := by
    simpa [prefixWord, tailWord_236573, baseEnd_236573] using wordTrace_append hprefix tailTrace_236573
  have hstable : (prefixWord ++ tailWord_236573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236573).length < 2 ^ (prefixWord ++ tailWord_236573).sum := by decide
  have hdescent : baseEnd_236573 < baseStart_236573 := by decide
  rcases family_descends (prefixWord ++ tailWord_236573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236592 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 2, 5]
def baseStart_236592 : Nat := 118140960795 + 236592 * 2 ^ 59
def prefixEnd_236592 : Nat := 4983230072969 + 3 ^ 40 * 236592 * 2
def baseEnd_236592 : Nat := 40495138336214522137313

theorem tailTrace_236592 : CollatzResearch.WordTrace tailWord_236592 prefixEnd_236592 40495138336214522137313 := by
  unfold tailWord_236592
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314609579437532770884015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5752812772583377027845353 4314609579437532770884015)
  ·
    refine ⟨6471914369156299156326023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4314609579437532770884015 6471914369156299156326023)
    ·
      refine ⟨9707871553734448734489035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6471914369156299156326023 9707871553734448734489035)
      ·
        refine ⟨14561807330601673101733553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9707871553734448734489035 14561807330601673101733553)
        ·
          refine ⟨10921355497951254826300165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14561807330601673101733553 10921355497951254826300165)
          ·
            refine ⟨2047754155865860279931281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10921355497951254826300165 2047754155865860279931281)
            ·
              refine ⟨1535815616899395209948461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047754155865860279931281 1535815616899395209948461)
              ·
                refine ⟨575930856337273203730673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1535815616899395209948461 575930856337273203730673)
                ·
                  refine ⟨431948142252954902798005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575930856337273203730673 431948142252954902798005)
                  ·
                    refine ⟨40495138336214522137313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 431948142252954902798005 40495138336214522137313)
                    ·
                      rfl

theorem cell23_236592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_236592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236592 prefixEnd_236592 := by exact prefixLift 236592
  have htrace : WordTrace (prefixWord ++ tailWord_236592) baseStart_236592 baseEnd_236592 := by
    simpa [prefixWord, tailWord_236592, baseEnd_236592] using wordTrace_append hprefix tailTrace_236592
  have hstable : (prefixWord ++ tailWord_236592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236592).length < 2 ^ (prefixWord ++ tailWord_236592).sum := by decide
  have hdescent : baseEnd_236592 < baseStart_236592 := by decide
  rcases family_descends (prefixWord ++ tailWord_236592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236629 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 1, 6, 2]
def baseStart_236629 : Nat := 118140960795 + 236629 * 2 ^ 59
def prefixEnd_236629 : Nat := 4983230072969 + 3 ^ 40 * 236629 * 2
def baseEnd_236629 : Nat := 121504413792859921649269

theorem tailTrace_236629 : CollatzResearch.WordTrace tailWord_236629 prefixEnd_236629 121504413792859921649269 := by
  unfold tailWord_236629
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630568659741020860864941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5753712439827347240576627 8630568659741020860864941)
  ·
    refine ⟨3236463247402882822824353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8630568659741020860864941 3236463247402882822824353)
    ·
      refine ⟨2427347435552162117118265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3236463247402882822824353 2427347435552162117118265)
      ·
        refine ⟨1820510576664121587838699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2427347435552162117118265 1820510576664121587838699)
        ·
          refine ⟨2730765864996182381758049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820510576664121587838699 2730765864996182381758049)
          ·
            refine ⟨2048074398747136786318537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2730765864996182381758049 2048074398747136786318537)
            ·
              refine ⟨1536055799060352589738903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048074398747136786318537 1536055799060352589738903)
              ·
                refine ⟨2304083698590528884608355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536055799060352589738903 2304083698590528884608355)
                ·
                  refine ⟨3456125547885793326912533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304083698590528884608355 3456125547885793326912533)
                  ·
                    refine ⟨162005885057146562199025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3456125547885793326912533 162005885057146562199025)
                    ·
                      refine ⟨121504413792859921649269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162005885057146562199025 121504413792859921649269)
                      ·
                        rfl

theorem cell23_236629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_236629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236629 prefixEnd_236629 := by exact prefixLift 236629
  have htrace : WordTrace (prefixWord ++ tailWord_236629) baseStart_236629 baseEnd_236629 := by
    simpa [prefixWord, tailWord_236629, baseEnd_236629] using wordTrace_append hprefix tailTrace_236629
  have hstable : (prefixWord ++ tailWord_236629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236629).length < 2 ^ (prefixWord ++ tailWord_236629).sum := by decide
  have hdescent : baseEnd_236629 < baseStart_236629 := by decide
  rcases family_descends (prefixWord ++ tailWord_236629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236649 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 2, 2, 3]
def baseStart_236649 : Nat := 118140960795 + 236649 * 2 ^ 59
def prefixEnd_236649 : Nat := 4983230072969 + 3 ^ 40 * 236649 * 2
def baseEnd_236649 : Nat := 121514683405949843399177

theorem tailTrace_236649 : CollatzResearch.WordTrace tailWord_236649 prefixEnd_236649 121514683405949843399177 := by
  unfold tailWord_236649
  simp only [CollatzResearch.WordTrace]
  refine ⟨8631298119668564276593001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5754198746445709517728667 8631298119668564276593001)
  ·
    refine ⟨6473473589751423207444751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8631298119668564276593001 6473473589751423207444751)
    ·
      refine ⟨9710210384627134811167127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6473473589751423207444751 9710210384627134811167127)
      ·
        refine ⟨14565315576940702216750691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9710210384627134811167127 14565315576940702216750691)
        ·
          refine ⟨21847973365411053325126037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14565315576940702216750691 21847973365411053325126037)
          ·
            refine ⟨1024123751503643124615283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21847973365411053325126037 1024123751503643124615283)
            ·
              refine ⟨1536185627255464686922925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024123751503643124615283 1536185627255464686922925)
              ·
                refine ⟨576069610220799257596097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1536185627255464686922925 576069610220799257596097)
                ·
                  refine ⟨432052207665599443197073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576069610220799257596097 432052207665599443197073)
                  ·
                    refine ⟨324039155749199582397805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 432052207665599443197073 324039155749199582397805)
                    ·
                      refine ⟨121514683405949843399177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 324039155749199582397805 121514683405949843399177)
                      ·
                        rfl

theorem cell23_236649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2, 3].length) (baseStart_236649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236649 prefixEnd_236649 := by exact prefixLift 236649
  have htrace : WordTrace (prefixWord ++ tailWord_236649) baseStart_236649 baseEnd_236649 := by
    simpa [prefixWord, tailWord_236649, baseEnd_236649] using wordTrace_append hprefix tailTrace_236649
  have hstable : (prefixWord ++ tailWord_236649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236649).length < 2 ^ (prefixWord ++ tailWord_236649).sum := by decide
  have hdescent : baseEnd_236649 < baseStart_236649 := by decide
  rcases family_descends (prefixWord ++ tailWord_236649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236656 : List Nat := [2, 1, 1, 1, 5, 1, 2, 5, 1, 4]
def baseStart_236656 : Nat := 118140960795 + 236656 * 2 ^ 59
def prefixEnd_236656 : Nat := 4983230072969 + 3 ^ 40 * 236656 * 2
def baseEnd_236656 : Nat := 40506092590177105337215

theorem tailTrace_236656 : CollatzResearch.WordTrace tailWord_236656 prefixEnd_236656 40506092590177105337215 := by
  unfold tailWord_236656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315776715321602236048911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5754368953762136314731881 4315776715321602236048911)
  ·
    refine ⟨6473665072982403354073367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4315776715321602236048911 6473665072982403354073367)
    ·
      refine ⟨9710497609473605031110051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6473665072982403354073367 9710497609473605031110051)
      ·
        refine ⟨14565746414210407546665077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9710497609473605031110051 14565746414210407546665077)
        ·
          refine ⟨1365538726332225707499851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14565746414210407546665077 1365538726332225707499851)
          ·
            refine ⟨2048308089498338561249777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365538726332225707499851 2048308089498338561249777)
            ·
              refine ⟨1536231067123753920937333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048308089498338561249777 1536231067123753920937333)
              ·
                refine ⟨144021662542851930087875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1536231067123753920937333 144021662542851930087875)
                ·
                  refine ⟨216032493814277895131813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144021662542851930087875 216032493814277895131813)
                  ·
                    refine ⟨40506092590177105337215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 216032493814277895131813 40506092590177105337215)
                    ·
                      rfl

theorem cell23_236656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 1, 4].length) (baseStart_236656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236656 prefixEnd_236656 := by exact prefixLift 236656
  have htrace : WordTrace (prefixWord ++ tailWord_236656) baseStart_236656 baseEnd_236656 := by
    simpa [prefixWord, tailWord_236656, baseEnd_236656] using wordTrace_append hprefix tailTrace_236656
  have hstable : (prefixWord ++ tailWord_236656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236656).length < 2 ^ (prefixWord ++ tailWord_236656).sum := by decide
  have hdescent : baseEnd_236656 < baseStart_236656 := by decide
  rcases family_descends (prefixWord ++ tailWord_236656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236669 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 6]
def baseStart_236669 : Nat := 118140960795 + 236669 * 2 ^ 59
def prefixEnd_236669 : Nat := 4983230072969 + 3 ^ 40 * 236669 * 2
def baseEnd_236669 : Nat := 13502772557671085016565

theorem tailTrace_236669 : CollatzResearch.WordTrace tailWord_236669 prefixEnd_236669 13502772557671085016565 := by
  unfold tailWord_236669
  simp only [CollatzResearch.WordTrace]
  refine ⟨8632027579596107692321061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5754685053064071794880707 8632027579596107692321061)
  ·
    refine ⟨1618505171174270192310199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8632027579596107692321061 1618505171174270192310199)
    ·
      refine ⟨2427757756761405288465299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1618505171174270192310199 2427757756761405288465299)
      ·
        refine ⟨3641636635142107932697949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427757756761405288465299 3641636635142107932697949)
        ·
          refine ⟨1365613738178290474761731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3641636635142107932697949 1365613738178290474761731)
          ·
            refine ⟨2048420607267435712142597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365613738178290474761731 2048420607267435712142597)
            ·
              refine ⟨384078863862644196026737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2048420607267435712142597 384078863862644196026737)
              ·
                refine ⟨288059147896983147020053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384078863862644196026737 288059147896983147020053)
                ·
                  refine ⟨13502772557671085016565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 288059147896983147020053 13502772557671085016565)
                  ·
                    rfl

theorem cell23_236669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_236669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236669 prefixEnd_236669 := by exact prefixLift 236669
  have htrace : WordTrace (prefixWord ++ tailWord_236669) baseStart_236669 baseEnd_236669 := by
    simpa [prefixWord, tailWord_236669, baseEnd_236669] using wordTrace_append hprefix tailTrace_236669
  have hstable : (prefixWord ++ tailWord_236669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236669).length < 2 ^ (prefixWord ++ tailWord_236669).sum := by decide
  have hdescent : baseEnd_236669 < baseStart_236669 := by decide
  rcases family_descends (prefixWord ++ tailWord_236669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236673 : List Nat := [1, 2, 4, 2, 2, 2, 1, 4, 1, 4]
def baseStart_236673 : Nat := 118140960795 + 236673 * 2 ^ 59
def prefixEnd_236673 : Nat := 4983230072969 + 3 ^ 40 * 236673 * 2
def baseEnd_236673 : Nat := 40509002313885916499689

theorem tailTrace_236673 : CollatzResearch.WordTrace tailWord_236673 prefixEnd_236673 40509002313885916499689 := by
  unfold tailWord_236673
  simp only [CollatzResearch.WordTrace]
  refine ⟨8632173471581616375466673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5754782314387744250311115 8632173471581616375466673)
  ·
    refine ⟨6474130103686212281600005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8632173471581616375466673 6474130103686212281600005)
    ·
      refine ⟨1213899394441164802800001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6474130103686212281600005 1213899394441164802800001)
      ·
        refine ⟨910424545830873602100001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1213899394441164802800001 910424545830873602100001)
        ·
          refine ⟨682818409373155201575001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910424545830873602100001 682818409373155201575001)
          ·
            refine ⟨512113807029866401181251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682818409373155201575001 512113807029866401181251)
            ·
              refine ⟨768170710544799601771877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512113807029866401181251 768170710544799601771877)
              ·
                refine ⟨144032008227149925332227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768170710544799601771877 144032008227149925332227)
                ·
                  refine ⟨216048012340724887998341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144032008227149925332227 216048012340724887998341)
                  ·
                    refine ⟨40509002313885916499689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 216048012340724887998341 40509002313885916499689)
                    ·
                      rfl

theorem cell23_236673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_236673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236673 prefixEnd_236673 := by exact prefixLift 236673
  have htrace : WordTrace (prefixWord ++ tailWord_236673) baseStart_236673 baseEnd_236673 := by
    simpa [prefixWord, tailWord_236673, baseEnd_236673] using wordTrace_append hprefix tailTrace_236673
  have hstable : (prefixWord ++ tailWord_236673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236673).length < 2 ^ (prefixWord ++ tailWord_236673).sum := by decide
  have hdescent : baseEnd_236673 < baseStart_236673 := by decide
  rcases family_descends (prefixWord ++ tailWord_236673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236696 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 5, 1, 3]
def baseStart_236696 : Nat := 118140960795 + 236696 * 2 ^ 59
def prefixEnd_236696 : Nat := 4983230072969 + 3 ^ 40 * 236696 * 2
def baseEnd_236696 : Nat := 121538816996711159511461

theorem tailTrace_236696 : CollatzResearch.WordTrace tailWord_236696 prefixEnd_236696 121538816996711159511461 := by
  unfold tailWord_236696
  simp only [CollatzResearch.WordTrace]
  refine ⟨4316506175249145651776971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5755341566998860869035961 4316506175249145651776971)
  ·
    refine ⟨6474759262873718477665457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4316506175249145651776971 6474759262873718477665457)
    ·
      refine ⟨4856069447155288858249093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6474759262873718477665457 4856069447155288858249093)
      ·
        refine ⟨910513021341616660921705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4856069447155288858249093 910513021341616660921705)
        ·
          refine ⟨682884766006212495691279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910513021341616660921705 682884766006212495691279)
          ·
            refine ⟨1024327149009318743536919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682884766006212495691279 1024327149009318743536919)
            ·
              refine ⟨1536490723513978115305379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024327149009318743536919 1536490723513978115305379)
              ·
                refine ⟨2304736085270967172958069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536490723513978115305379 2304736085270967172958069)
                ·
                  refine ⟨216069007994153172464819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2304736085270967172958069 216069007994153172464819)
                  ·
                    refine ⟨324103511991229758697229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216069007994153172464819 324103511991229758697229)
                    ·
                      refine ⟨121538816996711159511461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 324103511991229758697229 121538816996711159511461)
                      ·
                        rfl

theorem cell23_236696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_236696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236696 prefixEnd_236696 := by exact prefixLift 236696
  have htrace : WordTrace (prefixWord ++ tailWord_236696) baseStart_236696 baseEnd_236696 := by
    simpa [prefixWord, tailWord_236696, baseEnd_236696] using wordTrace_append hprefix tailTrace_236696
  have hstable : (prefixWord ++ tailWord_236696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236696).length < 2 ^ (prefixWord ++ tailWord_236696).sum := by decide
  have hdescent : baseEnd_236696 < baseStart_236696 := by decide
  rcases family_descends (prefixWord ++ tailWord_236696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236739 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 3]
def baseStart_236739 : Nat := 118140960795 + 236739 * 2 ^ 59
def prefixEnd_236739 : Nat := 4983230072969 + 3 ^ 40 * 236739 * 2
def baseEnd_236739 : Nat := 121560896664854491273763

theorem tailTrace_236739 : CollatzResearch.WordTrace tailWord_236739 prefixEnd_236739 121560896664854491273763 := by
  unfold tailWord_236739
  simp only [CollatzResearch.WordTrace]
  refine ⟨8634580689342509647369271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5756387126228339764912847 8634580689342509647369271)
  ·
    refine ⟨12951871034013764471053907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8634580689342509647369271 12951871034013764471053907)
    ·
      refine ⟨19427806551020646706580861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12951871034013764471053907 19427806551020646706580861)
      ·
        refine ⟨7285427456632742514967823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19427806551020646706580861 7285427456632742514967823)
        ·
          refine ⟨10928141184949113772451735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285427456632742514967823 10928141184949113772451735)
          ·
            refine ⟨16392211777423670658677603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10928141184949113772451735 16392211777423670658677603)
            ·
              refine ⟨24588317666135505988016405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16392211777423670658677603 24588317666135505988016405)
              ·
                refine ⟨1152577390600101843188269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24588317666135505988016405 1152577390600101843188269)
                ·
                  refine ⟨432216521475038191195601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152577390600101843188269 432216521475038191195601)
                  ·
                    refine ⟨324162391106278643396701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 432216521475038191195601 324162391106278643396701)
                    ·
                      refine ⟨121560896664854491273763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 324162391106278643396701 121560896664854491273763)
                      ·
                        rfl

theorem cell23_236739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_236739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236739 prefixEnd_236739 := by exact prefixLift 236739
  have htrace : WordTrace (prefixWord ++ tailWord_236739) baseStart_236739 baseEnd_236739 := by
    simpa [prefixWord, tailWord_236739, baseEnd_236739] using wordTrace_append hprefix tailTrace_236739
  have hstable : (prefixWord ++ tailWord_236739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236739).length < 2 ^ (prefixWord ++ tailWord_236739).sum := by decide
  have hdescent : baseEnd_236739 < baseStart_236739 := by decide
  rcases family_descends (prefixWord ++ tailWord_236739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236746 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_236746 : Nat := 118140960795 + 236746 * 2 ^ 59
def prefixEnd_236746 : Nat := 4983230072969 + 3 ^ 40 * 236746 * 2
def baseEnd_236746 : Nat := 40521497009811987962077

theorem tailTrace_236746 : CollatzResearch.WordTrace tailWord_236746 prefixEnd_236746 40521497009811987962077 := by
  unfold tailWord_236746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158709000079287460718523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5756557333544766561916061 2158709000079287460718523)
  ·
    refine ⟨3238063500118931191077785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2158709000079287460718523 3238063500118931191077785)
    ·
      refine ⟨2428547625089198393308339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3238063500118931191077785 2428547625089198393308339)
      ·
        refine ⟨3642821437633797589962509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428547625089198393308339 3642821437633797589962509)
        ·
          refine ⟨1366058039112674096235941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3642821437633797589962509 1366058039112674096235941)
          ·
            refine ⟨256135882333626393044239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1366058039112674096235941 256135882333626393044239)
            ·
              refine ⟨384203823500439589566359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256135882333626393044239 384203823500439589566359)
              ·
                refine ⟨576305735250659384349539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384203823500439589566359 576305735250659384349539)
                ·
                  refine ⟨864458602875989076524309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576305735250659384349539 864458602875989076524309)
                  ·
                    refine ⟨40521497009811987962077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 864458602875989076524309 40521497009811987962077)
                    ·
                      rfl

theorem cell23_236746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_236746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236746 prefixEnd_236746 := by exact prefixLift 236746
  have htrace : WordTrace (prefixWord ++ tailWord_236746) baseStart_236746 baseEnd_236746 := by
    simpa [prefixWord, tailWord_236746, baseEnd_236746] using wordTrace_append hprefix tailTrace_236746
  have hstable : (prefixWord ++ tailWord_236746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236746).length < 2 ^ (prefixWord ++ tailWord_236746).sum := by decide
  have hdescent : baseEnd_236746 < baseStart_236746 := by decide
  rcases family_descends (prefixWord ++ tailWord_236746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236759 : List Nat := [1, 1, 3, 2, 1, 2, 6, 7]
def baseStart_236759 : Nat := 118140960795 + 236759 * 2 ^ 59
def prefixEnd_236759 : Nat := 4983230072969 + 3 ^ 40 * 236759 * 2
def baseEnd_236759 : Nat := 4502635788072015297173

theorem tailTrace_236759 : CollatzResearch.WordTrace tailWord_236759 prefixEnd_236759 4502635788072015297173 := by
  unfold tailWord_236759
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635310149270053063097331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5756873432846702042064887 8635310149270053063097331)
  ·
    refine ⟨12952965223905079594645997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8635310149270053063097331 12952965223905079594645997)
    ·
      refine ⟨4857361958964404847992249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12952965223905079594645997 4857361958964404847992249)
      ·
        refine ⟨3643021469223303635994187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4857361958964404847992249 3643021469223303635994187)
        ·
          refine ⟨5464532203834955453991281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643021469223303635994187 5464532203834955453991281)
          ·
            refine ⟨4098399152876216590493461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5464532203834955453991281 4098399152876216590493461)
            ·
              refine ⟨192112460291072652679381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4098399152876216590493461 192112460291072652679381)
              ·
                refine ⟨4502635788072015297173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 192112460291072652679381 4502635788072015297173)
                ·
                  rfl

theorem cell23_236759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 7].length) (baseStart_236759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236759 prefixEnd_236759 := by exact prefixLift 236759
  have htrace : WordTrace (prefixWord ++ tailWord_236759) baseStart_236759 baseEnd_236759 := by
    simpa [prefixWord, tailWord_236759, baseEnd_236759] using wordTrace_append hprefix tailTrace_236759
  have hstable : (prefixWord ++ tailWord_236759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236759).length < 2 ^ (prefixWord ++ tailWord_236759).sum := by decide
  have hdescent : baseEnd_236759 < baseStart_236759 := by decide
  rcases family_descends (prefixWord ++ tailWord_236759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236787 : List Nat := [1, 1, 1, 2, 2, 6, 3, 2, 1, 2, 2]
def baseStart_236787 : Nat := 118140960795 + 236787 * 2 ^ 59
def prefixEnd_236787 : Nat := 4983230072969 + 3 ^ 40 * 236787 * 2
def baseEnd_236787 : Nat := 121585543736270303473543

theorem tailTrace_236787 : CollatzResearch.WordTrace tailWord_236787 prefixEnd_236787 121585543736270303473543 := by
  unfold tailWord_236787
  simp only [CollatzResearch.WordTrace]
  refine ⟨8636331393168613845116615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5757554262112409230077743 8636331393168613845116615)
  ·
    refine ⟨12954497089752920767674923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8636331393168613845116615 12954497089752920767674923)
    ·
      refine ⟨19431745634629381151512385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12954497089752920767674923 19431745634629381151512385)
      ·
        refine ⟨14573809225972035863634289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19431745634629381151512385 14573809225972035863634289)
        ·
          refine ⟨10930356919479026897725717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14573809225972035863634289 10930356919479026897725717)
          ·
            refine ⟨512360480600579385830893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10930356919479026897725717 512360480600579385830893)
            ·
              refine ⟨192135180225217269686585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512360480600579385830893 192135180225217269686585)
              ·
                refine ⟨144101385168912952264939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192135180225217269686585 144101385168912952264939)
                ·
                  refine ⟨216152077753369428397409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144101385168912952264939 216152077753369428397409)
                  ·
                    refine ⟨162114058315027071298057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 216152077753369428397409 162114058315027071298057)
                    ·
                      refine ⟨121585543736270303473543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162114058315027071298057 121585543736270303473543)
                      ·
                        rfl

theorem cell23_236787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 1, 2, 2].length) (baseStart_236787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236787 prefixEnd_236787 := by exact prefixLift 236787
  have htrace : WordTrace (prefixWord ++ tailWord_236787) baseStart_236787 baseEnd_236787 := by
    simpa [prefixWord, tailWord_236787, baseEnd_236787] using wordTrace_append hprefix tailTrace_236787
  have hstable : (prefixWord ++ tailWord_236787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236787).length < 2 ^ (prefixWord ++ tailWord_236787).sum := by decide
  have hdescent : baseEnd_236787 < baseStart_236787 := by decide
  rcases family_descends (prefixWord ++ tailWord_236787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236803 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 2, 1, 3]
def baseStart_236803 : Nat := 118140960795 + 236803 * 2 ^ 59
def prefixEnd_236803 : Nat := 4983230072969 + 3 ^ 40 * 236803 * 2
def baseEnd_236803 : Nat := 121593759426742240873469

theorem tailTrace_236803 : CollatzResearch.WordTrace tailWord_236803 prefixEnd_236803 121593759426742240873469 := by
  unfold tailWord_236803
  simp only [CollatzResearch.WordTrace]
  refine ⟨8636914961110648577699063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5757943307407099051799375 8636914961110648577699063)
  ·
    refine ⟨12955372441665972866548595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8636914961110648577699063 12955372441665972866548595)
    ·
      refine ⟨19433058662498959299822893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12955372441665972866548595 19433058662498959299822893)
      ·
        refine ⟨7287396998437109737433585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19433058662498959299822893 7287396998437109737433585)
        ·
          refine ⟨5465547748827832303075189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7287396998437109737433585 5465547748827832303075189)
          ·
            refine ⟨512395101452609278413299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5465547748827832303075189 512395101452609278413299)
            ·
              refine ⟨768592652178913917619949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512395101452609278413299 768592652178913917619949)
              ·
                refine ⟨288222244567092719107481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 768592652178913917619949 288222244567092719107481)
                ·
                  refine ⟨216166683425319539330611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288222244567092719107481 216166683425319539330611)
                  ·
                    refine ⟨324250025137979308995917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216166683425319539330611 324250025137979308995917)
                    ·
                      refine ⟨121593759426742240873469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 324250025137979308995917 121593759426742240873469)
                      ·
                        rfl

theorem cell23_236803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_236803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236803 prefixEnd_236803 := by exact prefixLift 236803
  have htrace : WordTrace (prefixWord ++ tailWord_236803) baseStart_236803 baseEnd_236803 := by
    simpa [prefixWord, tailWord_236803, baseEnd_236803] using wordTrace_append hprefix tailTrace_236803
  have hstable : (prefixWord ++ tailWord_236803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236803).length < 2 ^ (prefixWord ++ tailWord_236803).sum := by decide
  have hdescent : baseEnd_236803 < baseStart_236803 := by decide
  rcases family_descends (prefixWord ++ tailWord_236803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236860 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 2, 2, 2]
def baseStart_236860 : Nat := 118140960795 + 236860 * 2 ^ 59
def prefixEnd_236860 : Nat := 4983230072969 + 3 ^ 40 * 236860 * 2
def baseEnd_236860 : Nat := 121623027824048517860707

theorem tailTrace_236860 : CollatzResearch.WordTrace tailWord_236860 prefixEnd_236860 121623027824048517860707 := by
  unfold tailWord_236860
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319496960952073656262017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5759329281269431541682689 4319496960952073656262017)
  ·
    refine ⟨3239622720714055242196513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4319496960952073656262017 3239622720714055242196513)
    ·
      refine ⟨2429717040535541431647385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3239622720714055242196513 2429717040535541431647385)
      ·
        refine ⟨1822287780401656073735539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2429717040535541431647385 1822287780401656073735539)
        ·
          refine ⟨2733431670602484110603309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822287780401656073735539 2733431670602484110603309)
          ·
            refine ⟨1025036876475931541476241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2733431670602484110603309 1025036876475931541476241)
            ·
              refine ⟨768777657356948656107181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1025036876475931541476241 768777657356948656107181)
              ·
                refine ⟨288291621508855746040193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 768777657356948656107181 288291621508855746040193)
                ·
                  refine ⟨216218716131641809530145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288291621508855746040193 216218716131641809530145)
                  ·
                    refine ⟨162164037098731357147609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 216218716131641809530145 162164037098731357147609)
                    ·
                      refine ⟨121623027824048517860707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162164037098731357147609 121623027824048517860707)
                      ·
                        rfl

theorem cell23_236860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_236860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236860 prefixEnd_236860 := by exact prefixLift 236860
  have htrace : WordTrace (prefixWord ++ tailWord_236860) baseStart_236860 baseEnd_236860 := by
    simpa [prefixWord, tailWord_236860, baseEnd_236860] using wordTrace_append hprefix tailTrace_236860
  have hstable : (prefixWord ++ tailWord_236860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236860).length < 2 ^ (prefixWord ++ tailWord_236860).sum := by decide
  have hdescent : baseEnd_236860 < baseStart_236860 := by decide
  rcases family_descends (prefixWord ++ tailWord_236860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236889 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_236889 : Nat := 118140960795 + 236889 * 2 ^ 59
def prefixEnd_236889 : Nat := 4983230072969 + 3 ^ 40 * 236889 * 2
def baseEnd_236889 : Nat := 121637918763028904398073

theorem tailTrace_236889 : CollatzResearch.WordTrace tailWord_236889 prefixEnd_236889 121637918763028904398073 := by
  unfold tailWord_236889
  simp only [CollatzResearch.WordTrace]
  refine ⟨8640051638799085265329721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5760034425866056843553147 8640051638799085265329721)
  ·
    refine ⟨6480038729099313948997291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8640051638799085265329721 6480038729099313948997291)
    ·
      refine ⟨9720058093648970923495937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6480038729099313948997291 9720058093648970923495937)
      ·
        refine ⟨7290043570236728192621953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9720058093648970923495937 7290043570236728192621953)
        ·
          refine ⟨5467532677677546144466465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7290043570236728192621953 5467532677677546144466465)
          ·
            refine ⟨4100649508258159608349849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5467532677677546144466465 4100649508258159608349849)
            ·
              refine ⟨3075487131193619706262387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4100649508258159608349849 3075487131193619706262387)
              ·
                refine ⟨4613230696790429559393581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075487131193619706262387 4613230696790429559393581)
                ·
                  refine ⟨1729961511296411084772593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4613230696790429559393581 1729961511296411084772593)
                  ·
                    refine ⟨1297471133472308313579445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1729961511296411084772593 1297471133472308313579445)
                    ·
                      refine ⟨121637918763028904398073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1297471133472308313579445 121637918763028904398073)
                      ·
                        rfl

theorem cell23_236889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_236889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236889 prefixEnd_236889 := by exact prefixLift 236889
  have htrace : WordTrace (prefixWord ++ tailWord_236889) baseStart_236889 baseEnd_236889 := by
    simpa [prefixWord, tailWord_236889, baseEnd_236889] using wordTrace_append hprefix tailTrace_236889
  have hstable : (prefixWord ++ tailWord_236889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236889).length < 2 ^ (prefixWord ++ tailWord_236889).sum := by decide
  have hdescent : baseEnd_236889 < baseStart_236889 := by decide
  rcases family_descends (prefixWord ++ tailWord_236889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236939 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 10]
def baseStart_236939 : Nat := 118140960795 + 236939 * 2 ^ 59
def prefixEnd_236939 : Nat := 4983230072969 + 3 ^ 40 * 236939 * 2
def baseEnd_236939 : Nat := 13518176977305967641427

theorem tailTrace_236939 : CollatzResearch.WordTrace tailWord_236939 prefixEnd_236939 13518176977305967641427 := by
  unfold tailWord_236939
  simp only [CollatzResearch.WordTrace]
  refine ⟨8641875288617943804649871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5761250192411962536433247 8641875288617943804649871)
  ·
    refine ⟨12962812932926915706974807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8641875288617943804649871 12962812932926915706974807)
    ·
      refine ⟨19444219399390373560462211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12962812932926915706974807 19444219399390373560462211)
      ·
        refine ⟨29166329099085560340693317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19444219399390373560462211 29166329099085560340693317)
        ·
          refine ⟨5468686706078542563879997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29166329099085560340693317 5468686706078542563879997)
          ·
            refine ⟨2050757514779453461454999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5468686706078542563879997 2050757514779453461454999)
            ·
              refine ⟨3076136272169180192182499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050757514779453461454999 3076136272169180192182499)
              ·
                refine ⟨4614204408253770288273749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076136272169180192182499 4614204408253770288273749)
                ·
                  refine ⟨13518176977305967641427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 4614204408253770288273749 13518176977305967641427)
                  ·
                    rfl

theorem cell23_236939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 10].length) (baseStart_236939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236939 prefixEnd_236939 := by exact prefixLift 236939
  have htrace : WordTrace (prefixWord ++ tailWord_236939) baseStart_236939 baseEnd_236939 := by
    simpa [prefixWord, tailWord_236939, baseEnd_236939] using wordTrace_append hprefix tailTrace_236939
  have hstable : (prefixWord ++ tailWord_236939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236939).length < 2 ^ (prefixWord ++ tailWord_236939).sum := by decide
  have hdescent : baseEnd_236939 < baseStart_236939 := by decide
  rcases family_descends (prefixWord ++ tailWord_236939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236953 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 2, 2, 3]
def baseStart_236953 : Nat := 118140960795 + 236953 * 2 ^ 59
def prefixEnd_236953 : Nat := 4983230072969 + 3 ^ 40 * 236953 * 2
def baseEnd_236953 : Nat := 121670781524916653997779

theorem tailTrace_236953 : CollatzResearch.WordTrace tailWord_236953 prefixEnd_236953 121670781524916653997779 := by
  unfold tailWord_236953
  simp only [CollatzResearch.WordTrace]
  refine ⟨8642385910567224195659513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5761590607044816130439675 8642385910567224195659513)
  ·
    refine ⟨6481789432925418146744635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8642385910567224195659513 6481789432925418146744635)
    ·
      refine ⟨9722684149388127220116953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6481789432925418146744635 9722684149388127220116953)
      ·
        refine ⟨7292013112041095415087715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9722684149388127220116953 7292013112041095415087715)
        ·
          refine ⟨10938019668061643122631573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7292013112041095415087715 10938019668061643122631573)
          ·
            refine ⟨512719671940389521373355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10938019668061643122631573 512719671940389521373355)
            ·
              refine ⟨769079507910584282060033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512719671940389521373355 769079507910584282060033)
              ·
                refine ⟨576809630932938211545025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769079507910584282060033 576809630932938211545025)
                ·
                  refine ⟨432607223199703658658769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576809630932938211545025 432607223199703658658769)
                  ·
                    refine ⟨324455417399777743994077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 432607223199703658658769 324455417399777743994077)
                    ·
                      refine ⟨121670781524916653997779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 324455417399777743994077 121670781524916653997779)
                      ·
                        rfl

theorem cell23_236953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_236953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236953 prefixEnd_236953 := by exact prefixLift 236953
  have htrace : WordTrace (prefixWord ++ tailWord_236953) baseStart_236953 baseEnd_236953 := by
    simpa [prefixWord, tailWord_236953, baseEnd_236953] using wordTrace_append hprefix tailTrace_236953
  have hstable : (prefixWord ++ tailWord_236953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236953).length < 2 ^ (prefixWord ++ tailWord_236953).sum := by decide
  have hdescent : baseEnd_236953 < baseStart_236953 := by decide
  rcases family_descends (prefixWord ++ tailWord_236953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236969 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 1, 11]
def baseStart_236969 : Nat := 118140960795 + 236969 * 2 ^ 59
def prefixEnd_236969 : Nat := 4983230072969 + 3 ^ 40 * 236969 * 2
def baseEnd_236969 : Nat := 40559665738462863799235

theorem tailTrace_236969 : CollatzResearch.WordTrace tailWord_236969 prefixEnd_236969 40559665738462863799235 := by
  unfold tailWord_236969
  simp only [CollatzResearch.WordTrace]
  refine ⟨8642969478509258928241961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5761979652339505952161307 8642969478509258928241961)
  ·
    refine ⟨6482227108881944196181471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8642969478509258928241961 6482227108881944196181471)
    ·
      refine ⟨9723340663322916294272207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6482227108881944196181471 9723340663322916294272207)
      ·
        refine ⟨14585010994984374441408311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9723340663322916294272207 14585010994984374441408311)
        ·
          refine ⟨21877516492476561662112467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14585010994984374441408311 21877516492476561662112467)
          ·
            refine ⟨32816274738714842493168701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21877516492476561662112467 32816274738714842493168701)
            ·
              refine ⟨12306103027018065934938263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32816274738714842493168701 12306103027018065934938263)
              ·
                refine ⟨18459154540527098902407395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12306103027018065934938263 18459154540527098902407395)
                ·
                  refine ⟨27688731810790648353611093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18459154540527098902407395 27688731810790648353611093)
                  ·
                    refine ⟨40559665738462863799235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 27688731810790648353611093 40559665738462863799235)
                    ·
                      rfl

theorem cell23_236969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_236969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236969 prefixEnd_236969 := by exact prefixLift 236969
  have htrace : WordTrace (prefixWord ++ tailWord_236969) baseStart_236969 baseEnd_236969 := by
    simpa [prefixWord, tailWord_236969, baseEnd_236969] using wordTrace_append hprefix tailTrace_236969
  have hstable : (prefixWord ++ tailWord_236969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236969).length < 2 ^ (prefixWord ++ tailWord_236969).sum := by decide
  have hdescent : baseEnd_236969 < baseStart_236969 := by decide
  rcases family_descends (prefixWord ++ tailWord_236969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236983 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 5, 1, 3]
def baseStart_236983 : Nat := 118140960795 + 236983 * 2 ^ 59
def prefixEnd_236983 : Nat := 4983230072969 + 3 ^ 40 * 236983 * 2
def baseEnd_236983 : Nat := 121686185944551536622641

theorem tailTrace_236983 : CollatzResearch.WordTrace tailWord_236983 prefixEnd_236983 121686185944551536622641 := by
  unfold tailWord_236983
  simp only [CollatzResearch.WordTrace]
  refine ⟨8643480100458539319251603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5762320066972359546167735 8643480100458539319251603)
  ·
    refine ⟨12965220150687808978877405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8643480100458539319251603 12965220150687808978877405)
    ·
      refine ⟨4861957556507928367079027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12965220150687808978877405 4861957556507928367079027)
      ·
        refine ⟨7292936334761892550618541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4861957556507928367079027 7292936334761892550618541)
        ·
          refine ⟨2734851125535709706481953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7292936334761892550618541 2734851125535709706481953)
          ·
            refine ⟨2051138344151782279861465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2734851125535709706481953 2051138344151782279861465)
            ·
              refine ⟨1538353758113836709896099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051138344151782279861465 1538353758113836709896099)
              ·
                refine ⟨2307530637170755064844149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538353758113836709896099 2307530637170755064844149)
                ·
                  refine ⟨216330997234758287329139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2307530637170755064844149 216330997234758287329139)
                  ·
                    refine ⟨324496495852137430993709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216330997234758287329139 324496495852137430993709)
                    ·
                      refine ⟨121686185944551536622641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 324496495852137430993709 121686185944551536622641)
                      ·
                        rfl

theorem cell23_236983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_236983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_236983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_236983 prefixEnd_236983 := by exact prefixLift 236983
  have htrace : WordTrace (prefixWord ++ tailWord_236983) baseStart_236983 baseEnd_236983 := by
    simpa [prefixWord, tailWord_236983, baseEnd_236983] using wordTrace_append hprefix tailTrace_236983
  have hstable : (prefixWord ++ tailWord_236983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236983).length < 2 ^ (prefixWord ++ tailWord_236983).sum := by decide
  have hdescent : baseEnd_236983 < baseStart_236983 := by decide
  rcases family_descends (prefixWord ++ tailWord_236983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237017 : List Nat := [1, 2, 1, 2, 4, 3, 1, 4, 1, 1, 3]
def baseStart_237017 : Nat := 118140960795 + 237017 * 2 ^ 59
def prefixEnd_237017 : Nat := 4983230072969 + 3 ^ 40 * 237017 * 2
def baseEnd_237017 : Nat := 121703644286804403597485

theorem tailTrace_237017 : CollatzResearch.WordTrace tailWord_237017 prefixEnd_237017 121703644286804403597485 := by
  unfold tailWord_237017
  simp only [CollatzResearch.WordTrace]
  refine ⟨8644720182335363125989305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5763146788223575417326203 8644720182335363125989305)
  ·
    refine ⟨6483540136751522344491979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8644720182335363125989305 6483540136751522344491979)
    ·
      refine ⟨9725310205127283516737969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6483540136751522344491979 9725310205127283516737969)
      ·
        refine ⟨7293982653845462637553477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9725310205127283516737969 7293982653845462637553477)
        ·
          refine ⟨1367621747596024244541277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7293982653845462637553477 1367621747596024244541277)
          ·
            refine ⟨512858155348509091702979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1367621747596024244541277 512858155348509091702979)
            ·
              refine ⟨769287233022763637554469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512858155348509091702979 769287233022763637554469)
              ·
                refine ⟨144241356191768182041463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 769287233022763637554469 144241356191768182041463)
                ·
                  refine ⟨216362034287652273062195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144241356191768182041463 216362034287652273062195)
                  ·
                    refine ⟨324543051431478409593293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216362034287652273062195 324543051431478409593293)
                    ·
                      refine ⟨121703644286804403597485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 324543051431478409593293 121703644286804403597485)
                      ·
                        rfl

theorem cell23_237017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 1, 1, 3].length) (baseStart_237017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237017 prefixEnd_237017 := by exact prefixLift 237017
  have htrace : WordTrace (prefixWord ++ tailWord_237017) baseStart_237017 baseEnd_237017 := by
    simpa [prefixWord, tailWord_237017, baseEnd_237017] using wordTrace_append hprefix tailTrace_237017
  have hstable : (prefixWord ++ tailWord_237017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237017).length < 2 ^ (prefixWord ++ tailWord_237017).sum := by decide
  have hdescent : baseEnd_237017 < baseStart_237017 := by decide
  rcases family_descends (prefixWord ++ tailWord_237017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237040 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 5, 2, 2]
def baseStart_237040 : Nat := 118140960795 + 237040 * 2 ^ 59
def prefixEnd_237040 : Nat := 4983230072969 + 3 ^ 40 * 237040 * 2
def baseEnd_237040 : Nat := 121715454341857813609879

theorem tailTrace_237040 : CollatzResearch.WordTrace tailWord_237040 prefixEnd_237040 121715454341857813609879 := by
  unfold tailWord_237040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322779530626019027038287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5763706040834692036051049 4322779530626019027038287)
  ·
    refine ⟨6484169295939028540557431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4322779530626019027038287 6484169295939028540557431)
    ·
      refine ⟨9726253943908542810836147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6484169295939028540557431 9726253943908542810836147)
      ·
        refine ⟨14589380915862814216254221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9726253943908542810836147 14589380915862814216254221)
        ·
          refine ⟨5471017843448555331095333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14589380915862814216254221 5471017843448555331095333)
          ·
            refine ⟨1025815845646604124580375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5471017843448555331095333 1025815845646604124580375)
            ·
              refine ⟨1538723768469906186870563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025815845646604124580375 1538723768469906186870563)
              ·
                refine ⟨2308085652704859280305845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538723768469906186870563 2308085652704859280305845)
                ·
                  refine ⟨216383029941080557528673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2308085652704859280305845 216383029941080557528673)
                  ·
                    refine ⟨162287272455810418146505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 216383029941080557528673 162287272455810418146505)
                    ·
                      refine ⟨121715454341857813609879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162287272455810418146505 121715454341857813609879)
                      ·
                        rfl

theorem cell23_237040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5, 2, 2].length) (baseStart_237040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237040 prefixEnd_237040 := by exact prefixLift 237040
  have htrace : WordTrace (prefixWord ++ tailWord_237040) baseStart_237040 baseEnd_237040 := by
    simpa [prefixWord, tailWord_237040, baseEnd_237040] using wordTrace_append hprefix tailTrace_237040
  have hstable : (prefixWord ++ tailWord_237040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237040).length < 2 ^ (prefixWord ++ tailWord_237040).sum := by decide
  have hdescent : baseEnd_237040 < baseStart_237040 := by decide
  rcases family_descends (prefixWord ++ tailWord_237040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237053 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_237053 : Nat := 118140960795 + 237053 * 2 ^ 59
def prefixEnd_237053 : Nat := 4983230072969 + 3 ^ 40 * 237053 * 2
def baseEnd_237053 : Nat := 121722129590366262747319

theorem tailTrace_237053 : CollatzResearch.WordTrace tailWord_237053 prefixEnd_237053 121722129590366262747319 := by
  unfold tailWord_237053
  simp only [CollatzResearch.WordTrace]
  refine ⟨8646033210204941274299813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5764022140136627516199875 8646033210204941274299813)
  ·
    refine ⟨1621131226913426488931215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8646033210204941274299813 1621131226913426488931215)
    ·
      refine ⟨2431696840370139733396823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1621131226913426488931215 2431696840370139733396823)
      ·
        refine ⟨3647545260555209600095235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431696840370139733396823 3647545260555209600095235)
        ·
          refine ⟨5471317890832814400142853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3647545260555209600095235 5471317890832814400142853)
          ·
            refine ⟨1025872104531152700026785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5471317890832814400142853 1025872104531152700026785)
            ·
              refine ⟨769404078398364525020089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1025872104531152700026785 769404078398364525020089)
              ·
                refine ⟨577053058798773393765067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769404078398364525020089 577053058798773393765067)
                ·
                  refine ⟨865579588198160090647601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577053058798773393765067 865579588198160090647601)
                  ·
                    refine ⟨649184691148620067985701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 865579588198160090647601 649184691148620067985701)
                    ·
                      refine ⟨121722129590366262747319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 649184691148620067985701 121722129590366262747319)
                      ·
                        rfl

theorem cell23_237053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_237053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237053 prefixEnd_237053 := by exact prefixLift 237053
  have htrace : WordTrace (prefixWord ++ tailWord_237053) baseStart_237053 baseEnd_237053 := by
    simpa [prefixWord, tailWord_237053, baseEnd_237053] using wordTrace_append hprefix tailTrace_237053
  have hstable : (prefixWord ++ tailWord_237053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237053).length < 2 ^ (prefixWord ++ tailWord_237053).sum := by decide
  have hdescent : baseEnd_237053 < baseStart_237053 := by decide
  rcases family_descends (prefixWord ++ tailWord_237053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237067 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 2, 4]
def baseStart_237067 : Nat := 118140960795 + 237067 * 2 ^ 59
def prefixEnd_237067 : Nat := 4983230072969 + 3 ^ 40 * 237067 * 2
def baseEnd_237067 : Nat := 40576439439843069324085

theorem tailTrace_237067 : CollatzResearch.WordTrace tailWord_237067 prefixEnd_237067 40576439439843069324085 := by
  unfold tailWord_237067
  simp only [CollatzResearch.WordTrace]
  refine ⟨8646543832154221665309455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5764362554769481110206303 8646543832154221665309455)
  ·
    refine ⟨12969815748231332497964183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8646543832154221665309455 12969815748231332497964183)
    ·
      refine ⟨19454723622346998746946275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12969815748231332497964183 19454723622346998746946275)
      ·
        refine ⟨29182085433520498120419413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19454723622346998746946275 29182085433520498120419413)
        ·
          refine ⟨341977563674068337348665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 29182085433520498120419413 341977563674068337348665)
          ·
            refine ⟨256483172755551253011499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341977563674068337348665 256483172755551253011499)
            ·
              refine ⟨384724759133326879517249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256483172755551253011499 384724759133326879517249)
              ·
                refine ⟨288543569349995159637937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384724759133326879517249 288543569349995159637937)
                ·
                  refine ⟨216407677012496369728453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288543569349995159637937 216407677012496369728453)
                  ·
                    refine ⟨40576439439843069324085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 216407677012496369728453 40576439439843069324085)
                    ·
                      rfl

theorem cell23_237067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 4].length) (baseStart_237067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237067 prefixEnd_237067 := by exact prefixLift 237067
  have htrace : WordTrace (prefixWord ++ tailWord_237067) baseStart_237067 baseEnd_237067 := by
    simpa [prefixWord, tailWord_237067, baseEnd_237067] using wordTrace_append hprefix tailTrace_237067
  have hstable : (prefixWord ++ tailWord_237067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237067).length < 2 ^ (prefixWord ++ tailWord_237067).sum := by decide
  have hdescent : baseEnd_237067 < baseStart_237067 := by decide
  rcases family_descends (prefixWord ++ tailWord_237067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237090 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_237090 : Nat := 118140960795 + 237090 * 2 ^ 59
def prefixEnd_237090 : Nat := 4983230072969 + 3 ^ 40 * 237090 * 2
def baseEnd_237090 : Nat := 121741128374582617984649

theorem tailTrace_237090 : CollatzResearch.WordTrace tailWord_237090 prefixEnd_237090 121741128374582617984649 := by
  unfold tailWord_237090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2161845677767724148349181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5764921807380597728931149 2161845677767724148349181)
  ·
    refine ⟨810692129162896555630943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2161845677767724148349181 810692129162896555630943)
    ·
      refine ⟨1216038193744344833446415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810692129162896555630943 1216038193744344833446415)
      ·
        refine ⟨1824057290616517250169623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216038193744344833446415 1824057290616517250169623)
        ·
          refine ⟨2736085935924775875254435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824057290616517250169623 2736085935924775875254435)
          ·
            refine ⟨4104128903887163812881653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736085935924775875254435 4104128903887163812881653)
            ·
              refine ⟨384762084739421607457655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4104128903887163812881653 384762084739421607457655)
              ·
                refine ⟨577143127109132411186483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384762084739421607457655 577143127109132411186483)
                ·
                  refine ⟨865714690663698616779725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577143127109132411186483 865714690663698616779725)
                  ·
                    refine ⟨324643008998886981292397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 865714690663698616779725 324643008998886981292397)
                    ·
                      refine ⟨121741128374582617984649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 324643008998886981292397 121741128374582617984649)
                      ·
                        rfl

theorem cell23_237090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_237090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237090 prefixEnd_237090 := by exact prefixLift 237090
  have htrace : WordTrace (prefixWord ++ tailWord_237090) baseStart_237090 baseEnd_237090 := by
    simpa [prefixWord, tailWord_237090, baseEnd_237090] using wordTrace_append hprefix tailTrace_237090
  have hstable : (prefixWord ++ tailWord_237090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237090).length < 2 ^ (prefixWord ++ tailWord_237090).sum := by decide
  have hdescent : baseEnd_237090 < baseStart_237090 := by decide
  rcases family_descends (prefixWord ++ tailWord_237090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237193 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_237193 : Nat := 118140960795 + 237193 * 2 ^ 59
def prefixEnd_237193 : Nat := 4983230072969 + 3 ^ 40 * 237193 * 2
def baseEnd_237193 : Nat := 121794016881995714996675

theorem tailTrace_237193 : CollatzResearch.WordTrace tailWord_237193 prefixEnd_237193 121794016881995714996675 := by
  unfold tailWord_237193
  simp only [CollatzResearch.WordTrace]
  refine ⟨8651139429697745184396233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5767426286465163456264155 8651139429697745184396233)
  ·
    refine ⟨6488354572273308888297175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8651139429697745184396233 6488354572273308888297175)
    ·
      refine ⟨9732531858409963332445763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6488354572273308888297175 9732531858409963332445763)
      ·
        refine ⟨14598797787614944998668645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9732531858409963332445763 14598797787614944998668645)
        ·
          refine ⟨2737274585177802187250371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14598797787614944998668645 2737274585177802187250371)
          ·
            refine ⟨4105911877766703280875557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737274585177802187250371 4105911877766703280875557)
            ·
              refine ⟨769858477081256865164167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4105911877766703280875557 769858477081256865164167)
              ·
                refine ⟨1154787715621885297746251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769858477081256865164167 1154787715621885297746251)
                ·
                  refine ⟨1732181573432827946619377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154787715621885297746251 1732181573432827946619377)
                  ·
                    refine ⟨1299136180074620959964533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1732181573432827946619377 1299136180074620959964533)
                    ·
                      refine ⟨121794016881995714996675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1299136180074620959964533 121794016881995714996675)
                      ·
                        rfl

theorem cell23_237193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_237193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237193 prefixEnd_237193 := by exact prefixLift 237193
  have htrace : WordTrace (prefixWord ++ tailWord_237193) baseStart_237193 baseEnd_237193 := by
    simpa [prefixWord, tailWord_237193, baseEnd_237193] using wordTrace_append hprefix tailTrace_237193
  have hstable : (prefixWord ++ tailWord_237193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237193).length < 2 ^ (prefixWord ++ tailWord_237193).sum := by decide
  have hdescent : baseEnd_237193 < baseStart_237193 := by decide
  rcases family_descends (prefixWord ++ tailWord_237193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237217 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 2, 5]
def baseStart_237217 : Nat := 118140960795 + 237217 * 2 ^ 59
def prefixEnd_237217 : Nat := 4983230072969 + 3 ^ 40 * 237217 * 2
def baseEnd_237217 : Nat := 40602113472567873698855

theorem tailTrace_237217 : CollatzResearch.WordTrace tailWord_237217 prefixEnd_237217 40602113472567873698855 := by
  unfold tailWord_237217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652014781610797283269905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5768009854407198188846603 8652014781610797283269905)
  ·
    refine ⟨6489011086208097962452429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8652014781610797283269905 6489011086208097962452429)
    ·
      refine ⟨2433379157328036735919661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6489011086208097962452429 2433379157328036735919661)
      ·
        refine ⟨912517183998013775969873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2433379157328036735919661 912517183998013775969873)
        ·
          refine ⟨684387887998510331977405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 912517183998013775969873 684387887998510331977405)
          ·
            refine ⟨256645457999441374491527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 684387887998510331977405 256645457999441374491527)
            ·
              refine ⟨384968186999162061737291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256645457999441374491527 384968186999162061737291)
              ·
                refine ⟨577452280498743092605937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384968186999162061737291 577452280498743092605937)
                ·
                  refine ⟨433089210374057319454453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577452280498743092605937 433089210374057319454453)
                  ·
                    refine ⟨40602113472567873698855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 433089210374057319454453 40602113472567873698855)
                    ·
                      rfl

theorem cell23_237217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_237217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237217 prefixEnd_237217 := by exact prefixLift 237217
  have htrace : WordTrace (prefixWord ++ tailWord_237217) baseStart_237217 baseEnd_237217 := by
    simpa [prefixWord, tailWord_237217, baseEnd_237217] using wordTrace_append hprefix tailTrace_237217
  have hstable : (prefixWord ++ tailWord_237217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237217).length < 2 ^ (prefixWord ++ tailWord_237217).sum := by decide
  have hdescent : baseEnd_237217 < baseStart_237217 := by decide
  rcases family_descends (prefixWord ++ tailWord_237217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237220 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_237220 : Nat := 118140960795 + 237220 * 2 ^ 59
def prefixEnd_237220 : Nat := 4983230072969 + 3 ^ 40 * 237220 * 2
def baseEnd_237220 : Nat := 121807880859667109359051

theorem tailTrace_237220 : CollatzResearch.WordTrace tailWord_237220 prefixEnd_237220 121807880859667109359051 := by
  unfold tailWord_237220
  simp only [CollatzResearch.WordTrace]
  refine ⟨4326062100299964397814557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5768082800399952530419409 4326062100299964397814557)
  ·
    refine ⟨1622273287612486649180459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4326062100299964397814557 1622273287612486649180459)
    ·
      refine ⟨2433409931418729973770689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622273287612486649180459 2433409931418729973770689)
      ·
        refine ⟨1825057448564047480328017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2433409931418729973770689 1825057448564047480328017)
        ·
          refine ⟨1368793086423035610246013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1825057448564047480328017 1368793086423035610246013)
          ·
            refine ⟨513297407408638353842255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1368793086423035610246013 513297407408638353842255)
            ·
              refine ⟨769946111112957530763383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513297407408638353842255 769946111112957530763383)
              ·
                refine ⟨1154919166669436296145075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769946111112957530763383 1154919166669436296145075)
                ·
                  refine ⟨1732378750004154444217613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154919166669436296145075 1732378750004154444217613)
                  ·
                    refine ⟨649642031251557916581605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732378750004154444217613 649642031251557916581605)
                    ·
                      refine ⟨121807880859667109359051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 649642031251557916581605 121807880859667109359051)
                      ·
                        rfl

theorem cell23_237220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_237220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237220 prefixEnd_237220 := by exact prefixLift 237220
  have htrace : WordTrace (prefixWord ++ tailWord_237220) baseStart_237220 baseEnd_237220 := by
    simpa [prefixWord, tailWord_237220, baseEnd_237220] using wordTrace_append hprefix tailTrace_237220
  have hstable : (prefixWord ++ tailWord_237220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237220).length < 2 ^ (prefixWord ++ tailWord_237220).sum := by decide
  have hdescent : baseEnd_237220 < baseStart_237220 := by decide
  rcases family_descends (prefixWord ++ tailWord_237220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237240 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 2, 2, 3]
def baseStart_237240 : Nat := 118140960795 + 237240 * 2 ^ 59
def prefixEnd_237240 : Nat := 4983230072969 + 3 ^ 40 * 237240 * 2
def baseEnd_237240 : Nat := 121818150472757031108959

theorem tailTrace_237240 : CollatzResearch.WordTrace tailWord_237240 prefixEnd_237240 121818150472757031108959 := by
  unfold tailWord_237240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4326426830263736105678587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5768569107018314807571449 4326426830263736105678587)
  ·
    refine ⟨6489640245395604158517881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4326426830263736105678587 6489640245395604158517881)
    ·
      refine ⟨4867230184046703118888411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6489640245395604158517881 4867230184046703118888411)
      ·
        refine ⟨7300845276070054678332617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867230184046703118888411 7300845276070054678332617)
        ·
          refine ⟨5475633957052541008749463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7300845276070054678332617 5475633957052541008749463)
          ·
            refine ⟨8213450935578811513124195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5475633957052541008749463 8213450935578811513124195)
            ·
              refine ⟨12320176403368217269686293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8213450935578811513124195 12320176403368217269686293)
              ·
                refine ⟨577508268907885184516545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12320176403368217269686293 577508268907885184516545)
                ·
                  refine ⟨433131201680913888387409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577508268907885184516545 433131201680913888387409)
                  ·
                    refine ⟨324848401260685416290557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433131201680913888387409 324848401260685416290557)
                    ·
                      refine ⟨121818150472757031108959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 324848401260685416290557 121818150472757031108959)
                      ·
                        rfl

theorem cell23_237240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_237240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237240 prefixEnd_237240 := by exact prefixLift 237240
  have htrace : WordTrace (prefixWord ++ tailWord_237240) baseStart_237240 baseEnd_237240 := by
    simpa [prefixWord, tailWord_237240, baseEnd_237240] using wordTrace_append hprefix tailTrace_237240
  have hstable : (prefixWord ++ tailWord_237240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237240).length < 2 ^ (prefixWord ++ tailWord_237240).sum := by decide
  have hdescent : baseEnd_237240 < baseStart_237240 := by decide
  rcases family_descends (prefixWord ++ tailWord_237240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237247 : List Nat := [1, 1, 2, 2, 2, 3, 1, 6, 1, 4]
def baseStart_237247 : Nat := 118140960795 + 237247 * 2 ^ 59
def prefixEnd_237247 : Nat := 4983230072969 + 3 ^ 40 * 237247 * 2
def baseEnd_237247 : Nat := 40607248279112834573809

theorem tailTrace_237247 : CollatzResearch.WordTrace tailWord_237247 prefixEnd_237247 40607248279112834573809 := by
  unfold tailWord_237247
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653108971502112406861995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5768739314334741604574663 8653108971502112406861995)
  ·
    refine ⟨12979663457253168610292993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8653108971502112406861995 12979663457253168610292993)
    ·
      refine ⟨9734747592939876457719745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12979663457253168610292993 9734747592939876457719745)
      ·
        refine ⟨7301060694704907343289809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9734747592939876457719745 7301060694704907343289809)
        ·
          refine ⟨5475795521028680507467357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7301060694704907343289809 5475795521028680507467357)
          ·
            refine ⟨2053423320385755190300259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5475795521028680507467357 2053423320385755190300259)
            ·
              refine ⟨3080134980578632785450389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053423320385755190300259 3080134980578632785450389)
              ·
                refine ⟨144381327214623411817987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3080134980578632785450389 144381327214623411817987)
                ·
                  refine ⟨216571990821935117726981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144381327214623411817987 216571990821935117726981)
                  ·
                    refine ⟨40607248279112834573809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 216571990821935117726981 40607248279112834573809)
                    ·
                      rfl

theorem cell23_237247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 1, 4].length) (baseStart_237247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237247 prefixEnd_237247 := by exact prefixLift 237247
  have htrace : WordTrace (prefixWord ++ tailWord_237247) baseStart_237247 baseEnd_237247 := by
    simpa [prefixWord, tailWord_237247, baseEnd_237247] using wordTrace_append hprefix tailTrace_237247
  have hstable : (prefixWord ++ tailWord_237247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237247).length < 2 ^ (prefixWord ++ tailWord_237247).sum := by decide
  have hdescent : baseEnd_237247 < baseStart_237247 := by decide
  rcases family_descends (prefixWord ++ tailWord_237247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237254 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_237254 : Nat := 118140960795 + 237254 * 2 ^ 59
def prefixEnd_237254 : Nat := 4983230072969 + 3 ^ 40 * 237254 * 2
def baseEnd_237254 : Nat := 121825339201919976333895

theorem tailTrace_237254 : CollatzResearch.WordTrace tailWord_237254 prefixEnd_237254 121825339201919976333895 := by
  unfold tailWord_237254
  simp only [CollatzResearch.WordTrace]
  refine ⟨270417633827398518823963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5768909521651168401577877 270417633827398518823963)
  ·
    refine ⟨405626450741097778235945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270417633827398518823963 405626450741097778235945)
    ·
      refine ⟨304219838055823333676959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405626450741097778235945 304219838055823333676959)
      ·
        refine ⟨456329757083735000515439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304219838055823333676959 456329757083735000515439)
        ·
          refine ⟨684494635625602500773159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456329757083735000515439 684494635625602500773159)
          ·
            refine ⟨1026741953438403751159739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684494635625602500773159 1026741953438403751159739)
            ·
              refine ⟨1540112930157605626739609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026741953438403751159739 1540112930157605626739609)
              ·
                refine ⟨1155084697618204220054707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540112930157605626739609 1155084697618204220054707)
                ·
                  refine ⟨1732627046427306330082061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155084697618204220054707 1732627046427306330082061)
                  ·
                    refine ⟨649735142410239873780773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732627046427306330082061 649735142410239873780773)
                    ·
                      refine ⟨121825339201919976333895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 649735142410239873780773 121825339201919976333895)
                      ·
                        rfl

theorem cell23_237254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_237254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237254 prefixEnd_237254 := by exact prefixLift 237254
  have htrace : WordTrace (prefixWord ++ tailWord_237254) baseStart_237254 baseEnd_237254 := by
    simpa [prefixWord, tailWord_237254, baseEnd_237254] using wordTrace_append hprefix tailTrace_237254
  have hstable : (prefixWord ++ tailWord_237254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237254).length < 2 ^ (prefixWord ++ tailWord_237254).sum := by decide
  have hdescent : baseEnd_237254 < baseStart_237254 := by decide
  rcases family_descends (prefixWord ++ tailWord_237254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237281 : List Nat := [1, 2, 3, 1, 5, 2, 1, 3, 1, 4]
def baseStart_237281 : Nat := 118140960795 + 237281 * 2 ^ 59
def prefixEnd_237281 : Nat := 4983230072969 + 3 ^ 40 * 237281 * 2
def baseEnd_237281 : Nat := 40613067726530456898757

theorem tailTrace_237281 : CollatzResearch.WordTrace tailWord_237281 prefixEnd_237281 40613067726530456898757 := by
  unfold tailWord_237281
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654349053378936213599697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5769566035585957475733131 8654349053378936213599697)
  ·
    refine ⟨6490761790034202160199773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8654349053378936213599697 6490761790034202160199773)
    ·
      refine ⟨2434035671262825810074915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6490761790034202160199773 2434035671262825810074915)
      ·
        refine ⟨3651053506894238715112373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434035671262825810074915 3651053506894238715112373)
        ·
          refine ⟨342286266271334879541785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3651053506894238715112373 342286266271334879541785)
          ·
            refine ⟨256714699703501159656339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342286266271334879541785 256714699703501159656339)
            ·
              refine ⟨385072049555251739484509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256714699703501159656339 385072049555251739484509)
              ·
                refine ⟨144402018583219402306691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385072049555251739484509 144402018583219402306691)
                ·
                  refine ⟨216603027874829103460037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144402018583219402306691 216603027874829103460037)
                  ·
                    refine ⟨40613067726530456898757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 216603027874829103460037 40613067726530456898757)
                    ·
                      rfl

theorem cell23_237281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_237281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237281 prefixEnd_237281 := by exact prefixLift 237281
  have htrace : WordTrace (prefixWord ++ tailWord_237281) baseStart_237281 baseEnd_237281 := by
    simpa [prefixWord, tailWord_237281, baseEnd_237281] using wordTrace_append hprefix tailTrace_237281
  have hstable : (prefixWord ++ tailWord_237281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237281).length < 2 ^ (prefixWord ++ tailWord_237281).sum := by decide
  have hdescent : baseEnd_237281 < baseStart_237281 := by decide
  rcases family_descends (prefixWord ++ tailWord_237281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237297 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 4, 3, 2]
def baseStart_237297 : Nat := 118140960795 + 237297 * 2 ^ 59
def prefixEnd_237297 : Nat := 4983230072969 + 3 ^ 40 * 237297 * 2
def baseEnd_237297 : Nat := 121847418870063308096197

theorem tailTrace_237297 : CollatzResearch.WordTrace tailWord_237297 prefixEnd_237297 121847418870063308096197 := by
  unfold tailWord_237297
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654932621320970946182145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5769955080880647297454763 8654932621320970946182145)
  ·
    refine ⟨6491199465990728209636609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8654932621320970946182145 6491199465990728209636609)
    ·
      refine ⟨4868399599493046157227457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6491199465990728209636609 4868399599493046157227457)
      ·
        refine ⟨3651299699619784617920593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4868399599493046157227457 3651299699619784617920593)
        ·
          refine ⟨2738474774714838463440445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3651299699619784617920593 2738474774714838463440445)
          ·
            refine ⟨1026928040518064423790167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2738474774714838463440445 1026928040518064423790167)
            ·
              refine ⟨1540392060777096635685251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026928040518064423790167 1540392060777096635685251)
              ·
                refine ⟨2310588091165644953527877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540392060777096635685251 2310588091165644953527877)
                ·
                  refine ⟨433235267093558428786477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2310588091165644953527877 433235267093558428786477)
                  ·
                    refine ⟨162463225160084410794929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 433235267093558428786477 162463225160084410794929)
                    ·
                      refine ⟨121847418870063308096197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162463225160084410794929 121847418870063308096197)
                      ·
                        rfl

theorem cell23_237297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_237297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237297 prefixEnd_237297 := by exact prefixLift 237297
  have htrace : WordTrace (prefixWord ++ tailWord_237297) baseStart_237297 baseEnd_237297 := by
    simpa [prefixWord, tailWord_237297, baseEnd_237297] using wordTrace_append hprefix tailTrace_237297
  have hstable : (prefixWord ++ tailWord_237297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237297).length < 2 ^ (prefixWord ++ tailWord_237297).sum := by decide
  have hdescent : baseEnd_237297 < baseStart_237297 := by decide
  rcases family_descends (prefixWord ++ tailWord_237297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237314 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_237314 : Nat := 118140960795 + 237314 * 2 ^ 59
def prefixEnd_237314 : Nat := 4983230072969 + 3 ^ 40 * 237314 * 2
def baseEnd_237314 : Nat := 121856148041189741583619

theorem tailTrace_237314 : CollatzResearch.WordTrace tailWord_237314 prefixEnd_237314 121856148041189741583619 := by
  unfold tailWord_237314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163888165564845712387749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5770368441506255233033997 2163888165564845712387749)
  ·
    refine ⟨405729031043408571072703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2163888165564845712387749 405729031043408571072703)
    ·
      refine ⟨608593546565112856609055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405729031043408571072703 608593546565112856609055)
      ·
        refine ⟨912890319847669284913583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608593546565112856609055 912890319847669284913583)
        ·
          refine ⟨1369335479771503927370375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912890319847669284913583 1369335479771503927370375)
          ·
            refine ⟨2054003219657255891055563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369335479771503927370375 2054003219657255891055563)
            ·
              refine ⟨3081004829485883836583345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054003219657255891055563 3081004829485883836583345)
              ·
                refine ⟨2310753622114412877437509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081004829485883836583345 2310753622114412877437509)
                ·
                  refine ⟨433266304146452414519533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2310753622114412877437509 433266304146452414519533)
                  ·
                    refine ⟨162474864054919655444825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 433266304146452414519533 162474864054919655444825)
                    ·
                      refine ⟨121856148041189741583619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162474864054919655444825 121856148041189741583619)
                      ·
                        rfl

theorem cell23_237314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_237314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237314 prefixEnd_237314 := by exact prefixLift 237314
  have htrace : WordTrace (prefixWord ++ tailWord_237314) baseStart_237314 baseEnd_237314 := by
    simpa [prefixWord, tailWord_237314, baseEnd_237314] using wordTrace_append hprefix tailTrace_237314
  have hstable : (prefixWord ++ tailWord_237314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237314).length < 2 ^ (prefixWord ++ tailWord_237314).sum := by decide
  have hdescent : baseEnd_237314 < baseStart_237314 := by decide
  rcases family_descends (prefixWord ++ tailWord_237314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237320 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 1, 6]
def baseStart_237320 : Nat := 118140960795 + 237320 * 2 ^ 59
def prefixEnd_237320 : Nat := 4983230072969 + 3 ^ 40 * 237320 * 2
def baseEnd_237320 : Nat := 40619742975038906036197

theorem tailTrace_237320 : CollatzResearch.WordTrace tailWord_237320 prefixEnd_237320 40619742975038906036197 := by
  unfold tailWord_237320
  simp only [CollatzResearch.WordTrace]
  refine ⟨4327885750118822937134707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5770514333491763916179609 4327885750118822937134707)
  ·
    refine ⟨6491828625178234405702061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4327885750118822937134707 6491828625178234405702061)
    ·
      refine ⟨2434435734441837902138273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6491828625178234405702061 2434435734441837902138273)
      ·
        refine ⟨1825826800831378426603705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2434435734441837902138273 1825826800831378426603705)
        ·
          refine ⟨1369370100623533819952779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1825826800831378426603705 1369370100623533819952779)
          ·
            refine ⟨2054055150935300729929169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369370100623533819952779 2054055150935300729929169)
            ·
              refine ⟨1540541363201475547446877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2054055150935300729929169 1540541363201475547446877)
              ·
                refine ⟨577703011200553330292579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1540541363201475547446877 577703011200553330292579)
                ·
                  refine ⟨866554516800829995438869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577703011200553330292579 866554516800829995438869)
                  ·
                    refine ⟨40619742975038906036197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 866554516800829995438869 40619742975038906036197)
                    ·
                      rfl

theorem cell23_237320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_237320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237320 prefixEnd_237320 := by exact prefixLift 237320
  have htrace : WordTrace (prefixWord ++ tailWord_237320) baseStart_237320 baseEnd_237320 := by
    simpa [prefixWord, tailWord_237320, baseEnd_237320] using wordTrace_append hprefix tailTrace_237320
  have hstable : (prefixWord ++ tailWord_237320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237320).length < 2 ^ (prefixWord ++ tailWord_237320).sum := by decide
  have hdescent : baseEnd_237320 < baseStart_237320 := by decide
  rcases family_descends (prefixWord ++ tailWord_237320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237325 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_237325 : Nat := 118140960795 + 237325 * 2 ^ 59
def prefixEnd_237325 : Nat := 4983230072969 + 3 ^ 40 * 237325 * 2
def baseEnd_237325 : Nat := 121861796328389198546069

theorem tailTrace_237325 : CollatzResearch.WordTrace tailWord_237325 prefixEnd_237325 121861796328389198546069 := by
  unfold tailWord_237325
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655953865219531728201429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5770635910146354485467619 8655953865219531728201429)
  ·
    refine ⟨202873918716082774879721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8655953865219531728201429 202873918716082774879721)
    ·
      refine ⟨152155439037062081159791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202873918716082774879721 152155439037062081159791)
      ·
        refine ⟨228233158555593121739687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152155439037062081159791 228233158555593121739687)
        ·
          refine ⟨342349737833389682609531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228233158555593121739687 342349737833389682609531)
          ·
            refine ⟨513524606750084523914297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342349737833389682609531 513524606750084523914297)
            ·
              refine ⟨385143455062563392935723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513524606750084523914297 385143455062563392935723)
              ·
                refine ⟨577715182593845089403585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385143455062563392935723 577715182593845089403585)
                ·
                  refine ⟨433286386945383817052689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577715182593845089403585 433286386945383817052689)
                  ·
                    refine ⟨324964790209037862789517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433286386945383817052689 324964790209037862789517)
                    ·
                      refine ⟨121861796328389198546069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 324964790209037862789517 121861796328389198546069)
                      ·
                        rfl

theorem cell23_237325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_237325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237325 prefixEnd_237325 := by exact prefixLift 237325
  have htrace : WordTrace (prefixWord ++ tailWord_237325) baseStart_237325 baseEnd_237325 := by
    simpa [prefixWord, tailWord_237325, baseEnd_237325] using wordTrace_append hprefix tailTrace_237325
  have hstable : (prefixWord ++ tailWord_237325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237325).length < 2 ^ (prefixWord ++ tailWord_237325).sum := by decide
  have hdescent : baseEnd_237325 < baseStart_237325 := by decide
  rcases family_descends (prefixWord ++ tailWord_237325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237344 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 1, 1, 4]
def baseStart_237344 : Nat := 118140960795 + 237344 * 2 ^ 59
def prefixEnd_237344 : Nat := 4983230072969 + 3 ^ 40 * 237344 * 2
def baseEnd_237344 : Nat := 121871552460824624208481

theorem tailTrace_237344 : CollatzResearch.WordTrace tailWord_237344 prefixEnd_237344 121871552460824624208481 := by
  unfold tailWord_237344
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328323426075348986571543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5771097901433798648762057 4328323426075348986571543)
  ·
    refine ⟨6492485139113023479857315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4328323426075348986571543 6492485139113023479857315)
    ·
      refine ⟨9738727708669535219785973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6492485139113023479857315 9738727708669535219785973)
      ·
        refine ⟨913005722687768926854935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9738727708669535219785973 913005722687768926854935)
        ·
          refine ⟨1369508584031653390282403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913005722687768926854935 1369508584031653390282403)
          ·
            refine ⟨2054262876047480085423605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369508584031653390282403 2054262876047480085423605)
            ·
              refine ⟨192587144629451258008463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2054262876047480085423605 192587144629451258008463)
              ·
                refine ⟨288880716944176887012695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192587144629451258008463 288880716944176887012695)
                ·
                  refine ⟨433321075416265330519043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288880716944176887012695 433321075416265330519043)
                  ·
                    refine ⟨649981613124397995778565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 433321075416265330519043 649981613124397995778565)
                    ·
                      refine ⟨121871552460824624208481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 649981613124397995778565 121871552460824624208481)
                      ·
                        rfl

theorem cell23_237344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_237344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237344 prefixEnd_237344 := by exact prefixLift 237344
  have htrace : WordTrace (prefixWord ++ tailWord_237344) baseStart_237344 baseEnd_237344 := by
    simpa [prefixWord, tailWord_237344, baseEnd_237344] using wordTrace_append hprefix tailTrace_237344
  have hstable : (prefixWord ++ tailWord_237344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237344).length < 2 ^ (prefixWord ++ tailWord_237344).sum := by decide
  have hdescent : baseEnd_237344 < baseStart_237344 := by decide
  rcases family_descends (prefixWord ++ tailWord_237344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237347 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 1, 2, 3]
def baseStart_237347 : Nat := 118140960795 + 237347 * 2 ^ 59
def prefixEnd_237347 : Nat := 4983230072969 + 3 ^ 40 * 237347 * 2
def baseEnd_237347 : Nat := 121873092902788112470967

theorem tailTrace_237347 : CollatzResearch.WordTrace tailWord_237347 prefixEnd_237347 121873092902788112470967 := by
  unfold tailWord_237347
  simp only [CollatzResearch.WordTrace]
  refine ⟨8656756271139829485502295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5771170847426552990334863 8656756271139829485502295)
  ·
    refine ⟨12985134406709744228253443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8656756271139829485502295 12985134406709744228253443)
    ·
      refine ⟨19477701610064616342380165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12985134406709744228253443 19477701610064616342380165)
      ·
        refine ⟨3652069051887115564196281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19477701610064616342380165 3652069051887115564196281)
        ·
          refine ⟨2739051788915336673147211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3652069051887115564196281 2739051788915336673147211)
          ·
            refine ⟨4108577683373005009720817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739051788915336673147211 4108577683373005009720817)
            ·
              refine ⟨3081433262529753757290613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108577683373005009720817 3081433262529753757290613)
              ·
                refine ⟨288884368362164414745995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3081433262529753757290613 288884368362164414745995)
                ·
                  refine ⟨433326552543246622118993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288884368362164414745995 433326552543246622118993)
                  ·
                    refine ⟨324994914407434966589245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433326552543246622118993 324994914407434966589245)
                    ·
                      refine ⟨121873092902788112470967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 324994914407434966589245 121873092902788112470967)
                      ·
                        rfl

theorem cell23_237347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_237347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237347 prefixEnd_237347 := by exact prefixLift 237347
  have htrace : WordTrace (prefixWord ++ tailWord_237347) baseStart_237347 baseEnd_237347 := by
    simpa [prefixWord, tailWord_237347, baseEnd_237347] using wordTrace_append hprefix tailTrace_237347
  have hstable : (prefixWord ++ tailWord_237347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237347).length < 2 ^ (prefixWord ++ tailWord_237347).sum := by decide
  have hdescent : baseEnd_237347 < baseStart_237347 := by decide
  rcases family_descends (prefixWord ++ tailWord_237347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
